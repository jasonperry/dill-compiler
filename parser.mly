%token <int> ICONST  (* TODO: change to int32 *)
%token <float> FCONST
%token <string> IDENT_LC
%token <string> IDENT_UC
%token LPAREN RPAREN
%token PLUS MINUS TIMES DIV MOD
%token UMINUS (* not lexed *)
%token BITAND BITOR BITXOR BITNOT
%token EQ NE LT GT LE GE
%token AND OR NOT
%token TRUE FALSE
%token ASSIGN COLON SEMI COMMA
%token VAR
%token BEGIN END
%token NULLASSIGN
%token IF THEN ELSIF ELSE ENDIF
%token WHILE LOOP ENDLOOP
%token PROC RETURN NOP
%token MODULE MODSPEC
%token USING AS OPEN
%token PRIVATE DOT TYPE STRUCT
%token EOF

(* ordering of these indicates precedence, low to high *)
%left OR
%left AND
%left EQ NE LT LE GE
%left BITAND BITOR BITXOR
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc UMINUS
%nonassoc BITNOT
%nonassoc NOT

%{
    open Ast
    (* let mod_name = ref "" (* ONE inherited attribute, okay? *) *)
%}

%type <Ast.locinfo Ast.expr> expr
%type <(Ast.locinfo, Ast.locinfo) Ast.stmt> stmt
%type <Ast.locinfo Ast.procdecl> procHeader
%type <(Ast.locinfo, Ast.locinfo) Ast.proc> proc
(* Thinking of eventually allowing multiple modules/file. *)
%type <(Ast.locinfo, Ast.locinfo) Ast.dillmodule> dillmodule
%type <(Ast.locinfo) Ast.module_spec> modspec
(* Switched back to a single module per file until I get object codegen working. *)
%start <(Ast.locinfo) Ast.module_spec option
        * (Ast.locinfo,Ast.locinfo) Ast.dillmodule option> main

%%

main: specopt=option(modspec) modopt=option(dillmodule) EOF
    { (specopt, modopt) }

(* My brilliant idea, but it never reduces. TODO: allow interspersing. *)
(* main: ml=list(pair (option(modspec), option(dillmodule))) EOF
    { (List.concat_map (fun (specopt, _) -> Option.to_list specopt) ml,
       List.concat_map (fun (_, modopt) -> Option.to_list modopt) ml)
    }
*)

dillmodule:
  | MODULE mn=moduleName ASSIGN
    iss=list(importStmt)
    tys=list(typedef)    (* TODO: let types come anywhere? Or be strict? *)
    gls=list(declStmt)
    pr=list(proc)
    bl=option(blockStmt)
    END mn2=moduleName
    { let initstmts = match bl with
	| Some (StmtBlock slist) -> slist
	| _ -> [] in
      if mn = mn2 then {
	  name=mn;
	  imports=iss;
	  typedefs=tys;
	  globals=List.map (
		      fun (v, topt, eopt) ->
		      {varname=v;
		       typeexp=topt; init=eopt; decor=$loc}
		    ) gls;
	  procs=pr;
	  initblock=initstmts
	}
      else $syntaxerror
    }

moduleName: mn=IDENT_UC { mn }

modspec:
  | MODSPEC mn=moduleName ASSIGN
    iss=list(usingStmt)
    gls=list(declOnlyStmt) pd=list(procDecl)
    END mn2=moduleName
    { if mn = mn2 then {
	  name=mn;
	  imports=iss;
	  typedefs=[];
	  globals= List.map (
		       fun (v, t) -> {varname=v; 
				      typeexp=t; decor=$loc}
		     ) gls;
	  procdecls=pd;
	}
      else $syntaxerror
    }

importStmt:
  | is=usingStmt
  | is=openStmt
    { is }

usingStmt:
  | USING mn=moduleName SEMI  { Using (mn, None) }
  | USING mn=moduleName AS alias=moduleName SEMI { Using (mn, Some alias) }

openStmt: OPEN mn=moduleName SEMI { Open mn }

typedef:
  | sd=structTypedef { Struct sd }

structTypedef:
  | TYPE tn=IDENT_UC ASSIGN STRUCT fl=fieldList SEMI END tn2=IDENT_UC
    { if tn2 = tn then
	{typename=tn; fields=fl}
      else
	$syntaxerror
    }

fieldList:
  | fl=separated_list(COMMA, fieldDecl) { fl }

fieldDecl:
  | vn=IDENT_LC COLON te=IDENT_UC (* not varName, can't have dots *)
    { (vn, TypeName te) }

proc:
  | pd=procHeader ASSIGN sb=stmtSeq END en=procName 
    { if pd.name = en then
	{ decor=$loc; decl=pd; body=sb }
      else  (* TODO: try "new way" error handling (Menhir Ch. 11)
             * (or wait for a hand-rolled parser? *)
	$syntaxerror
    }

procHeader:
  | PROC pn=IDENT_LC LPAREN pl=paramList RPAREN COLON rt=typeExp
    { {decor=$loc; name=pn; params=pl; rettype=rt} (* procdecl *) }

procDecl: ph=procHeader SEMI { ph }

procName:
  (* TODO: A method needs a dot or an arrow. *)
  | mn=option(terminated(moduleName, DOT)) pn=IDENT_LC
    { match mn with
      | Some mname -> mname ^ "." ^ pn
      | None -> pn
    }

paramList:
  | pl=separated_list(COMMA, nameAndType)
    { pl }

nameAndType:
  (* should this be varexp or should I have a different 'varname' rule? 
   * I think later I will have objExp and then I'll need it. 
   * It's definitely not an expression. *)
  | v=varName COLON t=typeExp
    { v, t }

stmtSeq:
  | sl = list(stmt)
    { sl }

stmt:
  | ds=declStmt
    { {decor=$loc;
       st=match ds with (v, topt, eopt) -> StmtDecl (v, topt, eopt); }
    }			       
  | st=assignStmt
  | st=ifStmt
  | st=whileStmt
  | st=nopStmt
  | st=returnStmt
  | st=callStmt
  | st=blockStmt
    { {decor=$loc; st=st} }

declStmt:
  | ds=declOnlyStmt
    { match ds with
      | (v, t) -> (v, Some t, None)
    }
  | ds=declInitStmt
    { match ds with 
      | (v, topt, eopt) -> (v, topt, eopt)
    }

(* These are split out for global decls in the AST. *)
declOnlyStmt:
  | VAR v=IDENT_LC COLON t=typeExp SEMI
    { (v, t) }

declInitStmt:
  | VAR v=IDENT_LC t=option(preceded(COLON, typeExp)) ASSIGN e=expr SEMI
    { (v, t, Some e) }

assignStmt:
  | v=varName ASSIGN e=expr SEMI
    { StmtAssign (v, e) }

nopStmt:
  | NOP SEMI
    { StmtNop }

returnStmt:
  | RETURN eopt=option(expr) SEMI
    { StmtReturn eopt }

callStmt:
  | e=expr SEMI
    { StmtCall e }

blockStmt:
  | BEGIN sb=stmtSeq END
    { StmtBlock sb }

ifStmt:
  | IF LPAREN e=expr RPAREN THEN
    tb=stmtSeq
    eifs=list(elsifBlock)
    eb=option(preceded(ELSE, stmtSeq))
    ENDIF
    { StmtIf (e, tb, eifs, eb) }

elsifBlock:
  | ELSIF LPAREN e=expr RPAREN THEN body=stmtSeq
    { (e, body) }

whileStmt:
  | WHILE LPAREN cond=expr RPAREN LOOP
    body=stmtSeq
    ENDLOOP
    { StmtWhile (cond, body) }

typeExp:
  (* This will be elaborated to include array, null, type variables,... *)
  | tn=IDENT_UC
    { TypeName tn }

(* Expressions are what evaluates to a value. *)
expr:
  | LPAREN ex=expr RPAREN
    { ex }
  | ex=constExp
  | ex=varExp
  | ex=opExp
  | ex=callExp
  | ex=nullAssnExp
    { {decor=$loc; e=ex} }

(* objexp to replace varexp *)

constExp:
  | i = ICONST
    { ExpConst (IntVal i) }
  | f = FCONST
    { ExpConst (FloatVal f) }
  | TRUE
    { ExpConst (BoolVal true) }
  | FALSE
    { ExpConst (BoolVal false) }
(* | STRCONST | *)

varExp:
  (* later, objExp will have other productions *)
  | v = varName
    { ExpVar v }

varName:
  (* later, to add type or object prefix *)
  | mn=option(terminated(moduleName, DOT)) vn=IDENT_LC
    { match mn with
      | Some mname -> mname ^ "." ^ vn
      | None -> vn
    }

opExp:
(* TODO: check type of subexps and apply promotion rules *)
(* Nope! Do everything with the AST. *)
(*  | e1=expr op=binOp e2=expr
    { ExpBinop (e1, op, e2) } *)
  | e1=expr TIMES e2=expr
    { ExpBinop (e1, OpTimes, e2) }
  | e1=expr DIV e2=expr
    { ExpBinop (e1, OpDiv, e2) } 
  | e1=expr MOD e2=expr
    { ExpBinop (e1, OpMod, e2) } 
  | e1=expr PLUS e2=expr
    { ExpBinop (e1, OpPlus, e2) }
  | e1=expr MINUS e2=expr
    { ExpBinop (e1, OpMinus, e2) }
  | e1=expr BITAND e2=expr
    { ExpBinop (e1, OpBitAnd, e2) }
  | e1=expr BITOR e2=expr
    { ExpBinop (e1, OpBitOr, e2) }
  | e1=expr BITXOR e2=expr
    { ExpBinop (e1, OpBitXor, e2) }
  | e1=expr EQ e2=expr
    { ExpBinop (e1, OpEq, e2) }
  | e1=expr NE e2=expr
    { ExpBinop (e1, OpNe, e2) }
  | e1=expr LT e2=expr
    { ExpBinop (e1, OpLt, e2) }
  | e1=expr GT e2=expr
    { ExpBinop (e1, OpGt, e2) }
  | e1=expr LE e2=expr
    { ExpBinop (e1, OpLe, e2) }
  | e1=expr GE e2=expr
    { ExpBinop (e1, OpGe, e2) }
  | e1=expr AND e2=expr
    { ExpBinop (e1, OpAnd, e2) }
  | e1=expr OR e2=expr
    { ExpBinop (e1, OpOr, e2) }
  | MINUS e=expr %prec UMINUS  (* apply unary minus precedence *)
    { ExpUnop (OpNeg, e) }
  | BITNOT e=expr
    { ExpUnop (OpBitNot, e) }
  | NOT e=expr
    { ExpUnop (OpNot, e) }

callExp:
  | pn=procName LPAREN al=argList RPAREN
    { ExpCall (pn, al) }

argList:
  | al=separated_list(COMMA, expr)
    { al }

nullAssnExp:  (* This needs lookahead, will it work? *)
  | VAR v=varName COLON ty=typeExp NULLASSIGN e=expr
    { ExpNullAssn (true, v, Some ty, e) }
  | VAR v=varName NULLASSIGN e=expr
    { ExpNullAssn (true, v, None, e) }
  | v=varName NULLASSIGN e=expr
    { ExpNullAssn (false, v, None, e) }
(*  | dec=option(VAR) v=varName NULLASSIGN e=expr
    { ExpNullAssn ( Option.is_some dec, v, e) } *)

(* parameterized rule to add location info to any nonterminal. *)
(* located(X):
  | x=X { { loc = $loc; value = x } } *)
