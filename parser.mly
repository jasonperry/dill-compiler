%token <int> ICONST  (* TODO: change to int32 *)
%token <float> FCONST
%token <string> STRCONST
%token <string> IDENT_LC
%token <string> IDENT_UC
%token LPAREN RPAREN LBRACE RBRACE
%token PLUS MINUS TIMES DIV MOD
%token UMINUS (* not lexed *)
%token AMP PIPE CARAT TILDE
%token EQ NE LT GT LE GE
%token AND OR NOT
%token TRUE FALSE NULL
%token COLON DCOLON SEMI DOT COMMA HASH QMARK
%token ASSIGN NULLASSIGN
%token VAR
%token BEGIN END
%token IF THEN ELSIF ELSE ENDIF
%token WHILE LOOP ENDLOOP
%token PROC RETURN NOP
%token MODULE MODSPEC
%token IMPORT AS OPEN 
%token PRIVATE EXPORT
%token TYPE STRUCT VARIANT MUT
%token EOF

(* ordering of these indicates precedence, low to high *)
%left OR
%left AND
%left EQ NE LT LE GE
%left AMP PIPE CARAT  (* Only makes a difference in exprs, right? *)
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc UMINUS
%nonassoc TILDE
%nonassoc NOT

%{
    open Ast
    (* let mod_name = ref "" (* ONE inherited attribute, okay? *) *)
%}

%type <Ast.locinfo Ast.expr> expr
%type <(Ast.locinfo, Ast.locinfo) Ast.stmt> stmt
%type <Ast.locinfo Ast.procdecl> procHeader
%type <(Ast.locinfo, Ast.locinfo) Ast.proc> proc
%type <Ast.locinfo Ast.variantDecl> variantDecl
(* Thinking of eventually allowing multiple modules/file. *)
%type <(Ast.locinfo, Ast.locinfo) Ast.dillmodule> dillmodule
%type <(Ast.locinfo) Ast.module_spec> modspec
(* Switched to a single module per file until I get object codegen working. *)
%start <(Ast.locinfo) Ast.module_spec option
        * (Ast.locinfo,Ast.locinfo) Ast.dillmodule option> main

%%

(* Why the heck did I make it consist of a modspec *and* a module instead
 * of one or (a list of) the other? *)
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
    iss=list(includeStmt)
    tys=list(typedef)    (* TODO: let types come anywhere? Or be strict? *)
    gls=list(declStmt)
    pr=list(proc)
    (* bl=option(blockStmt) *)
    END mn2=moduleName
    (* { let initstmts = match bl with
	| Some (StmtBlock slist) -> slist
	| _ -> [] in *)
    { if mn = mn2 then {
        name=mn;
        imports=iss;
        typedefs=tys;
        globals=List.map (
            fun (v, topt, eopt) ->
	      {varname=v;
	       typeexp=topt; init=eopt; decor=$loc}
          ) gls;
        procs=pr;
        (* initblock=initstmts *)
        }
        else $syntaxerror
    }

moduleName: mn=IDENT_UC { mn }

modspec:
  | MODSPEC mn=moduleName ASSIGN
    iss=list(includeStmt)
    tys=list(typedef)
    gls=list(declOnlyStmt) pd=list(procDecl)
    END mn2=moduleName
    { if mn = mn2 then {
	  name=mn;
	  imports=iss;
	  typedefs=tys;
	  globals= List.map (
		       fun (v, t) -> {varname=v; 
				      typeexp=t; decor=$loc}
		     ) gls;
	  procdecls=pd;
	}
      else $syntaxerror
    }

includeStmt:
  | is=importStmt
  | is=openStmt
    { is }

importStmt:
  | IMPORT mn=moduleName SEMI  { Using (mn, None) }
  | IMPORT mn=moduleName AS alias=moduleName SEMI { Using (mn, Some alias) }

openStmt: OPEN mn=moduleName SEMI { Open mn }

typedef:
  | TYPE tname=IDENT_UC ASSIGN tdi=typedefInfo END tname2=IDENT_UC
    { if tname2 = tname then
	{typename=tname; subinfo=tdi; decor=$loc}
      else
	$syntaxerror
    }

typedefInfo:
  | STRUCT fl=fieldList SEMI
    { Fields fl }
  | VARIANT vl=variantList SEMI
    { Variants vl }

fieldList:
  | fl=separated_nonempty_list(COMMA, fieldDecl)
    { fl }

fieldDecl:
  | priv=option(PRIVATE) mut=option(MUT) fn=IDENT_LC COLON fty=typeExp
    { {fieldname=fn;
       priv=Option.is_some priv;
       mut=Option.is_some mut;
       fieldtype=fty;
       decor=$loc
    } }

variantList:
  | option(PIPE) vl=separated_nonempty_list(PIPE, variantDecl)
    { vl }

variantDecl:
  | vname=IDENT_LC COLON vty=typeExp
    { {variantName=vname; variantType=vty; decor=$loc} }

proc:
  | pd=procHeader ASSIGN sb=stmtSeq END en=IDENT_LC 
    { if pd.name = en then
	{ decor=$loc; decl=pd; body=sb }
      else  (* TODO: try "new way" error handling (Menhir Ch. 11)
             * (or wait for a hand-rolled parser? *)
	$syntaxerror
    }

procHeader:
  | ex = option(EXPORT) PROC pn=IDENT_LC
    LPAREN pl=paramList RPAREN COLON rt=typeExp
    { {decor=$loc;
       name=pn;
       params=pl;
       export=Option.is_some ex;
       rettype=rt} (* procdecl *) }

procDecl: ph=procHeader SEMI { ph }

paramList:
  | pl=separated_list(COMMA, paramInfo)
    { pl }

paramInfo:
  (* should this be varexp or should I have a different 'varname' rule? 
   * I believe it's just a name, you can't have dots in a parameter. *)
  | HASH v=varName COLON t=typeExp
    { true, v, t }
  | v=varName COLON t=typeExp
    { false, v, t } (* (string * typeExpr) for procdecl.params *)

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
  | ve=varExp ASSIGN e=expr SEMI
    { StmtAssign (ve, e) }
(*    { match ve with
      | ExpVar (v, fl) -> StmtAssign ((v, fl), e)
      | _ -> $syntaxerror (* not possible. Maybe change expr *)
    } *)

nopStmt:
  | NOP SEMI
    { StmtNop }

returnStmt:
  | RETURN eopt=option(expr) SEMI
    { StmtReturn eopt }

callStmt:
(* Now specifies the subtype of expressions *)
  | ce = callExp SEMI
    { StmtCall {decor=$loc; e=ce} }

blockStmt:
  | BEGIN sb=stmtSeq END
    { StmtBlock sb }

ifStmt:
  | IF e=expr THEN
    tb=stmtSeq
    eifs=list(elsifBlock)
    eb=option(preceded(ELSE, stmtSeq))
    ENDIF
    { StmtIf (e, tb, eifs, eb) }

elsifBlock:
  | ELSIF e=expr THEN body=stmtSeq
    { (e, body) }

whileStmt:
  | WHILE cond=expr LOOP
    body=stmtSeq
    ENDLOOP
    { StmtWhile (cond, body) }

typeExp:
  (* typename plus possibly array, null markers *)
  | mn=moduleName DCOLON tn=IDENT_UC qm=option(QMARK)
    { { modname=Some mn; classname=tn;
        nullable=Option.is_some qm } }
  | tn=IDENT_UC qm=option(QMARK)
    { { modname=None; classname=tn;
        nullable=Option.is_some qm } }

(* Expressions are what evaluates to a value. *)
expr:
  | LPAREN ex=expr RPAREN
    { ex }
  | ex=constExp
  | ex=recordExp
  | ex=opExp
  | ex=callExp
  | ex=nullAssnExp
    { {decor=$loc; e=ex} }
  | ve=varExp
    { {decor=$loc; e=ExpVar ve} }

(* objexp to replace varexp *)

constExp:
  | i=ICONST
    { ExpConst (IntVal i) }
  | f=FCONST
    { ExpConst (FloatVal f) }
  | TRUE
    { ExpConst (BoolVal true) }
  | FALSE
    { ExpConst (BoolVal false) }
  | s=STRCONST
    { ExpConst (StringVal s) }
  | NULL
    { ExpConst (NullVal) }
(* | STRCONST | *)

varExp:
  (* a method call could be preceded by this. *)
  | v=varName fl=list(preceded(DOT, varName))
    { (v, fl) }
    (* { ExpVar (v, fl) } *)

varName:
  vn=IDENT_LC { vn }

recordExp:
  | LBRACE fl=separated_list(COMMA, fieldAssign) RBRACE
    { ExpRecord fl }

fieldAssign:
  | vn=varName ASSIGN e=expr
    { (vn, e) }

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
  | e1=expr AMP e2=expr
    { ExpBinop (e1, OpBitAnd, e2) }
  | e1=expr PIPE e2=expr
    { ExpBinop (e1, OpBitOr, e2) }
  | e1=expr CARAT e2=expr
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
  | TILDE e=expr
    { ExpUnop (OpBitNot, e) }
  | NOT e=expr
    { ExpUnop (OpNot, e) }

callExp:
(* Todo: for methods, will be preceded by varExp and dot *)
(* Resolved conflicts by putting procName options here. *)
  | mn=moduleName DCOLON pn=IDENT_LC LPAREN al=argList RPAREN
    { ExpCall (mn ^ "." ^ pn, al) }
  | pn=IDENT_LC LPAREN al=argList RPAREN
    { ExpCall (pn, al) }

argList:
(* Turn the mutability marker into a boolean *)
  | al=separated_list(COMMA, pair(option(HASH), expr))
    { List.map (fun (eopt, ex) -> match eopt with
				  | Some _ -> (true, ex)
				  | None -> (false, ex)
	       ) al }

nullAssnExp:  (* This needs lookahead, will it work? *)
  | VAR v=varName COLON ty=typeExp NULLASSIGN e=expr
    { ExpNullAssn (true, (v,[]), Some ty, e) }
  | VAR v=varName NULLASSIGN e=expr
    { ExpNullAssn (true, (v,[]), None, e) }
  | ve=varExp NULLASSIGN e=expr
    { ExpNullAssn (false, ve, None, e) }
(*  | dec=option(VAR) v=varName NULLASSIGN e=expr
    { ExpNullAssn ( Option.is_some dec, v, e) } *)

(* parameterized rule to add location info to any nonterminal. *)
(* located(X):
  | x=X { { loc = $loc; value = x } } *)
