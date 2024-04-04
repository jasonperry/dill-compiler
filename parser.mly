%token <Int64.t> ICONST
%token <float> FCONST
%token <string> STRCONST
%token <char> BYTECONST
%token <string> IDENT_LC
%token <string> IDENT_UC
%token <string> IDENT_VARIANT
%token LPAREN RPAREN LBRACE RBRACE LSQRB RSQRB
%token PLUS MINUS TIMES DIV MOD
%token UMINUS (* not lexed *)
%token AMP PIPE CARAT TILDE
%token EQ NE LT GT LE GE
%token AND OR BANG
%token TRUE FALSE NULL VAL
%token COLON DCOLON SEMI DOT COMMA HASH QMARK ARROW DARROW
%token ASSIGN NULLASSIGN
%token VAR REF
%token IS (* BEGIN END *)
%token IF THEN ELSIF ELSE ENDIF
%token WHILE LOOP ENDWHILE
%token CASE OF ENDCASE
%token PROC ENDPROC RETURN NOP
%token MODULE ENDMODULE MODSPEC ENDMODSPEC
%token IMPORT AS OPEN 
%token PRIVATE EXPORT
%token TYPE ENDTYPE OPAQUE REC STRUCT VARIANT MUT
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
%nonassoc BANG

%{
    open Common (* error and location types here now *)
    open Ast
	 (* let mod_name = ref "" (* ONE inherited attribute, okay? *) *)
    open Syntax
%}

%type <locinfo expr> expr
%type <locinfo typeExpr> typeExp
%type <(locinfo, locinfo, locinfo) stmt> stmt
%type <(string * (locinfo typeExpr) option * (locinfo expr) option)> declStmt
%type <(string * locinfo typeExpr)> declOnlyStmt
%type <(string * locinfo typeExpr option * locinfo expr)> declInitStmt
%type <(locinfo, locinfo) procdecl> procHeader
%type <(locinfo, locinfo) procdecl> procDecl
%type <(locinfo, locinfo, locinfo) proc> proc

(* These are removed from the AST after analysis. *)
%type <locinfo fieldDecl> fieldDecl
%type <locinfo variantDecl> variantDecl

(* Thinking of eventually allowing multiple modules/file. *)
%type <(locinfo, locinfo, locinfo) dillmodule> dillmodule
(* Switched to a single module per file until I get object codegen working. *)
%start <(locinfo, locinfo, locinfo) dillmodule> modsource
%start <(locinfo, locinfo, locinfo) module_spec> modspec
%%

(* In the future, may allow multiple modules in a source file/stream *)
modsource: onemod=dillmodule EOF
    { onemod }

dillmodule:
  | MODULE mn=moduleName IS
    mb=moduleBody
    ENDMODULE (* mn2=moduleName *)
    { { mb with name=mn } }
    (*{ if mn = mn2 then
      else (* $syntaxerror *)
	raise (SyntaxError ($loc(mn2), "Module name mismatch"))
	(* raise Parsing.Parse_error (* also deprecated *) *)
    } *)
  | MODULE error
    { raise (SyntaxError ($loc($2), "Not a valid module name")) } 
  | mb=moduleBody (* unnamed top-level module *)
    { mb }

moduleBody: 
  | iss=list(includeStmt)
    tys=list(typedef)    (* TODO: let types come anywhere? Or be strict? *)
    gls=list(declStmt)
    pr=list(proc)
    { {
        name="";
        imports=iss;
        typedefs=tys;
        globals=List.map (
            fun (v, topt, eopt) ->
	      {varname=v; typeexp=topt; init=eopt; decor=$loc}
          ) gls;
        procs=pr;
      }
    }

moduleName:
  | mn=IDENT_LC { mn } (* will this ever need to be anything more? *)

modspec:
  | MODSPEC mn=moduleName IS
    iss=list(includeStmt)  (* TODO: no "open" in modspec *)
    tyds=list(typedecl)
    gls=list(declOnlyStmt) pd=list(procDecl)
    ENDMODSPEC (* mn2=moduleName *)
(* { if mn = mn2 then *)
    { {
	  name=mn;
	  imports=iss;
	  typedefs=tyds;
	  globals= List.map (
		       fun (v, t) -> {varname=v; typeexp=t; decor=$loc}
		     ) gls;
	  procdecls=pd;
    } }
    (*  else
      	raise (SyntaxError ($loc(mn2), "Modspec name mismatch"))
    } *)

includeStmt:
  | is=importStmt
  | is=openStmt
    { {value=is; loc=$loc} }

importStmt:
  | IMPORT mn=moduleName SEMI  { Import (mn, None) }
  | IMPORT mn=moduleName AS alias=moduleName SEMI { Import (mn, Some alias) }

openStmt:
  | OPEN mn=moduleName SEMI { Open mn }
  | OPEN moduleName error
    { raise (SyntaxError (($endpos($2), $endpos($2)), "expected ';'")) }
  | OPEN error
    { raise (SyntaxError ($loc($2), "Invalid module name in import")) }

(* Type declaration in modspec, may or may not have a body *)
typedecl:
  | TYPE tname=IDENT_UC td=typedeclBody
    tps=option(delimited(LPAREN, separated_nonempty_list(COMMA, IDENT_LC), RPAREN))
    { {td with typename=tname;
	       typeparams=(match tps with
			   | Some tps -> tps
			   | None -> [])} }
  | TYPE error
    { raise (SyntaxError ($loc, "Invalid type identifier")) }


typedeclBody:
  | SEMI
    { {typename="";
       kindinfo=Hidden;
       typeparams=[];
       rectype=false;
       opaque=true;
       decor=$loc}
    }
  | IS rt=option(REC) tdi=typedefInfo SEMI
    { {typename="";
       typeparams=[];
       rectype=(
	 match rt with
	 | None -> false
	 | Some _ -> ( match tdi with
		       | Newtype _ ->
			  raise (SyntaxError
				   ($loc(rt), "Newtype can't be marked recursive"))
		       | _ -> true)
	 );
       kindinfo=tdi;
       opaque=false;
       decor=$loc}
    }

(* Type definition in a module, must have a body *)
typedef:
  | op=option(OPAQUE) TYPE tname=IDENT_UC
    tps=option(delimited(LPAREN, separated_nonempty_list(COMMA, IDENT_LC), RPAREN))
    IS
    rt=option(REC) tdi=typedefInfo ENDTYPE
    { {typename=tname;
       rectype=(
	 match rt with
	 | None -> false
	 | Some _ -> ( match tdi with
		       | Newtype _ ->
			  raise (SyntaxError
				   ($loc(rt), "Newtype can't be marked recursive"))
		       | _ -> true)
       );
       typeparams=(match tps with
		   | Some tplist -> tplist
		   | None -> []);
       kindinfo=tdi;
       opaque=Option.is_some(op);
       decor=$loc} }
  | option(OPAQUE) TYPE error
    { raise (SyntaxError ($loc($3), "Invalid type identifier")) }

typedefInfo:
  | STRUCT fl=fieldList SEMI
    { Fields fl }
  | VARIANT vl=variantList SEMI
    { Variants vl }
  | ty=typeExp SEMI
    { Newtype ty }

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
(* | option(PIPE) vl=separated_nonempty_list(PIPE, variantDecl) *)
  | vl=separated_nonempty_list(COMMA, variantDecl)
    { vl }

variantDecl:
  | vname=IDENT_VARIANT vty=option(preceded(COLON, typeExp))
    (* remove the initial pipe character *)
    { {variantName=vname; (* (String.sub vname 1 (String.length vname - 1)); *)
       variantType=vty; decor=$loc} }

proc:
  | pd=procHeader IS sb=stmtSeq ENDPROC (*name2=IDENT_LC *)
    (* code generated by Menhir still can't infer the type of pd. ??? *)
    { { decor=$loc; decl=pd; body=sb } }
    (* { if (pd: (locinfo, locinfo) procdecl).name = name2 then
	{ decor=$loc; decl=pd; body=sb }
      else
	raise (SyntaxError ($loc(name2), "procedure name mismatch"))
    } *)

procHeader:
  | ex = option(EXPORT) PROC tvs=option(tyvarList) pn=IDENT_LC
    LPAREN pl=paramList RPAREN rt=option(preceded(DARROW, typeExp))
    { {decor=$loc;
       name=pn;
       typeparams=(match tvs with
		   | None -> []
		   | Some tvList -> tvList
		  );
       params=pl;
       export=Option.is_some ex;
       rettype = (
	 match rt with
	 | None ->
	    { texpkind=(Concrete {
			    modname = "";
			    classname="Void";
			    typeargs=[] });
	      nullable=false; array=false;
	      loc=$loc }
	 | Some te -> te )
      }
    }

procDecl: ph=procHeader SEMI { ph }

tyvarList:
  | LPAREN tvs=separated_nonempty_list(COMMA, IDENT_LC) RPAREN
    { tvs }

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
  | st=caseStmt
  | st=nopStmt
  | st=returnStmt
  | st=callStmt
  (*  | st=blockStmt *) (* do we need these? *)
    { {decor=$loc; st=st} }

declStmt:
  | ds=declOnlyStmt
    { match ds with
      | (v, t) -> (v, Some t, None) 
    }
  | ds=declInitStmt
    { match ds with 
      | (v, topt, e) -> (v, topt, Some e)
    }

(* These are split out for global decls in the AST. *)
declOnlyStmt:
  | VAR v=IDENT_LC COLON t=typeExp SEMI
    { (v, t) }

declInitStmt:
  | VAR v=IDENT_LC topt=option(preceded(COLON, typeExp)) ASSIGN e=expr SEMI
    { (v, topt, e) }

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

(* blockStmt:
  | BEGIN sb=stmtSeq END
    { StmtBlock sb } *)

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
    ENDWHILE
    { StmtWhile (cond, body) }

caseStmt:
  | CASE matchexp=expr
    caseblocks=list(caseBlock)
    elseopt=option(preceded(ELSE, stmtSeq))
    ENDCASE
    { StmtCase (matchexp, caseblocks, elseopt) }

caseBlock:
  | OF caseexp=expr THEN blk=stmtSeq
    { (caseexp, blk) }

typeExp:
  (* typename plus possibly array, null markers *)
  | mn=moduleName DCOLON tn=IDENT_UC
    tprms=option(delimited(LPAREN, nonempty_list(typeExp), RPAREN))
    qm=option(QMARK) arr=option(pair(LSQRB,RSQRB))
    { { texpkind=(
	  Concrete {
	      modname=mn; classname=tn;
	      typeargs=(match tprms with
			| Some tplist -> tplist
			| None -> []) });
        nullable=Option.is_some qm;
	array=Option.is_some arr;
	loc=$loc } }
  | tn=IDENT_UC
    tprms=option(delimited(LPAREN, nonempty_list(typeExp), RPAREN))
    qm=option(QMARK) arr=option(pair(LSQRB,RSQRB))
    { { texpkind=(
	  Concrete {
	      modname=""; classname=tn;
	      typeargs=(match tprms with
			| Some tplist -> tplist
			| None -> []) });
        nullable=Option.is_some qm;
	array=Option.is_some arr;
	loc=$loc } }
  | tvar=IDENT_LC qm=option(QMARK) arr=option(pair(LSQRB,RSQRB))
    { { texpkind=(Generic tvar);
	nullable=Option.is_some qm;
	array=Option.is_some arr;
	loc=$loc } }
	

expr:
  | LPAREN ex=expr RPAREN
    { ex }
  | ex=constExp
  | ex=valExp
  | ex=recordExp
  | ex=seqExp
  | ex=variantExp
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
  | c=BYTECONST
    { ExpConst (ByteVal c) }
  | TRUE
    { ExpConst (BoolVal true) }
  | FALSE
    { ExpConst (BoolVal false) }
  | s=STRCONST
    { ExpConst (StringVal s) }
  | NULL
    { ExpConst (NullVal) }

valExp: 
  | VAL LPAREN e=expr RPAREN
    { ExpVal (e) }

varExp:
  (* we don't wrap this in the variant ExpVar because it's used in 
   * various places, such as a CallExp *)
  | mn=moduleName DCOLON iv=indexedVar fl=list(preceded(DOT, indexedVar))
    { ((mn ^ "::" ^ (fst iv), snd iv), fl) }
  | iv=indexedVar fl=list(preceded(DOT, indexedVar))
    { (iv, fl) }

indexedVar:
  | v=varName LSQRB e=expr RSQRB 
    { (v, Some e) }
  | v=varName
    { (v, None) }

(* indexOp:
  (* will it conflict with seqExp? *)
  | LSQRB e=expr RSQRB
    { e } *)

varName:
  vn=IDENT_LC { vn }

recordExp:
  | LBRACE fl=separated_list(COMMA, fieldAssign) RBRACE
    { ExpRecord fl }

seqExp:
  | LSQRB vl=separated_nonempty_list(COMMA, expr) RSQRB
    { ExpSeq vl }

variantExp: (* Now using pairs everywhere for type names *)
  | mn=moduleName DCOLON (*tn=IDENT_UC PIPE*) vn=IDENT_VARIANT
        eopt=option(delimited(LPAREN, expr, RPAREN))
    { ExpVariant (mn, vn, eopt) }
  | (* tn=IDENT_UC *) vn=IDENT_VARIANT
        eopt=option(delimited(LPAREN, expr, RPAREN))
    { ExpVariant ("", vn, eopt) }

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
  | BANG e=expr
    { ExpUnop (OpNot, e) }

callExp:
(* Todo: for methods, will be preceded by varExp and dot *)
(* Resolved conflicts by putting procName options here. *)
  | mn=moduleName DCOLON pn=IDENT_LC LPAREN al=argList RPAREN
    { ExpCall (mn ^ "::" ^ pn, al) }
  | pn=IDENT_LC LPAREN al=argList RPAREN
    { ExpCall (pn, al) }

argList:
(* Turn the mutability marker into a boolean *)
  | al=separated_list(COMMA, pair(option(HASH), expr))
    { List.map (fun (eopt, ex) -> match eopt with
				  | Some _ -> (true, ex)
				  | None -> (false, ex)
	       ) al }

nullAssnExp:  (* switching to option reduced S/R conflicts *)
  (* got rid of var decl in null assignment exp for now, to tame the
     type variable proliferation *)
  (* | VAR vn=varName ty=option(preceded(COLON, typeExp)) NULLASSIGN e=expr
    { ExpNullAssn (true, ((vn, None),[]), ty, e) } *)
  | ve=varExp NULLASSIGN e=expr
    { ExpNullAssn (false, ve, e)}
(*  | dec=option(VAR) v=varName NULLASSIGN e=expr
    { ExpNullAssn ( Option.is_some dec, v, e) } *)

(* parameterized rule to add location info to any nonterminal. *)
(* located(X):
  | x=X { { loc = $loc; value = x } } *)
