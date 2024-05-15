%token <Int64.t> I_LIT
%token <float> F_LIT
%token <string> S_LIT
%token <char> B_LIT
%token <string> LC_IDENT
%token <string> UC_IDENT
%token <string> VLABEL
%token LPAREN RPAREN LBRACE RBRACE LSQRB RSQRB
%token PLUS MINUS TIMES DIV MOD
%token UMINUS (* not lexed *)
%token AMP PIPE CARAT TILDE SHL SHR
%token EQ NE LT GT LE GE
%token AND OR BANG
%token TRUE FALSE NULL VAL
%token COLON DCOLON SEMI DOT COMMA HASH QMARK ARROW DARROW DOLLAR
%token ASSIGN NULLASSIGN
%token VAR REF
%token IS BEGIN  (* END *)
%token IF THEN ELSIF ELSE ENDIF
%token WHILE LOOP ENDWHILE
%token CASE OF ENDCASE
%token PROC ENDPROC RETURN NOP
%token MODULE ENDMODULE MODSPEC ENDMODSPEC
%token IMPORT AS OPEN 
%token PRIVATE (* EXPORT *)
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
%start <(locinfo, locinfo, locinfo) dillmodule list> modsource
%start <(locinfo, locinfo, locinfo) module_spec> modspec
%%

(* In the future, may allow multiple modules in a source file/stream *)
modsource: mods=list(dillmodule) tl=option(moduleBody) EOF
    { match tl with
      | Some tl -> mods @ [tl]
      | None -> mods }

dillmodule:
  | MODULE mn=moduleName BEGIN
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
(*  | mb=moduleBody (* unnamed top-level module *)
    { mb } *)

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
  | mn=LC_IDENT { mn } (* will this ever need to be anything more? *)

modspec:
  | MODSPEC mn=moduleName BEGIN
    iss=list(includeStmt)  (* TODO: no "open" in modspec *)
    tyds=list(typedecl)
    gls=list(declOnlyStmt)
    pd=list(procDecl)
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
  | TYPE tname=UC_IDENT td=typedeclBody
    tps=option(delimited(LPAREN, separated_nonempty_list(COMMA, LC_IDENT), RPAREN))
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
       visibility=Opaque;
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
       visibility=Open;  (* not relevant for newtypes? *)
       decor=$loc}
    }

(* Type definition in a module, must have a body *)
typedef:
  | op=option(typevis) TYPE tname=UC_IDENT
    tps=option(delimited(LPAREN, separated_nonempty_list(COMMA, LC_IDENT), RPAREN))
    IS
    rt=option(REC) tdi=typedefInfo (* ENDTYPE *)
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
       visibility=(match op with
		   | Some vis -> vis
		   | None -> Open) ;
       decor=$loc} }
  | option(typevis) TYPE error
    { raise (SyntaxError ($loc($3), "Invalid type identifier")) }

typevis:
  | OPAQUE { Opaque }
  | PRIVATE { Private }

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
  | priv=option(PRIVATE) mut=option(MUT) fn=LC_IDENT COLON fty=typeExp
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
  | vname=VLABEL vty=option(preceded(COLON, typeExp))
    (* remove the initial pipe character *)
    { {variantName=vname; (* (String.sub vname 1 (String.length vname - 1)); *)
       variantType=vty; decor=$loc} }

proc:
  | pd=procHeader BEGIN sb=stmtSeq ENDPROC (*name2=LC_IDENT *)
    (* code generated by Menhir still can't infer the type of pd. ??? *)
    { { decor=$loc; decl=pd; body=sb } }
    (* { if (pd: (locinfo, locinfo) procdecl).name = name2 then
	{ decor=$loc; decl=pd; body=sb }
      else
	raise (SyntaxError ($loc(name2), "procedure name mismatch"))
    } *)

procHeader:
  | vis=option(visibility) PROC tvs=option(tyvarList) pn=LC_IDENT
    LPAREN pl=paramList RPAREN rt=option(preceded(ARROW, typeExp))
    { {decor=$loc;
       name=pn;
       typeparams=(match tvs with
		   | None -> []
		   | Some tvList -> tvList
		  );
       params=pl;
       visibility=( match vis with | Some v -> v | None -> Public );
       rettype=(
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
  | LPAREN tvs=separated_nonempty_list(COMMA, LC_IDENT) RPAREN
    { tvs }

paramList:
  | pl=separated_list(COMMA, paramInfo)
    { pl }

paramInfo:
  (* should this be varexp or should I have a different 'varname' rule? 
   * I believe it's just a name, you can't have dots in a parameter. *)
  | DOLLAR v=varName COLON t=typeExp
    { true, v, t }
  | v=varName COLON t=typeExp
    { false, v, t } (* (string * typeExpr) for procdecl.params *)

visibility:
  (* | EXPORT { Export } *)
  | PRIVATE { Private : visibility }

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
  | VAR v=LC_IDENT COLON t=typeExp SEMI
    { (v, t) }

declInitStmt:
  | VAR v=LC_IDENT topt=option(preceded(COLON, typeExp)) ASSIGN e=expr SEMI
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
  (* typename or type variable plus possibly array, null markers *)
  | mn=moduleName DCOLON tn=UC_IDENT
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
  | tn=UC_IDENT
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
  | tvar=LC_IDENT qm=option(QMARK) arr=option(pair(LSQRB,RSQRB))
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
  | i=I_LIT
    { ExpLiteral (IntVal i) }
  | f=F_LIT
    { ExpLiteral (FloatVal f) }
  | c=B_LIT
    { ExpLiteral (ByteVal c) }
  | TRUE
    { ExpLiteral (BoolVal true) }
  | FALSE
    { ExpLiteral (BoolVal false) }
  | s=S_LIT
    { ExpLiteral (StringVal s) }
  | NULL
    { ExpLiteral (NullVal) }

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
  | v=varName ixs=list(delimited(LSQRB, expr, RSQRB))
    { (v, ixs) }

(* indexOp:
  (* will it conflict with seqExp? *)
  | LSQRB e=expr RSQRB
    { e } *)

varName:
  vn=LC_IDENT { vn }

recordExp:
  | LBRACE fl=separated_list(COMMA, fieldAssign) RBRACE
    { ExpRecord fl }

seqExp:
  | LSQRB vl=separated_nonempty_list(COMMA, expr) RSQRB
    { ExpSeq vl }

variantExp:
  | vl=VLABEL
    etup=option(delimited(LPAREN,
                          separated_nonempty_list(COMMA, expr), RPAREN))
    { match etup with
      | Some etup -> ExpVariant (vl, etup)
      | None -> ExpVariant (vl, []) }

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
  | e1=expr SHL e2=expr
    { ExpBinop (e1, OpShl, e2) }
  | e1=expr SHR e2=expr
    { ExpBinop (e1, OpShr, e2) }
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
  | mn=moduleName DCOLON pn=LC_IDENT LPAREN al=argList RPAREN
    { ExpCall (mn ^ "::" ^ pn, al) }
  | pn=LC_IDENT LPAREN al=argList RPAREN
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
