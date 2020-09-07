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
%token EOF

(* ordering of these indicates precedence, low to high *)
%left OR
%left AND
%left EQ NE LT LE GE
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS
%nonassoc BITNOT
%nonassoc NOT

%{
    open Ast
%}

%type <Ast.locinfo Ast.expr> expr
%type <(Ast.locinfo, Ast.locinfo) Ast.stmt> stmt
%type <Ast.locinfo Ast.procdecl> procHeader
%type <(Ast.locinfo, Ast.locinfo) Ast.proc> proc
(* Thinking of eventually allowing multiple modules/file. *)
%start <(Ast.locinfo, Ast.locinfo) Ast.dillmodule> main
(* %start <(Ast.locinfo, Ast.locinfo) Ast.proc list
        * (Ast.locinfo,Ast.locinfo) Ast.stmt list> main *)

%%

main:  (* TODO: let the init block come before or after. And imports. *)
  | gl=list(declStmt) pr=list(proc) bl=option(blockStmt) EOF
    { let initstmts = match bl with
	| Some (StmtBlock slist) -> slist
	| _ -> [] in
      {name="YourModuleNameHere";
       globals=gl;
       procs=pr;
       initblock=initstmts} }

proc:
  | pd=procHeader ASSIGN sb=stmtSeq END en=procName 
    { if pd.name = en then
	{ decor=$loc; decl=pd; body=sb }
      else  (* TODO: try "new way" error handling (Menhir Ch. 11)
             * (or wait for a hand-rolled parser? *)
	$syntaxerror
    }

procHeader:
  | PROC pn=procName LPAREN pl=paramList RPAREN COLON rt=typeExp
    (* construct declaration object! Good idea! *)
    { { decor=$loc; name=pn; params=pl; rettype=rt } }

procName:
  (* TODO: A method needs a dot or an arrow. *)
  | pn=IDENT_LC { pn }

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
  | ds=declStmt  (* gets its decor early b/c used in other contexts. *)
    { ds }
  | st=assignStmt
  | st=ifStmt
  | st=whileStmt
  | st=nopStmt
  | st=returnStmt
  | st=callStmt
  | st=blockStmt
    { {decor=$loc; st=st} }

declStmt:
  | VAR v=varName t=option(preceded(COLON, typeExp)) ASSIGN e=expr SEMI
    { {decor=$loc; st=StmtDecl (v, t, Some e)} }
  | VAR v=varName t=option(preceded(COLON, typeExp)) SEMI
    { {decor=$loc; st=StmtDecl (v, t, None)} }

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
  (* later, to add the dot in it *)
  | vn = IDENT_LC
    { vn }

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
  | MINUS e=expr %prec UMINUS
    { ExpUnop (OpNeg, e) } (* need to learn what this trick does *)
  | BITNOT e=expr
    { ExpUnop (OpBitNot, e) }
  | NOT e=expr
    { ExpUnop (OpNot, e) }

(* binOp: 
  | TIMES { OpTimes }
  | DIV { OpDiv }
  | PLUS { OpPlus }
  | MINUS { OpMinus }
  | BITAND { OpBitAnd }
  | BITOR { OpBitOr }
  | BITXOR { OpBitXor }
  | EQ { OpEq }
  | NE { OpNe }
  | LT { OpLt }
  | GT { OpGt }
  | LE { OpLe }
  | GE { OpGe }
  | AND { OpAnd }
  | OR { OpOr } *)
	
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
