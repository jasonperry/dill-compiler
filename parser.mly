%token <int> ICONST  (* TODO: make it full 32-bit *)
%token <float> FCONST
%token <string> IDENT_LC
%token <string> IDENT_UC
%token LPAREN RPAREN
%token ASSIGN COLON SEMI COMMA
%token NULLASSIGN
(* %token EQUAL COMMA DOT ARROW 
%token STAR AMP *)
%token VAR
%token BEGIN END
%token IF THEN ELSIF ELSE ENDIF
%token UMINUS PLUS MINUS TIMES DIV
%token PROC RETURN
%token EOF

(* ordering of these indicates precedence, low to high *)
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS

%{
    open Ast
%}

%type <Ast.expr> expr
%type <Ast.stmt> stmt
%type <Ast.proc> proc
%start <Ast.proc list * Ast.stmt list> main

%%

main:
  | procs=list(proc) block=nonempty_list(stmt) EOF
    { (procs, block) }

proc:
  | pd=procHeader ASSIGN sb=stmtSeq END en=procName 
    { if pd.value.name = en then
	{ loc = $loc; value = {decl=pd; body=sb} }
      else  (* TODO: try "new way" error handling (Menhir Ch. 11) *)
	$syntaxerror
    }

procHeader:
  | PROC pn=procName LPAREN pl=paramList RPAREN COLON rt=typeExp
    (* construct declaration object! Good idea! *)
    { { loc = $loc; value = { name=pn; params=pl; rettype=rt } } }

procName:
  (* A method needs a dot...should I have different syntax? *)
  | pn=IDENT_UC { pn }

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
  | st=declStmt
  | st=assignStmt
  | st=ifStmt
  | st=returnStmt
  | st=callStmt
  | st=blockStmt
    { { loc = $loc; value = st } }

declStmt:
  | VAR v=varName t=option(preceded(COLON, typeExp)) ASSIGN e = expr SEMI
    { StmtDecl (v, t, e) }

assignStmt:
  | v=varName ASSIGN e=expr SEMI
    { StmtAssign (v, e) }

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

typeExp:
  (* This will be elaborated to include array, list, type variables,... *)
  | tn=IDENT_LC
    { TypeName tn }

(* Expressions are what evaluates to a value. *)
expr:
  | LPAREN ex=expr RPAREN
    { ex }
  (* will this not work at all with old syntax? *)
  (* | el=located(constExp | varExp | opExp | callExp)
    { el } *)
  | ex=constExp
  | ex=varExp
  | ex=opExp
  | ex=callExp
  | ex=nullAssnExp
    { { loc=$loc; value={ ty=None; e=ex } } }

(* objexp to replace varexp *)

constExp:
  | i = ICONST
    { ExpConst (IntVal i) }
  | f = FCONST
    { ExpConst (FloatVal f) }
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
  | e1=expr PLUS e2=expr
    { ExpBinop (e1, OpPlus, e2) }
  | e1=expr MINUS e2=expr
    { ExpBinop (e1, OpMinus, e2) }
  | e1=expr TIMES e2=expr
    { ExpBinop (e1, OpTimes, e2) }
  | e1=expr DIV e2=expr
    { ExpBinop (e1, OpDiv, e2) }
  | MINUS e=expr %prec UMINUS
    { ExpUnop (OpNeg, e) } (* need to learn what this trick does *)

callExp:
  | pn=procName LPAREN al=argList RPAREN
    { ExpCall (pn, al) }

argList:
  | al=separated_list(COMMA, expr)
    { al }

nullAssnExp:
  | dec=option(VAR) v=varname NULLASSIGN e=expr
    { ExpNullAssn ( Option.is_some dec, v, e) }

(* parameterized rule to add location info to any nonterminal. *)
located(X):
  | x=X { { loc = $loc; value = x } }
