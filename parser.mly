%token <int> ICONST  (* TODO: make it full 32-bit *)
%token <float> FCONST
%token <string> IDENT_LC
%token <string> IDENT_UC
%token LPAREN RPAREN
%token ASSIGN COLON SEMI
(* %token EQUAL COMMA DOT ARROW 
%token STAR AMP *)
%token VAR
%token IF THEN ELSIF ELSE END
%token UMINUS PLUS MINUS TIMES DIV
%token EOF

(* ordering of these indicates precedence, low to high *)
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS

%{
    open Ast
%}

%type <Ast.valtype> constexp
%type <string> varexp
%type <Ast.expr> opexp
%type <Ast.expr> expr
%start <Ast.stmt list> main

%%

main:
  | block = nonempty_list(stmt) EOF
    { block }

stmtBlock:
  | sl = list(stmt)
    { sl } (* couldn't get away without it. *)

stmt:
  | st = declStmt SEMI
    { st }
  | st = assignStmt SEMI
    { st }
  | st = ifStmt
    { st }

declStmt:
  | VAR v = varexp t=option(preceded(COLON, typeexp)) ASSIGN e = expr
    { StmtDecl (v, t, e) }

assignStmt:
  | v=varexp ASSIGN e=expr
    { StmtAssign (v, e) }

ifStmt:
  | IF LPAREN e=expr RPAREN THEN
    tb=stmtBlock
    eifs=list(elsifBlock)
    eb=option(preceded(ELSE, stmtBlock))
    END
    { StmtIf (e, tb, eifs, eb) }

elsifBlock:
  | ELSIF LPAREN e=expr RPAREN THEN body=stmtBlock
    { (e, body) }

typeexp:
  | tn=IDENT_LC
    { TypeName tn }

(* Expressions are what evaluates to a value. *)
expr:
  | c = constexp
    { ExpConst c }
  | v = varexp        (* then objexp! *)
    { ExpVar v }
  | o=opexp
    { o }
(* objexp to replace varexp *)
  | LPAREN e=expr RPAREN
    { e }

constexp:
  | i = ICONST
    { IntVal i }
  | f = FCONST
    { FloatVal f }
(* | STRCONST | *)

varexp:
  | v = IDENT_LC
    { v }

opexp:
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

(* parameterized rule to add location info to any nonterminal. *)
located(X):
  | x=X { { loc = $loc; value = x } }
