%token <int> ICONST  (* TODO: make it full 32-bit *)
%token <float> FCONST
%token LPAREN RPAREN
(* %token ASSIGN EQUAL COLON SEMI COMMA DOT ARROW 
%token STAR AMP *)
%token UMINUS PLUS MINUS TIMES DIV
%token EOF

(* ordering of these indicates precedence, low to high *)
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS

%{ open Ast %}

%type <Ast.valtype> constexp
%type <Ast.expr> opexp
%type <Ast.expr> expr
%start <Ast.expr> main

%%

(* do I need this to include the EOF so it's accepted? apparently. *)
main:
  | e = expr EOF
    { e }

(* Expressions are what evaluates to a value. *)
expr:
  | c = constexp
    { ExpConst c }
(* | varexp, then objexp!  *)
  | e = opexp
    { e }
(* objexp to replace varexp *)
  | LPAREN e = expr RPAREN
    { e }

constexp:
  | i = ICONST
    { IntVal i }
  | f = FCONST
    { FloatVal f }
(* | STRCONST | *)

opexp:
(* TODO: check type of subexps and apply promotion rules *)
(* Nope! Do everything with the AST. *)
  | e1 = expr PLUS e2 = expr
    { ExpBinop (e1, OpPlus, e2) }
  | e1 = expr MINUS e2 = expr
    { ExpBinop (e1, OpMinus, e2) }
  | e1 = expr TIMES e2 = expr
    { ExpBinop (e1, OpTimes, e2) }
  | e1 = expr DIV e2 = expr
    { ExpBinop (e1, OpDiv, e2) }
  | MINUS e = expr %prec UMINUS
    { ExpUnop (OpNeg, e) } (* need to learn what this trick does *)
