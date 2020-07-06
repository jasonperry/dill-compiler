%token <int> ICONST  (* TODO: make it full 32-bit *)
%token <float> FCONST
%token LPAREN RPAREN
(* %token ASSIGN EQUAL COLON SEMI COMMA DOT ARROW 
%token STAR AMP *)
%token UMINUS PLUS MINUS TIMES DIV
%token EOL

(* ordering of these indicates precedence, low to high *)
%left PLUS MINUS
%left TIMES DIV
%nonassoc UMINUS

%type <Ast.valtype> constexp
%type <Ast.expr> opexp
%type <Ast.expr> expr
%start <Ast.expr> main
%{ open Ast %}

%%

(* do I need this to include the EOF so it's accepted? apparently. *)
main:
  | e = expr EOL
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
(* Won't work e1 and e2 are valtypes *)
(* Would be nice if I could put some common code here to check e1 & e2 *)
  | e1 = expr PLUS e2 = expr
    { ExpBinop (e1, OpPlus, e2) }
  | e1 = expr MINUS e2 = expr
    { ExpBinop (e1, OpMinus, e2) }
  | e1 = expr TIMES e2 = expr
    { ExpBinop (e1, OpTimes, e2) }
  | e1 = expr DIV e2 = expr
    { ExpBinop (e1, OpDiv, e2) }
  | MINUS e = expr %prec UMINUS
    { ExpUnop (OpNeg, e) }
