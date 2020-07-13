%token <int> ICONST  (* TODO: make it full 32-bit *)
%token <float> FCONST
%token <string> IDENT_LC
%token <string> IDENT_UC
%token LPAREN RPAREN
%token ASSIGN COLON SEMI COMMA
(* %token EQUAL COMMA DOT ARROW 
%token STAR AMP *)
%token VAR
%token IF THEN ELSIF ELSE END
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

%type <Ast.valtype> constExp
%type <string> varExp
%type <Ast.expr> opExp
%type <Ast.expr> expr
%start <Ast.proc list * Ast.stmt list> main

%%

main:
  | procs=list(proc) block=nonempty_list(stmt) EOF
    { (procs, block) }

proc:
  | PROC pn=procName LPAREN pl=paramList RPAREN
      COLON rt=typeExp ASSIGN sb=stmtBlock END en=procName 
    { if pn = en then
	{ name=pn; params=pl; rettype=rt; body=sb }
      else  (* TODO: try "new way" error handling (Menhir Ch. 11) *)
	$syntaxerror
    }

procName:
  (* later, may include dots and stuff. *)
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

stmtBlock:
  | sl = list(stmt)
    { sl }

stmt:
  | st = declStmt
    { st }
  | st = assignStmt
    { st }
  | st = ifStmt
    { st }
  | st = returnStmt
    { st }
  | st = callStmt
    { st }

declStmt:
  | VAR v = varExp t=option(preceded(COLON, typeExp)) ASSIGN e = expr SEMI
    { StmtDecl (v, t, e) }

assignStmt:
  | v=varExp ASSIGN e=expr SEMI
    { StmtAssign (v, e) }

returnStmt:
  | RETURN e=expr SEMI
    { StmtReturn e }

callStmt:
  | e=expr SEMI
    { StmtCall e }

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

typeExp:
  (* This will be elaborated to include array, list, type variables,... *)
  | tn=IDENT_LC
    { TypeName tn }

(* Expressions are what evaluates to a value. *)
expr:
  | c = constExp
    { ExpConst c }
  | v = varExp        (* then objexp! *)
    { ExpVar v }
  | o=opExp
    { o }
  | ce=callExp
    { ce }
(* objexp to replace varexp *)
  | LPAREN e=expr RPAREN
    { e }

constExp:
  | i = ICONST
    { IntVal i }
  | f = FCONST
    { FloatVal f }
(* | STRCONST | *)

varExp:
  (* later, objExp will have other productions *)
  | v = varName
    { v }

varName:
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

(* parameterized rule to add location info to any nonterminal. *)
located(X):
  | x=X { { loc = $loc; value = x } }
