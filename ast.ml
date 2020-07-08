type valtype =
  | FloatVal of float
  | IntVal of int

type unary_op =
  | OpNeg

type binary_op =
  | OpPlus
  | OpMinus
  | OpTimes
  | OpDiv

(* lexing info *)
type 'a located =
  { loc: Lexing.position * Lexing.position; value: 'a }

(* type expr =
  raw_expr located  *)

type stmt = 
  | StmtAssign of string * expr
  | StmtDecl of string * (* typeexpr *) expr

and expr =
  | ExpConst of valtype
  | ExpVar of string     (* later a type for pieces of an object expr. *)
  | ExpBinop of expr * binary_op * expr
  | ExpUnop of unary_op * expr
  (* No parentheses *)
