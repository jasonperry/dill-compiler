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
  raw_expr located 

and type raw_expr = *)
type expr =
  | ExpConst of valtype
  | ExpBinop of expr * binary_op * expr
  | ExpUnop of unary_op * expr
  (* No parentheses *)
