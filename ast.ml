(** Abstract syntax tree structure *)

open Types

type consttype =
  | FloatVal of float
  | IntVal of int

type unary_op =
  | OpNeg

type binary_op =
  | OpPlus
  | OpMinus
  | OpTimes
  | OpDiv

(* position info *)
type 'a located =
  { loc: Lexing.position * Lexing.position; value: 'a }

type typed_expr =
  { ty: typetag option; e: raw_expr }

and raw_expr =
  | ExpConst of consttype
  | ExpVar of string     (* later a type for pieces of an object expr. *)
  | ExpBinop of expr * binary_op * expr
  | ExpUnop of unary_op * expr
  | ExpCall of string * expr list

and expr =
  typed_expr located

type typeExpr =
  | TypeName of string  (* type variables later *)

type raw_stmt = 
  | StmtDecl of string * typeExpr option * expr
  | StmtAssign of string * expr
  | StmtReturn of expr
  (* Hmm, may want to make this a record, it's a little unwieldy. *)
  | StmtIf of expr * stmt list * (expr * stmt list) list * stmt list option
  | StmtCall of expr  (* have to check the function returns void *)

and stmt = raw_stmt located

type raw_procdecl = {
    name: string;
    params: (string * typeExpr) list;
    rettype: typeExpr
  }
and procdecl = raw_procdecl located

type raw_proc = {
    decl: procdecl;
    body: stmt list
  }

type proc = raw_proc located


(* Idea: use result types for typechecking the AST: either a new decorated
 * node or an error. *)

(* START OF TYPECHECKING CODE (maybe move it) *)

(* check_expr: expr -> typed_expr result or just node? *)
(* let check_expr env e = [] *)
