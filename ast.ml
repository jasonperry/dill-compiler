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

(** position info to decorate the AST with *)
type locinfo = Lexing.position * Lexing.position

(** This is still used for error messages. *)
type 'a located =
  { loc: Lexing.position * Lexing.position; value: 'a }

(** Type info to decorate the second verion of the AST *)
type typeinfo = { ty: typetag }
(* type typed_expr =
  { ty: typetag option; e: raw_expr } *)

type 'a raw_expr = (* should really probably change to inline records *)
  | ExpConst of consttype
  | ExpVar of string  (* later a type for pieces of an object expr *)
  | ExpBinop of 'a expr * binary_op * 'a expr
  | ExpUnop of unary_op * 'a expr
  | ExpCall of string * 'a expr list
  | ExpNullAssn of bool * string * 'a expr (* true if declaring new var *)

and 'a expr = { decor: 'a; e: 'a raw_expr }

(* and expr =
  typed_expr located *)

(** Like a typeTag, but can contain variables (eventually) *)
type typeExpr =
  | TypeName of string

type 'a raw_stmt = 
  | StmtDecl of string * typeExpr option * 'a expr
  | StmtAssign of string * 'a expr  (* need to make var expr on left? *)
  | StmtReturn of 'a expr option
  (* Hmm, may want to make this a record, it's a little unwieldy. *)
  | StmtIf of 'a expr * 'a stmt list * ('a expr * 'a stmt list) list
              * 'a stmt list option
  | StmtCall of 'a expr  (* have to check the function returns void *)
  | StmtBlock of 'a stmt list

and 'a stmt = { decor: 'a; st: 'a raw_stmt }
(* and stmt = raw_stmt located *)

type 'a raw_procdecl = {
    name: string;
    params: (string * typeExpr) list;
    rettype: typeExpr
  }
and 'a procdecl = { decor: 'a; pdecl: 'a raw_procdecl }

type 'a raw_proc = {
    decl: 'a procdecl;
    body: 'a stmt list
  }

type 'a proc = { decor: 'a; proc: 'a raw_proc }


(* Idea: use result types for typechecking the AST: either a new decorated
 * node or an error. *)

(* START OF TYPECHECKING CODE (maybe move it) *)

(* check_expr: expr -> typed_expr result or just node? *)
(* let check_expr env e = [] *)
