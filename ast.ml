(** Abstract syntax tree structure *)

(* open Types *) (* yay, now generic over what it's decorated with! *)

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
(* type typeinfo = { ty: typetag } *) (* just use typetag directly. *)

type 'a raw_expr = (* should really probably change to inline records *)
  | ExpConst of consttype
  | ExpVar of string  (* later a type for pieces of an object expr *)
  | ExpBinop of 'a expr * binary_op * 'a expr
  | ExpUnop of unary_op * 'a expr
  | ExpCall of string * 'a expr list
  | ExpNullAssn of bool * string * 'a expr (* true if declaring new var *)

(* type typed_expr =
  { ty: typetag option; e: raw_expr } *)
and 'a expr = { e: 'a raw_expr; decor: 'a }

(* "redecorate" helper function. Bummer that we have to reconstruct. *)
let redeco_exp exp deco =
  match exp.e with
  | ExpConst c -> { e=ExpConst c; decor=deco }
  | ExpVar s -> { e=ExpVar s; decor=deco }
  | _ -> failwith "don't need redeco on recursive constructors"

(* and expr =
  typed_expr located *)

(** Like a typeTag, but can contain variables (eventually) *)
type typeExpr =
  | TypeName of string

type ('a,'b) raw_stmt = 
  | StmtDecl of string * typeExpr option * 'a expr
  | StmtAssign of string * 'a expr  (* need to make var expr on left? *)
  | StmtReturn of 'a expr option
  (* Hmm, may want to make this a record, it's a little unwieldy. *)
  | StmtIf of 'a expr * (* cond *)('a,'b) stmt list (* then block *)
              * ('a expr * ('a,'b) stmt list) list (* elsif blocks *)
              * ('a,'b) stmt list option (* else block *)
  | StmtCall of 'a expr  (* have to check the function returns void *)
  | StmtBlock of ('a,'b) stmt list

and ('a,'b) stmt = { st: ('a,'b) raw_stmt; decor: 'b }
(* and stmt = raw_stmt located *)

type 'a raw_procdecl = {
    name: string;
    params: (string * typeExpr) list;
    rettype: typeExpr
  }
and 'a procdecl = { pdecl: 'a raw_procdecl; decor: 'a;  }

type ('a,'b) raw_proc = {
    decl: 'b procdecl;
    body: ('a,'b) stmt list
  }

type ('a,'b) proc = { proc: ('a,'b) raw_proc; decor: 'b }


(* Idea: use result types for typechecking the AST: either a new decorated
 * node or an error. *)

(* START OF TYPECHECKING CODE (maybe move it) *)

(* check_expr: expr -> typed_expr result or just node? *)
(* let check_expr env e = [] *)
