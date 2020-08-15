(** Abstract syntax tree structure *)

(* open Types *) (* yay, now generic over what it's decorated with! *)

type consttype =
  | FloatVal of float
  | IntVal of int  (* TODO: make int32 to avoid OCaml 31-bit ints *)
  | BoolVal of bool

type unary_op =
  | OpNeg
  | OpBitNot
  | OpNot

type binary_op =
  | OpTimes
  | OpDiv
  | OpMod  (* Want to make it the "proper" mod *)
  | OpPlus
  | OpMinus
  | OpBitAnd
  | OpBitOr
  | OpBitXor
  | OpEq
  | OpNe
  | OpLt
  | OpGt
  | OpLe
  | OpGe
  | OpAnd
  | OpOr

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
  | StmtWhile of 'a expr (* cond *) * ('a, 'b) stmt list (* body *)
  | StmtCall of 'a expr  (* have to check the function returns void *)
  | StmtBlock of ('a,'b) stmt list

and ('a,'b) stmt = { st: ('a,'b) raw_stmt; decor: 'b }
(* and stmt = raw_stmt located *)

(* Note that this doesn't need a decoration type param, it's not recursive. *)
type raw_procdecl = {
    name: string;
    (* One could imagine removing the typeExprs after analysis. *)
    params: (string * typeExpr) list;
    rettype: typeExpr
  }
(* I thought about removing the decoration from the decl, but it can
 * stand on its own in an interface file, so I guess it needs it. *)
and 'a procdecl = { pdecl: raw_procdecl; decor: 'a;  }

type ('a,'b) raw_proc = {
    decl: 'b procdecl;
    body: ('a,'b) stmt list
  }

type ('a,'b) proc = { proc: ('a,'b) raw_proc; decor: 'b }

