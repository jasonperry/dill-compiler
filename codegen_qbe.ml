(** Dill codegen for QBE backend. *)

(*open Common *)
open Ast
open Types
(* open Symtable1 *)
open Qbe

let gen_expr _(*theModule*) _(*syms*) _(*lltypes*) (ex: typetag expr) =
  match ex.e with
  | ExpConst (IntVal i) -> Const (LConst i)
  | _ -> failwith "unimplemented so far"

let res1 = Reg (Word, "res1")

let gen_module _(*tenv*) _(* topsyms*) =
  Qbe.new_module ()
