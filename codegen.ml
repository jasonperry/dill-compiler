open Ast
open Types
(* open Analyzer (* for symbol table definitions *) *)
open Llvm

(* code to set up IR builder... *)
exception CodegenError of string

(* Augmented symentry record, with methods to easily add/get? *)
(* Maybe this is where I could use flex records or some kind of polymorphic 
   variant. Add new variants to symentry.
   Or, do it the old-fashioned way and just have a new node type also. *)

(* will I need sub-contexts later? *)
let context = global_context()
let the_module = create_module context "datlang emitter"
(* builder keeps track of current insert place *)
let builder = builder context
(* TODO: change this to be an augmented version of the symbol table. *)
let named_values: (string, llvalue) Hashtbl.t = Hashtbl.create 10
let double_type = double_type context
let int_type = i32_type context

let rec codegen_expr syms tenv e = 
  match e.value with
  | ExpConst (IntVal i) -> const_int int_type i
  | ExpConst (FloatVal f) -> const_float double_type f
