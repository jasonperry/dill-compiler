open Ast
(* open Analyzer (* for symbol table definitions *) *)
open Llvm

(* code to set up IR builder... *)
exception CodegenError of string

(* will I need sub-contexts later? *)
let context = global_context()
let the_module = create_module context "datlang emitter"
(* builder keeps track of current insert place *)
let builder = builder context
let named_values:(string, llvalue) Hashtbl.t = Hashtbl.create 10
let double_type = double_type context
let int_type = i32_type context

let rec codegen_expr e = 
  match e.value with
  | ExpConst (IntVal i) -> const_int int_type i
  | ExpConst (FloatVal f) -> const_float double_type f
