open Ast
open Types
open Symtable1
open Llvm

(* code to set up IR builder... *)
exception CodegenError of string

(* Augmented symentry record, with methods to easily add/get? *)
(* Maybe this is where I could use flex records or some kind of polymorphic 
   variant. Add new variants to symentry.
   Or, do it the old-fashioned way and just have a new node type also. *)

(* will I need sub-contexts later? for modules, yes *)
let context = global_context()
let the_module = create_module context "dillout.ll"
(* builder keeps track of current insert place *)
let builder = builder context
let float_type = double_type context
let int_type = i32_type context
let bool_type = i1_type context

let rec gen_expr syms tenv ex = 
  match ex.e with
  | ExpConst (IntVal i) -> const_int int_type i
  | ExpConst (FloatVal f) -> const_float float_type f
  | ExpConst (BoolVal b) -> const_int bool_type (if b then 1 else 0)
  (* stmtDecl will create new symtable entry ,this will get it. *)
  | ExpVar varname -> (
     let (entry, _) = Symtable.findvar varname syms in
     match entry.addr with
     | None -> failwith ("BUG: alloca address not present for " ^ varname)
     | Some alloca -> build_load alloca varname builder
  )
  | ExpUnop (op, e1) -> (
    (* there are const versions of the ops I could try to put in later, 
     * for optimization. *)
    let e1val = gen_expr syms tenv e1 in
    if e1.decor = int_ttag then 
      match op with
      (* type checker should catch negating an unsigned. *)
      | OpNeg -> build_neg e1val "inegtemp" builder
      | OpBitNot -> build_not e1val "bitnottemp" builder
      | _ -> failwith "BUG: Codegen type error in unary op (int)"
    else if e1.decor = float_ttag then
      match op with
      | OpNeg -> build_fneg e1val "fnegtemp" builder
      | _ -> failwith "BUG: Codegen type error in unary op (float)"
    else if e1.decor = bool_ttag then 
      match op with 
      | OpNot -> build_not e1val "boolnottemp" builder
      | _ -> failwith "BUG: Codegen type error in unary op (bool)"
    else
      failwith "BUG: Unknown type in unary op"
  )
  | ExpBinop (e1, op, e2) -> (
    let e1val = gen_expr syms tenv e1 in
    let e2val = gen_expr syms tenv e2 in
    (* for other tags, we'll emit the appropriate procedure call. *)
    if e1.decor = int_ttag then
      match op with
      | OpTimes -> build_mul e1val e2val "imultemp" builder
      | OpDiv -> build_sdiv e1val e2val "sdivtemp" builder
      | OpPlus -> build_add e1val e2val "iaddtemp" builder
      | OpMinus -> build_sub e1val e2val "isubtemp" builder
      | OpEq -> build_icmp Icmp.Eq e1val e2val "ieqtemp" builder
      | OpNe -> build_icmp Icmp.Ne e1val e2val "inetemp" builder
      | _ -> failwith "int binop Not implemented yet"
    else if e1.decor = float_ttag then
      match op with
      | OpTimes -> build_fmul e1val e2val "fmultemp" builder
      | OpDiv -> build_fdiv e1val e2val "fdivtemp" builder
      | OpPlus -> build_fadd e1val e2val "faddtemp" builder
      | OpMinus -> build_fsub e1val e2val "fsubtemp" builder
      | _ -> failwith "float binop Not implemented yet"
    else if e1.decor = bool_ttag then
      match op with
      | OpAnd -> build_and e1val e2val "bandtemp" builder
      | OpOr -> build_or e1val e2val "bortemp" builder
      | OpEq -> build_icmp Icmp.Eq e1val e2val "beqtemp" builder
      | OpNe -> build_icmp Icmp.Ne e1val e2val "bnetemp" builder
      | _ -> failwith "BUG: type error in boolean binop"
    else
      failwith "unknown type for binary operation"
  )
  | ExpCall (_, _) -> failwith "not implemented yet"
  | ExpNullAssn (_, _, _, _) -> failwith "not implemented yet"

let rec gen_stmt tenv (stmt: (_, _) stmt) =
  let syms = stmt.decor in
  (* later: look up types in tenv *)
  match stmt.st with
  | StmtDecl (varname, _, eopt) -> (
    (* technically, decl should only lookup in this scope. *)
    let (entry, _) = Symtable.findvar varname syms in
    let allocatype =
      if entry.symtype = int_ttag then int_type
      else if entry.symtype = float_ttag then float_type
      else if entry.symtype = bool_ttag then bool_type
      else failwith "Unknown type for allocation"
    in
    print_string ("about to try allocating for " ^ varname ^ "\n");
    (* Need to save the result? Don't think so, I'll grab it for stores. *)
    (* position_builder (instr_begin (insertion_block builder)) builder; *)
    Symtable.set_addr syms varname
      (* TODO If in a function, will need to build it in entry block,
       * so it goes in the stack frame *) 
      (declare_global allocatype varname the_module);
    match eopt with
    | None -> ()
    | Some initexp ->
       (* make a fake assignment statement to avoid duplication. *)
       gen_stmt tenv {st=StmtAssign (varname, initexp); decor=syms}
  )
  | StmtAssign (varname, ex) -> (
     let (entry, _) = Symtable.findvar varname syms in
     let expval = gen_expr syms tenv ex in
     match entry.addr with
     | None -> failwith ("BUG: alloca address not present for " ^ varname)
     | Some alloca ->
        print_string "Found allocator for assignment, building store...\n";
        let store = build_store expval alloca builder in
        print_string (string_of_llvalue store)
  )
  | StmtReturn _ -> failwith "not implemented"
  | StmtIf (_, _, _, _) -> failwith "not implemented"
  | StmtWhile (_, _) -> failwith "not implemented"
  | StmtCall _ -> failwith "not implemented"
  | StmtBlock _ -> failwith "not implemented"

let gen_proc _ _ _ =
  failwith "Not implemented yet"

let gen_module tenv (_, block) =
  List.iter (gen_stmt tenv) block;
  (* print_module "./dillout.ll" the_module *)
  print_string (string_of_llmodule the_module);
  the_module
  
  
