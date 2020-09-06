open Ast
open Types
open Symtable1
open Llvm

exception CodegenError of string

(* code to set up IR builder. Later can be per-module *)
let context = global_context()
let float_type = double_type context
let int_type = i32_type context
let bool_type = i1_type context
let void_type = void_type context

let the_module = create_module context "dillout.ll"
(* builder keeps track of current insert place *)
let builder = builder context

let rec gen_expr syms tenv ex = 
  match ex.e with
  | ExpConst (IntVal i) -> const_int int_type i
  | ExpConst (FloatVal f) -> const_float float_type f
  | ExpConst (BoolVal b) -> const_int bool_type (if b then 1 else 0)
  (* stmtDecl will create new symtable entry ,this will get it. *)
  | ExpVar varname -> (
     let (entry, _) = Symtable.findvar varname syms in
     match entry.addr with
     | None ->
        (* find it in the params and use the llvalue directly *)
        failwith ("BUG: alloca address not present for " ^ varname)
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
  | ExpCall (fname, params) -> (
    match lookup_function fname the_module with
    (* assumes function names are unique. this may mean that
     * procedure entries will need to store a "canonicalized" proc name
     * (or at least the class name, so it can be generated.) *)
    | None -> failwith "BUG: unknown function name in codegen"
    | Some callee ->
       let args = List.map (gen_expr syms tenv) params
                  |> Array.of_list in
       build_call callee args "calltmp" builder
  )
  | ExpNullAssn (_, _, _, _) ->
     failwith "BUG: null assign found outside condition"

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
    (* print_string ("about to try allocating for " ^ varname ^ "\n"); *)
    (* Need to save the result? Don't think so, I'll grab it for stores. *)
    (* position_builder (instr_begin (insertion_block builder)) builder; *)
    let blockstart =
      builder_at context (instr_begin (insertion_block builder)) in
    let alloca = build_alloca allocatype varname blockstart in 
    Symtable.set_addr syms varname alloca;
      (* TODO If in a function, will need to build it in entry block,
       * so it goes in the stack frame *)
      (* BUT, let's just try to alloca it wherever we are? 
       * No, let's do it in the entry block. shadowing will just work? *)
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
        ignore (build_store expval alloca builder)
        (* print_string (string_of_llvalue store) *)
  )
  | StmtNop -> () (* will I need to generate so labels work? *)
  | StmtReturn eopt -> (
    match eopt with
    | None -> ignore (build_ret_void builder)
    | Some rexp -> 
       let expval = gen_expr syms tenv rexp in
       ignore (build_ret expval builder)
  )
  | StmtIf (cond, thenblock, _, elsopt) -> (
    let condres = 
      match cond.e with
      | ExpNullAssn (_,_,_,_) (* (isDecl, varname, _, ex) *) ->
         (* if it's a null-assignment, set the var's addr in thenblock's syms *)
         failwith "Null assignment not implemented yet"
      | _ -> gen_expr syms tenv cond
    in
    (* Maybe I don't need this, could just use the i1 value in the branch. *)
    (* let one = const_int bool_type 1 in
     * let condval = build_icmp Icmp.Eq condres one "ifcond" builder in *)
    (* wonder if it's easier to make the elsif blocks nested. *)
    let start_bb = insertion_block builder in
    let outer_bb = block_parent start_bb in
    let then_bb = append_block context "then" outer_bb in
    position_at_end then_bb builder;
    List.iter (gen_stmt tenv) thenblock;
    let new_then_bb = insertion_block builder in
    (* generating dummy else block regardless. *)
    let else_bb = append_block context "else" outer_bb in
    position_at_end else_bb builder;
    (match elsopt with
     | Some elseblock ->
        List.iter (gen_stmt tenv) elseblock
     | None -> ());
    let new_else_bb = insertion_block builder in
    let merge_bb = append_block context "ifcont" outer_bb in
    (* kaleidoscope inserts the phi here *)
    (* position_at_end merge_bb builder; *)
    position_at_end start_bb builder;
    ignore(build_cond_br condres then_bb else_bb builder);
    (* add unconditional jumps at end of blocks *)
    position_at_end new_then_bb builder;
    ignore (build_br merge_bb builder);
    position_at_end new_else_bb builder;
    ignore (build_br merge_bb builder);
    position_at_end merge_bb builder
  )
  | StmtWhile (_, _) -> failwith "not implemented"
  | StmtCall {decor=_; e=ExpCall (fname, params)} -> (
    match lookup_function fname the_module with
    (* assumes function names are unique. this may mean that
     * procedure entries will need to store a "canonicalized" proc name
     * (or at least the class name, so it can be generated.) *)
    | None -> failwith "BUG: unknown function name in codegen"
    | Some callee ->
       let args = List.map (gen_expr syms tenv) params
                  |> Array.of_list in
       (* instructions returning void cannot have a name *)
       ignore (build_call callee args "" builder)
  )
  | StmtCall _ -> failwith "BUG: StmtCall without CallExpr"
  | StmtBlock _ -> failwith "not implemented"

(** generate code for a global variable declaration *)
let gen_global_decl tenv stmt =
  match stmt.st with 
  | StmtDecl (varname, _, eopt) -> (
    let syms = stmt.decor in
    let (entry, _) = Symtable.findvar varname syms in
    let allocatype =
      (* I'll need some kind of ttag->llvm type mapping eventually. *)
      if entry.symtype = int_ttag then int_type
      else if entry.symtype = float_ttag then float_type
      else if entry.symtype = bool_ttag then bool_type
      else failwith "Unknown type for allocation" in
    (* I guess declare_global puts at the top automatically? *)
    let alloca = declare_global allocatype varname the_module in
    (match eopt with
     | Some ex ->
        let gval = gen_expr syms tenv ex in
        (* This assumes builder is positioned correctly. *)
        ignore (build_store gval alloca builder)
     | None -> ());
    Symtable.set_addr syms varname alloca
  )
  | _ -> failwith "BUG: Global statements should be checked to be decls"

(** Convert a type tag from the AST into a suitable LLVM type. *)
let ttag_to_llvmtype ttag =
  if ttag = void_ttag then void_type
  else if ttag = int_ttag then int_type
  else if ttag = float_ttag then float_type
  else if ttag = bool_ttag then bool_type
  else failwith "Unsupported type for procedure"   

(** Generate llvm function decls for a set of procs from the AST. *)
let gen_fdecls fsyms =
  StrMap.iter (fun _ procentry ->
      let rtype = ttag_to_llvmtype procentry.rettype in
      let params = List.map (fun entry -> ttag_to_llvmtype entry.symtype)
                     procentry.fparams
                   |> Array.of_list in
      ignore (declare_function procentry.procname
                (function_type (rtype) params) the_module)
    (* set names for arguments and store in symtable addr. 
     * actually, don't need to store? *)
    (* print_string ("Generated llvm decl for " ^ procentry.procname ^ "\n") *)
    ) fsyms  (* returns () *)

(** generate code for a procedure body (its declaration should already
 * be defined *)
let gen_proc tenv proc =
  let fname = proc.decl.pdecl.name in  (* sheesh. *)
  let fentry = match Symtable.findproc fname proc.decor with
    (* Maybe it's okay that the function name is in a parent scope. *)
    | None -> failwith "BUG: function not defined"
    | Some (procentry, _) -> procentry in
  match lookup_function fname the_module with
  | None -> failwith "BUG: llvm function lookup failed"
  | Some func -> (* do I need to prevent redecl here? Think not. *)
     (* should I define_function here, not add to the existing decl? *)
     let entry_bb = append_block context "entry" func in
     position_at_end entry_bb builder;
     (* create storage for all params (needed for uniformity in
      * codegen for vars. *)
     List.iteri (fun i (varname, _) ->
         let entrybuilder =
           builder_at context (instr_begin (entry_block func)) in
         let alloca =
           build_alloca (type_of (param func i)) varname entrybuilder in
         ignore (build_store (param func i) alloca builder);
         Symtable.set_addr proc.decor varname alloca
       ) proc.decl.pdecl.params;
     List.iter (gen_stmt tenv) (proc.body);
     (* If it doesn't end in a terminator, add either a void return or a 
      * dummy branch. *)
     if Option.is_none (block_terminator (insertion_block builder)) then
       (* if return_type (type_of func) = void_type then *)
       if fentry.rettype = void_ttag then
         ignore (build_ret_void builder)
       else 
         ignore (build_br entry_bb builder)


(** Generate code for an entire module. *)
let gen_module tenv topsyms modtree =
  (* Procedures declared in this module should already be here. *)
  gen_fdecls topsyms.fsyms;
  (* if there are globals or an init block, create an init procedure *)
  if modtree.globals <> [] || modtree.initblock <> [] then (
    let initproc =
      (* TODO: figure out how to pick a main. *)
      define_function "main" (* "Module.__init" *)
        (function_type (void_type) [||])
        the_module in
    (* let entry_bb = append_block context "entry" initproc in *)
    position_at_end (entry_block initproc) builder; (* global inits will go there *)
    List.iter (gen_global_decl tenv) modtree.globals;
    List.iter (gen_stmt tenv) modtree.initblock;
    ignore (build_ret_void builder)
    (* print_module "./dillout.ll" the_module *)
  );
  (* generate code for procs - how to associate with syms? 
   * probably easiest just to use llvm lookup_function after declare *)
  List.iter (gen_proc tenv) modtree.procs;
  the_module
