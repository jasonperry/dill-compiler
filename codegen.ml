(** Code generation module *)

open Common
open Ast
open Types
open Symtable1
open Llvm

exception CodegenError of string

(* Trying not to make a new context per module. OK so far. *)
let context = global_context() 
let float_type = double_type context
let int_type = i32_type context
let bool_type = i1_type context
let void_type = void_type context


let rec gen_expr the_module builder syms tenv (ex: typetag expr) = 
  match ex.e with
  | ExpConst (IntVal i) -> const_int int_type i
  | ExpConst (FloatVal f) -> const_float float_type f
  | ExpConst (BoolVal b) -> const_int bool_type (if b then 1 else 0)
  (* stmtDecl will create new symtable entry ,this will get it. *)
  | ExpVar (varname, _) -> (
     let (entry, _) = Symtable.findvar varname syms in
     match entry.addr with
     | None ->
        (* find it in the params and use the llvalue directly *)
        failwith ("BUG gen_expr: alloca address not present for " ^ varname)
     | Some alloca -> build_load alloca varname builder
  )
  | ExpUnop (op, e1) -> (
    (* there are const versions of the ops I could try to put in later, 
     * for optimization. *)
    let e1val = gen_expr the_module builder syms tenv e1 in
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
    let e1val = gen_expr the_module builder syms tenv e1 in
    let e2val = gen_expr the_module builder syms tenv e2 in
    (* for other tags, we'll emit the appropriate procedure call. *)
    if e1.decor = int_ttag then
      match op with
      | OpTimes -> build_mul e1val e2val "imultemp" builder
      | OpDiv -> build_sdiv e1val e2val "sdivtemp" builder
      | OpPlus -> build_add e1val e2val "iaddtemp" builder
      | OpMinus -> build_sub e1val e2val "isubtemp" builder
      | OpMod -> build_srem e1val e2val "modtemp" builder
      | OpEq -> build_icmp Icmp.Eq e1val e2val "ieqtemp" builder
      | OpNe -> build_icmp Icmp.Ne e1val e2val "inetemp" builder
      | OpLt -> build_icmp Icmp.Slt e1val e2val "ilttemp" builder
      | OpGt -> build_icmp Icmp.Sgt e1val e2val "igttemp" builder
      | OpLe -> build_icmp Icmp.Sle e1val e2val "iletemp" builder
      | OpGe -> build_icmp Icmp.Sge e1val e2val "igetemp" builder
      | OpBitAnd -> build_and e1val e2val "andtemp" builder
      | OpBitOr -> build_or e1val e2val "ortemp" builder
      | OpBitXor -> build_xor e1val e2val "xortemp" builder
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
    let (entry, _) = Symtable.findproc fname syms in
    match lookup_function entry.procname the_module with
    (* assumes function names are unique. this may mean that
     * procedure entries will need to store a "canonicalized" proc name
     * (or at least the class name, so it can be generated.) *)
    | None -> failwith "BUG: unknown function name in codegen"
    | Some callee ->
       let args = List.map (gen_expr the_module builder syms tenv) params
                  |> Array.of_list in
       build_call callee args "calltmp" builder
  )
  | ExpNullAssn (_, _, _, _) ->
     failwith "BUG: null assign found outside condition"


let rec gen_stmt the_module builder tenv (stmt: (typetag, 'a st_node) stmt) =
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
       gen_stmt the_module builder tenv
         {st=StmtAssign (varname, initexp); decor=syms}
  )

  | StmtAssign (varname, ex) -> (
     let (entry, _) = Symtable.findvar varname syms in
     let expval = gen_expr the_module builder syms tenv ex in
     match entry.addr with
     | None -> failwith ("BUG stmtAssign: alloca address not present for "
                         ^ varname)
     | Some alloca ->
        ignore (build_store expval alloca builder)
        (* print_string (string_of_llvalue store) *)
  )

  | StmtNop -> () (* will I need to generate so labels work? *)

  | StmtReturn eopt -> (
    (match eopt with
     | None -> ignore (build_ret_void builder)
     | Some rexp -> 
        let expval = gen_expr the_module builder syms tenv rexp in
        ignore (build_ret expval builder)
    );
    (* Add a basic block after in case a break is added afterwards. *)
    let this_function =
      Option.get (lookup_function
                    (Option.get syms.in_proc).procname the_module) in
    let retcont_bb = append_block context "retcont" this_function in
    position_at_end retcont_bb builder;
  )

  | StmtIf (cond, thenblock, elsifs, elsopt) -> (
    let condres = 
      match cond.e with
      | ExpNullAssn (_,_,_,_) (* (isDecl, varname, _, ex) *) ->
         (* if it's a null-assignment, set the var's addr in thenblock's syms *)
         failwith "Null assignment not implemented yet"
      | _ -> gen_expr the_module builder syms tenv cond
    in
    let start_bb = insertion_block builder in
    let the_function = block_parent start_bb in
    let then_bb = append_block context "then" the_function in
    position_at_end then_bb builder;
    List.iter (gen_stmt the_module builder tenv) thenblock;
    let new_then_bb = insertion_block builder in
    (* elsif generating code *)
    let gen_elsif (cond, block) =
      (* however, need to insert conditional jump and jump-to-merge later *)
      let cond_bb = append_block context "elsifcond" the_function in
      position_at_end cond_bb builder;
      let condres = 
        match cond.e with
        | ExpNullAssn (_,_,_,_) (* (isDecl, varname, _, ex) *) ->
           (* if it's a null-assignment, set the var addr in thenblock's syms *)
           failwith "Null assignment not implemented yet"
        | _ -> gen_expr the_module builder syms tenv cond in
      let then_bb = append_block context "elsifthen" the_function in
      position_at_end then_bb builder;
      List.iter (gen_stmt the_module builder tenv) block;
      (condres, cond_bb, then_bb, insertion_block builder) (* for jumps *)
    in
    let elsif_blocks = List.map gen_elsif elsifs in
    (* generating dummy else block regardless. *)
    let else_bb = append_block context "else" the_function in
    position_at_end else_bb builder;
    (match elsopt with
     | Some elseblock ->
        List.iter (gen_stmt the_module builder tenv) elseblock
     | None -> ());
    let new_else_bb = insertion_block builder in
    let merge_bb = append_block context "ifcont" the_function in
    (* kaleidoscope inserts the phi here *)
    (* position_at_end merge_bb builder; *)
    position_at_end start_bb builder;
    (* Still loop to the /original/ then block! *)
    let firstelse =
      match elsif_blocks with
      | [] -> else_bb
      | (_, condblk, _, _) :: _ -> condblk in
    ignore (build_cond_br condres then_bb firstelse builder);
    position_at_end new_then_bb builder;
    ignore (build_br merge_bb builder);
    (* add conditional and unconditional jumps between elsif blocks *)
    let rec add_elsif_jumps = function
      | [] -> ()
      | (condres, condblk, thenblk, endblk) :: rest ->
         position_at_end condblk builder;
         (match rest with
          | [] ->
             ignore (build_cond_br condres thenblk else_bb builder);
          | (_, nextblk, _, _) :: _ -> 
             ignore (build_cond_br condres thenblk nextblk builder);
         );
         position_at_end endblk builder;
         ignore (build_br merge_bb builder);
         add_elsif_jumps rest
    in
    add_elsif_jumps elsif_blocks;
    position_at_end new_else_bb builder;
    ignore (build_br merge_bb builder);
    position_at_end merge_bb builder
  )

  | StmtWhile (cond, body) -> (
    (* test block, loop block, afterloop block. *)
    let the_function = block_parent (insertion_block builder) in 
    let test_bb = append_block context "test" the_function in
    (* jump from current block into this one *)
    ignore (build_br test_bb builder);
    (* insert code in test block to compute condition (put test in later) *)
    position_at_end test_bb builder;
    let condres = match cond.e with
      | ExpNullAssn (_,_,_,_) -> failwith "null assign not yet implemented"
      | _ -> gen_expr the_module builder syms tenv cond in
    (* Create loop block and fill it in *)
    let loop_bb = append_block context "loop" the_function in
    position_at_end loop_bb builder;
    List.iter (gen_stmt the_module builder tenv) body;
    (* add unconditional jump back to test *)
    let new_loop_bb = insertion_block builder in (* don't need? *)
    position_at_end new_loop_bb builder;         (* is it there already? *)
    ignore (build_br test_bb builder);
    let merge_bb = append_block context "afterloop" the_function in
    (* Now, add the conditional branch in the test block. *)
    position_at_end test_bb builder;
    ignore (build_cond_br condres loop_bb merge_bb builder);
    position_at_end merge_bb builder    
  )
  | StmtCall {decor=_; e=ExpCall (fname, params)} -> (
    let (entry, _) = Symtable.findproc fname syms in
    match lookup_function entry.procname the_module with
    (* assumes function names are unique. this may mean that
     * procedure entries will need to store a "canonicalized" proc name
     * (or at least the class name, so it can be generated.) *)
    | None -> failwith "BUG: unknown function name in codegen"
    | Some callee ->
       let args = List.map (gen_expr the_module builder syms tenv) params
                  |> Array.of_list in
       (* instructions returning void cannot have a name *)
       ignore (build_call callee args "" builder)
  )
  | StmtCall _ -> failwith "BUG: StmtCall without CallExpr"
  | StmtBlock _ -> failwith "not implemented"

(** Get a default value for a type. Used only for globals. *)
(* and maybe for unreachable returns *)
let default_value ttag =
  (* I'll need some kind of ttag->llvm type mapping eventually. *)
  if ttag = int_ttag then const_int int_type 0
  else if ttag = float_ttag then const_float float_type 0.0
  else if ttag = bool_ttag then const_int bool_type 0
  else failwith ("Cannot generate default value for type "
                 ^ typetag_to_string ttag)


(** generate code for a global variable declaration (init code in main) *)
let gen_global_decl the_module builder tenv (gdecl: ('ed, 'sd) globalstmt) =
  let syms = gdecl.decor in
  let (entry, _) = Symtable.findvar gdecl.varname syms in
    (* define_global doesn't use the builder, puts at the top *)
    (* The default value will never be used, it's just to satisfy clang. *)
    (* A more optimized approach would be to check if it's a constExpr 
     * and use that if it's there. *)
  let gaddr =
    define_global gdecl.varname (default_value entry.symtype) the_module in
  Symtable.set_addr syms gdecl.varname gaddr;
  match gdecl.init with
  | Some ex ->
     let gval = gen_expr the_module builder syms tenv ex in
     (* This assumes builder is positioned correctly. *)
     ignore (build_store gval gaddr builder)
  | None -> ()


(** Convert a type tag from the AST into a suitable LLVM type. *)
let ttag_to_llvmtype ttag =
  if ttag = void_ttag then void_type
  else if ttag = int_ttag then int_type
  else if ttag = float_ttag then float_type
  else if ttag = bool_ttag then bool_type
  else failwith "Unsupported type for procedure"   


(** Generate llvm function decls for a set of procs from the AST. *)
(* Could this work for both local and imported functions? *)
let gen_fdecls the_module fsyms =
  StrMap.iter (fun _ procentry ->
      let rtype = ttag_to_llvmtype procentry.rettype in
      let params = List.map (fun entry -> ttag_to_llvmtype entry.symtype)
                     procentry.fparams
                   |> Array.of_list in
      (* print_string ("Declaring function " ^ procentry.procname ^ "\n"); *)
      ignore (declare_function procentry.procname
                (function_type (rtype) params) the_module)
    (* We could set names for arguments here. *)
    ) fsyms  (* returns () *)


(** generate code for a procedure body (its declaration should already
 * be defined *)
let gen_proc the_module builder tenv proc =
  let fname = proc.decl.name in
  (* procedure is now defined in its own scope, so "getproc" *)
  let fentry = Symtable.getproc fname proc.decor in 
  match lookup_function fentry.procname the_module with
  | None -> failwith "BUG: llvm function lookup failed"
  | Some func -> 
     (* should I define_function here, not add to the existing decl? *)
     let entry_bb = append_block context "entry" func in
     position_at_end entry_bb builder;
     (* create storage for all params (needed for uniformity in
      * codegen for vars.) *)
     List.iteri (fun i (varname, _) ->
         let entrybuilder =
           builder_at context (instr_begin (entry_block func)) in
         let alloca =
           build_alloca (type_of (param func i)) varname entrybuilder in
         ignore (build_store (param func i) alloca builder);
         Symtable.set_addr proc.decor varname alloca
       ) proc.decl.params;
     List.iter (gen_stmt the_module builder tenv) (proc.body);
     (* If it doesn't end in a terminator, add either a void return or a 
      * dummy branch. *)
     if Option.is_none (block_terminator (insertion_block builder)) then
       (* if return_type (type_of func) = void_type then *)
       if fentry.rettype = void_ttag then (
         ignore (build_ret_void builder);
         Llvm_analysis.assert_valid_function func
       )
       else (
         (* dummy return, should be unreachable *)
         ignore (build_ret (default_value fentry.rettype) builder);
         Llvm_analysis.assert_valid_function func
       )


(** Generate code for an entire module. *)
let gen_module tenv topsyms (modtree: (typetag, 'a st_node) dillmodule) =
  let the_module = create_module context (modtree.name ^ ".ll") in
  let builder = builder context in
  (* Generate decls for imports (already in the top symbol table node.) *)
  gen_fdecls the_module topsyms.fsyms;
  (* The next symtable node underneath has this module's proc declarations *)
  (* if List.length (topsyms.children) <> 1 then
    failwith "BUG: didn't find unique module-level symtable"; *)
  let modsyms = List.hd (topsyms.children) in
  gen_fdecls the_module modsyms.fsyms;
  (* Procedures declared in this module should already be here. *)
  (* if there are globals or an init block, create an init procedure *)
  if modtree.globals <> [] || modtree.initblock <> [] then (
    let initproc =
      (* TODO: figure out how to pick a main. Will need to link all init blocks together? *)
      define_function "main" (* "Module.__init" *)
        (function_type (void_type) [||])
        the_module in
    (* let entry_bb = append_block context "entry" initproc in *)
    position_at_end (entry_block initproc) builder; (* global inits go there *)
    List.iter (gen_global_decl the_module builder tenv) modtree.globals;
    List.iter (gen_stmt the_module builder tenv) modtree.initblock;
    ignore (build_ret_void builder)
  );
  List.iter (gen_proc the_module builder tenv) modtree.procs;
  (* Llvm_analysis.assert_valid_module the_module; *)
  the_module
