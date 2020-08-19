(** Semantic analyzer: check for errors and build type-decorated AST *)

open Types
open Ast
open Symtable1

exception SemanticError of string

(** Initial symbol table *)
(* later just make this in the top-level analyzer function *)
let root_st = Symtable.empty 

(* Analysis pass populates symbol table, including with types. 
 * Hopefully all possibilities of error can be caught in this phase. *)

(* Should I add pointers to the symbol table node for a given scope to the 
 * AST? Maybe, because if I just rely on following, the order matters,
 * Or else you'd need a unique identifier for each child. *)

(** Helper to match a formal with actual parameter list, for
   typechecking procedure calls. *)
let rec match_params (formal: st_entry list) (actual: typetag list) =
  match (formal, actual) with
  | ([], []) -> true
  | (_, []) | ([], _) -> false
  | (fent::frest, atag::arest) ->
     (* Later, this could inform code generation of template types *)
     fent.symtype = atag && match_params frest arest

(** make the type expr result return only the tag for now. Seems
 * easier and I might not need it further down the line. *)
type typeExpr_result = (typetag, string) Stdlib.result

(** Check that a type expression refers to a valid type in the environment. *)
let check_typeExpr tenv (TypeName tyname) =
  match StrMap.find_opt tyname tenv with
  | Some cdata -> Ok ({ tclass=cdata; paramtypes=[]; array=false;
                        nullable=false })
  | None -> Error ("Unknown type " ^ tyname)



(** Expression result type (remember that exprs have a type field) *)
type expr_result = (typetag expr, string located) Stdlib.result

(** Check semantics of an expression, replacing with a type *)
let rec check_expr syms tenv (ex: locinfo expr) : expr_result =
  match ex.e with
  (* The type info in constants is already there...ok I guess *)
  | ExpConst (IntVal i) ->
     Ok {e=ExpConst (IntVal i); decor=int_ttag}
  | ExpConst (FloatVal f) ->
     Ok {e=ExpConst (FloatVal f); decor=float_ttag}
  | ExpConst (BoolVal b) ->
     Ok {e=ExpConst(BoolVal b); decor=bool_ttag}
  | ExpVar s -> (
    match Symtable.findvar_opt s syms with
    | Some (ent, _) -> Ok { e=ExpVar s; decor=ent.symtype }
    | None -> Error {loc=ex.decor; value="Undefined variable " ^ s}
  )
  | ExpBinop (e1, oper, e2) -> (
    match check_expr syms tenv e1 with
    | Ok ({e=_; decor=ty1} as e1) -> (  (* without () e1 is the whole thing *)
      match check_expr syms tenv e2 with
      | Ok ({e=_; decor=ty2} as e2) -> (
         if ty1 <> ty2 then 
           Error {loc=ex.decor;
                  value = ("Operator type mismatch: " ^ typetag_to_string ty1
                           ^ ", " ^ typetag_to_string ty2)}
         else
           match oper with
           | OpEq | OpNe | OpLt | OpGt | OpLe | OpGe ->
              Ok {e=ExpBinop (e1, oper, e2); decor=bool_ttag}
           | OpAnd | OpOr when ty1 <> bool_ttag ->
              if ty1 <> bool_ttag then
                Error {
                    loc=ex.decor;
                    value="Operations && and || only valid for type bool"
                  }
              else
                Ok {e=ExpBinop (e1, oper, e2); decor=bool_ttag}
           | _ ->
              (* TODO: check type interfaces for operation. *)
              Ok {e=ExpBinop (e1, oper, e2); decor=ty1}
      )
      | Error err -> Error err
    )
    | Error err -> Error err
  )

  | ExpUnop (oper, exp) -> (
     match check_expr syms tenv exp with
     | Error err -> Error err
     | Ok ({e=_; decor=ty} as exp) -> (
       match oper with
       | OpNot ->
          if ty <> bool_ttag then
            Error {loc=ex.decor;
                   value="Operation ! only valid for type bool"}
          else
            Ok {e=ExpUnop (oper, exp); decor=ty}
       | _ ->
          (* TODO: check interfaces of ty for operation *)
          Ok {e=ExpUnop (oper, exp); decor=ty}
  ))
       
  | ExpCall (fname, args) -> (
    match check_call syms tenv (fname, args) with
    | Error msg -> Error { loc=ex.decor; value=msg }
    | Ok cexp -> Ok cexp
  )
  | ExpNullAssn _ ->
     Error {loc=ex.decor;
            value="Null-check assignment not allowed in this context"}

(** Procedure call check factored out; it's used for both exprs and stmts. *)
and check_call syms tenv (fname, args) =
  (* recursively check argument exprs and store types in list. *)
  let args_res = List.map (check_expr syms tenv) args in
  (* Concatenate errors from args check and bail out if any *)
  let err_strs =
    List.fold_left (
        fun es res -> match res with
                      | Ok _ -> es
                      | Error {loc=_; value} -> es ^ "\n" ^ value
      ) "" args_res in
  if err_strs <> "" then
    (* check_expr doesn't return a list, so stitch into one. *)
    Error err_strs
  else
    (* could construct these further down... *)
    let args_typed = List.concat_map Result.to_list args_res in
    let argtypes = List.map (fun (ae: typetag expr) -> ae.decor)
                     args_typed in 
    (* find and match procedure *)
    match Symtable.findproc fname syms with
    | Some (proc, _) -> (
      if match_params proc.fparams argtypes then
        Ok {e=ExpCall (fname, args_typed); decor=proc.rettype}
      else
        (* TODO: make it print out the arg list *)
        Error ("Argument match failure for " ^ fname)
    )
    | None -> Error ("Unknown procedure " ^ fname)


(** Check for a redeclaration (name exists at same scope) *)
(* I'm not using this yet...was a candidate for check_stmt *)
let is_redecl varname syms =
  match Symtable.findvar_opt varname syms with
  | None -> false
  | Some (_, scope) -> scope = syms.scopedepth

(** Conditional exprs can have an assignment, so handle it specially. *)
let check_condexp condsyms tenv condexp =
  match condexp.e with
  | ExpNullAssn (decl, varname, ex) -> (
    match check_expr condsyms tenv ex with
    | Error err -> Error err
    | Ok {e=_; decor=ety} as goodex -> (
      (* if a var, add it to the symbol table. 
       * It can't be a redeclaration, it's the first thing in the scope! *)
      if decl then
        (* Caller will hold the modified 'condsyms' node *) 
        Symtable.addvar condsyms {symname=varname; symtype=ety; var=true};
      goodex
  ))
  | _ -> (
     (* Otherwise, it has to be bool *)
     match check_expr condsyms tenv condexp with
     | Error err -> Error err
     | Ok {e=_; decor=ety} as goodex ->
        if ety <> bool_ttag then
          Error {loc=condexp.decor;
                 value=("Conditional expression must have type bool, found"
                        ^ typetag_to_string ety)}
        else
          goodex
  )

(** Mash list of error lists into a single error with list *)
let concat_errors rlist =
  (* the list of errors are each themselves lists. *)
  Error (List.concat (
             List.concat_map (
                 fun r ->match r with
                         | Ok _ -> []
                         | Error erec -> [erec]
               ) rlist
    ))

(* Statements need a pointer back to their symbol table for future
 * traversals, or else I need a way to pick the correct child.
 * Or, I could assume traversal in the same order. *)
(* Exprs never start their own new scope! *)
type stmt_result = ((typetag, st_node) stmt, string located list)
                     Stdlib.result

let rec check_stmt syms tenv (stm: (locinfo, locinfo) stmt) : stmt_result =
  match stm.st with    
    (* Declaration: check for redeclaration, check the exp, make sure
     * types match if declared. *)
  | StmtDecl (v, tyopt, initopt) -> (
    (* Should I factor this logic into a try_add symtable method *)
    match Symtable.findvar_opt v syms with
    | Some (_, scope) when scope = syms.scopedepth ->
       Error [{loc=stm.decor; value="Redeclaration of variable " ^ v}]
    | Some _ | None -> (
      match initopt with
      | None -> (
         match tyopt with
         | None ->
            Error [{loc=stm.decor;
                    value="Var declaration must have type or initializer"}]
         | Some dty ->
            match check_typeExpr tenv dty with
            | Error msg -> Error [{loc=stm.decor; value=msg}] 
            | Ok ttag ->
               Symtable.addvar syms {symname=v; symtype=ttag; var=true};
               (* Add to uninitialized variable set *)
               syms.uninit <- StrSet.add v syms.uninit;
               Ok {st=StmtDecl (v, tyopt, None); decor=syms}
      )                                            
      | Some initexp -> (
        match check_expr syms tenv initexp with
        | Error err -> Error [err]
        | Ok ({e=_; decor=ettag} as e2) -> (
          let tycheck_res = (* I might want more lets to make it cleaner *) 
            match tyopt with
            | Some dty -> (
              match check_typeExpr tenv dty with
              | Ok ttag ->
                 (* May need a more sophisticated comparison here later. *)
                 if ttag = ettag then Ok ttag
                 else
                   Error [{loc=stm.decor;
                           value="Declared type: " ^ typetag_to_string ttag
                                 ^ " for variable " ^ v
                                 ^ " does not match initializer type: "
                                 ^ typetag_to_string ettag}]
              | Error msg -> Error [{loc=stm.decor; value=msg}] )
            | None -> Ok ettag in
          match tycheck_res with
          | Ok ety -> 
             (* syms is mutated, so don't need to return it *)
             Symtable.addvar syms {symname=v; symtype=ety; var=true};
             Ok {st=StmtDecl (v, tyopt, Some e2); decor=syms}
          | Error errs -> Error errs
  ))))

  | StmtAssign (v, e) -> (
     (* Typecheck e, look up v, make sure types match *)
     match check_expr syms tenv e with
     | Error err -> Error [err]
     | Ok ({e=_; decor=ettag} as te) -> ( 
       (* How about object field assignment? See .org for discussion. *)
       match Symtable.findvar_opt v syms with
       | None -> Error [{loc=stm.decor; value="Unknown variable " ^ v}]
       | Some (sym, _) -> (* scope doesn't matter here? *)
          (* Type error is more fundamental, give priority to report it. *)
          if sym.symtype <> ettag then
            Error [{loc=stm.decor;
                    value="Assignment type mismatch: "
                          ^ typetag_to_string sym.symtype ^ " can't store "
                          ^ typetag_to_string ettag}]
          else if sym.var = false then
            Error [{loc=stm.decor;
                    value="Cannot assign to non-var " ^ "v"}]
          else
            Ok {st=StmtAssign (v, te); decor=syms}
  ))

  | StmtReturn eopt -> (
    (* checks that type is return type of the enclosing function, 
     * so check_proc only needs to make sure all paths return. *)
    match syms.in_proc with
    | None ->
       Error [{loc=stm.decor;
               value="Return statement not allowed "
                     ^ "outside of procedure context"}]
    | Some inproc -> (
      match eopt with
      | None -> if inproc.rettype = void_ttag then
                  Ok {st=StmtReturn None; decor=syms}
                else
                  Error [{loc=stm.decor;
                          value="Cannot return void; function return type is "
                                ^ typetag_to_string inproc.rettype}]
      | Some e -> 
         (* have to have optional return type expression for void. *)
         match check_expr syms tenv e with
         | Error err -> Error [err]
         | Ok ({e=_; decor=ettag} as te) -> (
           if ettag <> inproc.rettype then
             Error [{loc=stm.decor;
                     value="Wrong return type "
                           ^ typetag_to_string ettag ^ ", needed "
                           ^ typetag_to_string inproc.rettype}]
           else Ok {st=StmtReturn (Some te); decor=syms}
  )))

  | StmtIf (condexp, thenbody, elsifs, elseopt) -> (
     let condsyms = Symtable.new_scope syms in 
     match check_condexp condsyms tenv condexp with
     | Error err -> Error [err]
     | Ok newcond -> (
       let thensyms = Symtable.new_scope condsyms in
       match check_stmt_seq thensyms tenv thenbody with
       | Error errs -> Error errs
       | Ok newthen -> (
         let elsifs_result = (* this will be a big concat. *)
           let allres =
             List.map (fun (elsifcond, blk) ->
                 let elsifsyms = Symtable.new_scope condsyms in
                 match check_condexp elsifsyms tenv elsifcond with
                 | Error err -> Error [err]
                 | Ok newelsifcond -> (
                   match check_stmt_seq elsifsyms tenv blk with
                   | Error errs -> Error errs
                   | Ok newblk -> Ok (newelsifcond, newblk)
                 ))
               elsifs
           in
           if List.exists Result.is_error allres then
             concat_errors allres
           else
             Ok (List.concat_map Result.to_list allres)
         in
         match elsifs_result with
         | Error errs -> Error errs
         | Ok newelsifs -> (
           (* each block will give an OK, so have to merge those too.*)
           match elseopt with 
           | None -> Ok {st=StmtIf (newcond, newthen, newelsifs, None);
                         decor=thensyms}
           | Some elsebody ->  (* as opposed to somebody else. *)
              let elsesyms = Symtable.new_scope condsyms in
              match check_stmt_seq elsesyms tenv elsebody with
              | Error errs -> Error errs
              | Ok newelse ->
                 Ok {st=StmtIf (newcond, newthen, newelsifs, Some newelse);
                     decor=thensyms}
  ))))

  | StmtWhile (cond, body) -> (
    let condsyms = Symtable.new_scope syms in 
    match check_condexp condsyms tenv cond with
    | Error err -> Error [err]
    | Ok newcond -> (
      let bodysyms = Symtable.new_scope condsyms in
      match check_stmt_seq bodysyms tenv body with
      | Error errs -> Error errs
      | Ok newbody -> Ok {st=StmtWhile (newcond, newbody); decor=bodysyms}
  ))

  | StmtCall ex -> (
     match ex.e with
     | ExpCall (fname, args) -> (
        match check_call syms tenv (fname, args) with
        | Error msg -> Error [{loc=stm.decor; value=msg}]
        | Ok newcallexp -> (
          (* non-void call can't be a standalone statement. *)
          match Symtable.findproc fname syms with
          | None -> failwith "BUG: proc name was previously found OK."
          | Some (entry, _) when entry.rettype <> Types.void_ttag ->
             Error [{loc=stm.decor;
                     value="Non-void return type must be assigned."}]
          | _ -> Ok {st=StmtCall newcallexp; decor=syms}
     ))
     | _ -> failwith "BUG: Call statement with non-call expression"
  )

  | StmtBlock stlist ->
     let blockscope = Symtable.new_scope syms in
     match check_stmt_seq blockscope tenv stlist with
     | Error errs -> Error errs
     | Ok newstmts -> Ok {st=StmtBlock newstmts; decor=blockscope}

(** Check a list of statements. Adds test for unreachable code. *)
and check_stmt_seq syms tenv sseq =
  let rec check' acc stmts = match stmts with
    | [] -> acc
    | stmt::rest -> (
       let res = check_stmt syms tenv stmt in
       match stmt.st with
       | StmtReturn _ when rest <> [] ->
          let unreach = Error [{loc=stmt.decor;
                                value="Unreachable code after return"}] in
          check' (unreach::res::acc) rest
       | _ -> check' (res::acc) rest
    )
  in
  let results = check' [] sseq in
  (* let results = List.map (check_stmt syms tenv) sseq in  *)
  if List.exists Result.is_error results then
    (* Make one error list out of all. Matches stmt_result. *)
    concat_errors results
  else
    (* Make one Ok out of the list of results. NOT a stmt_result. *)
    Ok (List.concat_map Result.to_list results)

(** Determine if a block of statements returns on every path.
  * Return types and unreachable code are checked elsewhere. *)
let rec block_returns stlist =
  (* If I add a break statement, this also has to make sure it doesn't happen
   * before a return. *)
  match stlist with
  | [] -> false 
  | stmt::rest -> (
    match stmt.st with
    | StmtReturn _ -> true
    | StmtDecl _ | StmtAssign _ | StmtCall _ -> block_returns rest
    | StmtBlock slist -> block_returns slist || block_returns rest
    | StmtIf (_, thenblk, elsifs, elsblock) -> (
      (* If all paths return, then OK, else must return after. *)
      match elsblock with
      | None -> block_returns rest
      | Some elsblock -> (
        if block_returns thenblk
           && List.for_all (fun (_, elsif) -> block_returns elsif) elsifs
           && block_returns elsblock then true
        else block_returns rest ))
    | StmtWhile (_, _) ->
       (* While body may never be entered, so can't guarantee *)
       block_returns rest
  )

let check_proc syms tenv pr =
  (* check name for redeclaration *)
  let pdecl = pr.proc.decl.pdecl in 
  match Symtable.findproc pdecl.name syms with
  | Some (_, scope) when syms.scopedepth = scope ->
     Error [{loc=pr.decor; value="Redeclaration of procedure " ^ pdecl.name}]
  | _ -> (
    let argchecks = List.map (fun (_, texp) -> check_typeExpr tenv texp)
                      pdecl.params in
    if List.exists Result.is_error argchecks then
      let errs =
        List.concat_map (
            fun r -> match r with
                     | Ok _ -> []
                     | Error msg -> [{loc=pr.proc.decl.decor; value=msg}]
          ) argchecks
      in Error errs
    else
      let paramentries =
        List.map2 (
            fun (paramname, _) arg ->
            match arg with
            | Error _ -> failwith "Bug: errors in param list should be gone"
            | Ok ttag -> {symname = paramname; symtype=ttag; var=false}
          ) pdecl.params argchecks in
      match check_typeExpr tenv pdecl.rettype with
      | Error msg -> Error [{loc=pr.proc.decl.decor; value=msg}]
      | Ok rttag -> (
        (* Create procedure symtable entry and add to OUTER scope (recursion). *)
        let procentry =
          {procname=pdecl.name; rettype=rttag; fparams=paramentries} in
        Symtable.addproc syms procentry;
        (* create new inner scope pointing to procedure entry, and add args *)
        let procscope = Symtable.new_proc_scope syms procentry in
        List.iter (Symtable.addvar procscope) paramentries;
        let newpdecl = {pdecl=pdecl; decor=procscope} in
        match check_stmt_seq procscope tenv pr.proc.body with
        | Error errs -> Error errs
        | Ok newslist ->
         (* Also need to check that it returns. *) 
          Ok {proc={decl=newpdecl; body=newslist}; decor=procscope}
      ))

let check_module syms tenv (procs, block) = 
  let procres = List.map (check_proc syms tenv) procs in
  if List.exists Result.is_error procres then
    (* check_proc errors are a list of string locateds. *)
    concat_errors procres  (* already wraps in result type *)
  else
    let newprocs = List.concat_map Result.to_list procres in
    match check_stmt_seq syms tenv block with
    | Error errs -> Error errs
    | Ok newblock -> Ok (newprocs, newblock)
