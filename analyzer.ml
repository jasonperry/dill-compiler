(** Semantic analyzer: check for errors and build type- and scope- 
  * decorated AST *)

open Types
open Ast
open Symtable1

exception SemanticError of string

(* Analysis pass populates symbol table, including with types. 
 * Hopefully all possibilities of error can be caught in this phase. *)

(* Should I add pointers to the symbol table node for a given scope to the 
 * AST? Maybe, because if I just rely on following, the order matters,
 * Or else you'd need a unique identifier for each child. *)

(** Mash list of error lists into a single error with list *)
let concat_errors rlist =
  (* the list of errors are each themselves lists. *)
  Error (List.concat (
             List.concat_map (
                 fun r -> match r with
                          | Ok _ -> []
                          | Error erec -> [erec]
               ) rlist
    ))

(** Combine all OKs into a single list *)
let concat_ok rlist = List.concat_map Result.to_list rlist

(* TODO: a check_list that does the map and concat error/Ok *)

(** Helper to match a formal with actual parameter list, for
   typechecking procedure calls. *)
let rec match_params (formal: 'a st_entry list) (actual: typetag list) =
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
  | ExpVar varname -> (
    match Symtable.findvar_opt varname syms with
    | Some (ent, _) ->
       if StrSet.mem varname syms.uninit then
         Error {loc=ex.decor;
                value="Variable " ^ varname ^ " may not be initialized"}
       else 
         Ok { e=ExpVar varname; decor=ent.symtype }
    | None -> Error {loc=ex.decor; value="Undefined variable " ^ varname}
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
    let args_typed = concat_ok args_res in
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
  | ExpNullAssn (decl, varname, tyopt, ex) -> (
    match check_expr condsyms tenv ex with
    | Error err -> Error err
    (* TODO: check that expression has option type. *)
    | Ok {e=_; decor=ety} as goodex -> (
      (* if a var, add it to the symbol table. 
       * It can't be a redeclaration, it's the first thing in the scope! *)
      if decl then
        match tyopt with
        | None -> 
           (* Caller will hold the modified 'condsyms' node *) 
           Symtable.addvar condsyms
             {symname=varname; symtype=ety; var=true; addr=None};
           goodex
        | Some tyexp -> (
          match check_typeExpr tenv tyexp with
          | Error msg -> Error {loc=condexp.decor; value=msg}
          | Ok dty when dty <> ety ->
             Error {loc=condexp.decor;
                    value="Declared type: " ^ typetag_to_string dty
                          ^ " for variable " ^ varname
                          ^ " does not match initializer type: "
                          ^ typetag_to_string ety}
          | Ok _ ->
             Symtable.addvar condsyms
               {symname=varname; symtype=ety; var=true; addr=None};
             goodex
        )
      else (
        (* remove assigned variable from uninit'ed set. *)
        condsyms.uninit <- StrSet.remove varname condsyms.uninit;
        goodex
      )
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

(* Statements need a pointer back to their symbol table for future
 * traversals, or else I need a way to pick the correct child.
 * Or, I could assume traversal in the same order. *)
(* Exprs never start their own new scope! *)
type 'a stmt_result = ((typetag, 'a st_node) stmt, string located list)
                     Stdlib.result

let rec check_stmt syms tenv (stm: (locinfo, locinfo) stmt) : 'a stmt_result =
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
               Symtable.addvar syms
                 {symname=v; symtype=ttag; var=true; addr=None};
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
             Symtable.addvar syms
               {symname=v; symtype=ety; var=true; addr=None};
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
       | Some (sym, scope) ->
          (* Type error is more fundamental, give priority to report it. *)
          if sym.symtype <> ettag then
            Error [{loc=stm.decor;
                    value="Assignment type mismatch: "
                          ^ " variable " ^ v ^ " of type " 
                          ^ typetag_to_string sym.symtype ^ " can't store "
                          ^ typetag_to_string ettag}]
          else if sym.var = false then
            Error [{loc=stm.decor;
                    value="Cannot assign to non-var " ^ "v"}]
          else (
            (* remove variable from unitialized set. *)
            syms.uninit <- StrSet.remove v syms.uninit;
            if scope < syms.scopedepth then 
              (* print_string
                ("Initializing variable from parent scope: " ^ v ^ "\n");
               *)
              syms.parent_init <- StrSet.add v syms.parent_init;
            Ok {st=StmtAssign (v, te); decor=syms}
          )
  ))

  | StmtNop -> Ok {st=StmtNop; decor=syms}

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
                     value="Wrong return type: "
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
                   (* return the elsif symbol tables for checking inits. *)
                   | Ok newblk -> Ok ((newelsifcond, newblk), elsifsyms)
                 ))
               elsifs
           in
           if List.exists Result.is_error allres then
             concat_errors allres
           else
             Ok (concat_ok allres)
         in
         match elsifs_result with
         | Error errs -> Error errs
         | Ok elsifres -> (
           let newelsifs = List.map fst elsifres in
           let elsifsyms = List.map snd elsifres in 
           match elseopt with 
           | None -> Ok {st=StmtIf (newcond, newthen, newelsifs, None);
                         decor=thensyms}
           | Some elsebody -> 
              let elsesyms = Symtable.new_scope condsyms in
              match check_stmt_seq elsesyms tenv elsebody with
              | Error errs -> Error errs
              | Ok newelse -> 
                 if not (StrSet.is_empty syms.uninit) then (
                   (* intersect all parent-initted symbols of the blocks. *)
                   let init_ifelse =
                     StrSet.inter thensyms.parent_init elsesyms.parent_init in
                   let initted_by_all =
                     List.fold_left StrSet.inter init_ifelse
                       (List.map (fun nd -> nd.parent_init) elsifsyms) in
                   (* print_string ("Initted by all blocks: "
                                 ^ StrSet.fold (fun v acc -> acc ^ ", " ^ v)
                                     initted_by_all "" ^ "\n"); *)
                   (* remove from uninitialized. *)
                   syms.uninit <-
                     (* It's a right fold. *)
                     StrSet.fold StrSet.remove initted_by_all syms.uninit
                 );
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
    | [] -> List.rev acc
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
    Ok (concat_ok results)

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
    | StmtDecl _ | StmtAssign _ | StmtNop | StmtCall _ -> block_returns rest
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

(** Check a procedure declaration and add it to the given symbol node. *)
let check_pdecl syms tenv pd =
  let pdecl = pd.pdecl in
  (* check name for redeclaration *)
  match Symtable.findproc pdecl.name syms with
  | Some (_, scope) when syms.scopedepth = scope ->
     Error [{loc=pd.decor; value="Redeclaration of procedure " ^ pdecl.name}]
  | _ -> (
    let argchecks = List.map (fun (_, texp) -> check_typeExpr tenv texp)
                      pdecl.params in
    if List.exists Result.is_error argchecks then
      let errs =
        List.concat_map (
            fun r -> match r with
                     | Ok _ -> []
                     | Error msg -> [{loc=pd.decor; value=msg}]
          ) argchecks
      in Error errs
    else
      let paramentries =
        List.map2 (
            fun (paramname, _) arg ->
            match arg with
            | Error _ -> failwith "Bug: errors in param list should be gone"
            | Ok ttag ->
               {symname = paramname; symtype=ttag; var=false; addr=None}
          ) pdecl.params argchecks in
      match check_typeExpr tenv pdecl.rettype with
      | Error msg -> Error [{loc=pd.decor; value=msg}]
      | Ok rttag -> (
        (* Create procedure symtable entry and add to OUTER (module) scope. *)
        let procentry =
          {procname=pdecl.name; rettype=rttag; fparams=paramentries} in
        Symtable.addproc syms procentry;
        (* create new inner scope under the procedure, and add args *)
        let procscope = Symtable.new_proc_scope syms procentry in
        List.iter (Symtable.addvar procscope) paramentries;
        Ok {pdecl=pdecl; decor=procscope}
  ))

(** Check the body of a procedure whose header has already been checked *)
let check_proc tenv (pd: 'addr st_node procdecl) proc =  
  let procscope = pd.decor in
  match check_stmt_seq procscope tenv proc.body with
  | Error errs -> Error errs
  | Ok newslist ->
     (* procedure's decoration is its inner symbol table *)
     (* return check is done afterwards. *)
     Ok {decl=pd; body=newslist; decor=procscope}

let rec is_const_expr = function
    (* if true, I could eval and replace it in the AST. But...
     * what if numerics don't match the target? Let LLVM do it. *)
  | ExpConst _ -> true
  | ExpVar _ -> false (* TODO: check in syms if it's a const *)
  | ExpBinop (e1, _, e2) -> is_const_expr e1.e && is_const_expr e2.e
  | ExpUnop (_, e1) -> is_const_expr e1.e
  | _ -> false

(** Check a global declaration statement (extra constraints) *)
let check_globdecl syms tenv st =
  match st.st with
  | StmtDecl (_, _, initopt) -> (
    match initopt with
    | Some initexp when not (is_const_expr initexp.e) -> 
       Error [{loc=initexp.decor;
               value="Global initializer must be constant expression"}]
    | _ -> (
      match check_stmt syms tenv st with (* catch redecl, type mismatch *)
      | Error errs -> Error errs
      | Ok newstmt -> Ok newstmt
  ))
  | _ -> failwith "BUG: non-decl global should be caught at parsing."
                                        

let check_module syms tenv dmod =
  let globalres = List.map (check_globdecl syms tenv) dmod.globals in
  if List.exists Result.is_error globalres then
    concat_errors globalres
  else
    let newglobals = concat_ok globalres in 
    let pdeclres = List.map (fun proc -> check_pdecl syms tenv proc.decl)
                     dmod.procs in
    if List.exists Result.is_error pdeclres then
      (* check_proc errors are a list of string locateds. *)
      concat_errors pdeclres  (* already wraps in result type *)
    else (
      let newdecls = concat_ok pdeclres in 
      let procres = List.map2 (check_proc tenv) newdecls dmod.procs in
      if List.exists Result.is_error procres then
        concat_errors procres  (* already wraps in result type *)
      else (
        let newprocs = concat_ok procres in
        (* tricky to check that globals are initialized. For now, just
         * make sure they're initted (direclty) in the init block. *)
        let blocksyms = Symtable.new_scope syms in
        (* Oh, I have to let it initialize globals upward, like with if-then *)
        match check_stmt_seq blocksyms tenv dmod.initblock with
        | Error errs -> Error errs
        | Ok newblock ->
           let global_uninit = StrSet.diff syms.uninit blocksyms.parent_init in
           if not (StrSet.is_empty global_uninit) then
             Error (StrSet.fold (fun v strs ->
                        {loc=(List.hd (dmod.globals)).decor; (* fudge the loc *)
                         value="Uninitialized global variable " ^ v ^ "\n"}
                        :: strs) global_uninit [])
           else 
             Ok {name=dmod.name; globals=newglobals; procs=newprocs;
                 initblock=newblock}
  ))
