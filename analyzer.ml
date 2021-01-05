(** Semantic analyzer: check for errors and build type- and symbol- 
  * decorated AST *)

open Common
open Types
open Ast
open Symtable1

exception SemanticError of string

(* Analysis pass populates symbol table, including with types. 
 * Hopefully all possibilities of error can be caught in this phase. *)

(* Should I add pointers to the symbol table node for a given scope to the 
 * AST? Maybe, because if I just rely on following, the order matters,
 * Or else you'd need a unique identifier for each child. *)

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

(** Check that a type expression refers to a valid type in the environment, 
    and return the tag. *)
let check_typeExpr tenv texp : (typetag, string) result =
  match StrMap.find_opt texp.classname tenv with
  | Some cdata -> Ok ({ modulename = cdata.in_module;
                        typename = cdata.classname;
                        paramtypes=[]; array=false; nullable=false })
  | None -> Error ("Unknown type " ^ typeExpr_to_string texp)


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
  | ExpVar (varname, fields) -> (
    match Symtable.findvar_opt varname syms with
    | Some (ent, _) ->
       if StrSet.mem varname syms.uninit then
         Error {loc=ex.decor;
                value="Variable " ^ varname ^ " may not be initialized"}
       else 
         Ok { e=ExpVar (varname, fields); decor=ent.symtype }
    | None -> Error {loc=ex.decor; value="Undefined variable " ^ varname}
  )
  | ExpRecord _ -> failwith "Record exp typechecking not implemented"
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
    match Symtable.findproc_opt fname syms with
    | Some (proc, _) -> (
      if match_params proc.fparams argtypes then
        Ok {e=ExpCall (fname, args_typed); decor=proc.rettype}
      else
        (* TODO: make it print out the arg list *)
        Error ("Argument match failure for " ^ fname)
    )
    | None -> Error ("Unknown procedure name: " ^ fname)

(** Check that a record expression matches the given type. *)
let rec check_recExpr syms (tenv: classData StrMap.t)
          (ttag: typetag) (rexp: locinfo expr) = match rexp.e with
  | ExpRecord flist ->
     let cdata = StrMap.find ttag.typename tenv in
     (* make a map from the fields to their types. *)
     let fdict = List.fold_left (fun s (fi: fieldInfo) ->
                     StrMap.add fi.fieldname fi.fieldtype s)
                   StrMap.empty
                   cdata.fields in
     (* check field types, recursively removing from the map. *)
     let rec check_fields
               (flist: (string * locinfo expr) list)
               (accdict: typetag StrMap.t)
               (accfields: (string * typetag expr) list) = match flist with
       | [] ->
          if StrMap.is_empty accdict
          then Ok {e=ExpRecord accfields; decor=ttag}
          else Error {
                   loc=rexp.decor;
                   value=("Undefined record field "
                          ^ fst (StrMap.choose accdict))}
       | (fname, fexp)::rest ->
          let ftype = StrMap.find fname accdict in
          (* recurse if it's a recExpr *)
          let res = match fexp.e with
            | ExpRecord _ -> check_recExpr syms tenv ftype fexp
            | _ -> check_expr syms tenv fexp in
          match res with 
          | Error err -> Error err
          | Ok eres ->
             if eres.decor = ftype
             then check_fields rest
                    (StrMap.remove fname accdict) ((fname,eres)::accfields)
             else Error {
                      loc=rexp.decor;
                      value=("Field type mismatch: got "
                             ^ typetag_to_string eres.decor ^ ", needed "
                             ^ typetag_to_string ftype)}
     in
     check_fields flist fdict []
  | _ -> failwith "BUG: check_recExpr called with non-record variant"


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
           Symtable.addvar condsyms varname
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
             Symtable.addvar condsyms varname
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
      match initopt with (* TODO: fix for record init (needs typeExp) *)
      | None -> (
         match tyopt with
         | None ->
            Error [{loc=stm.decor;
                    value="Var declaration must have type or initializer"}]
         | Some dty ->
            match check_typeExpr tenv dty with
            | Error msg -> Error [{loc=stm.decor; value=msg}] 
            | Ok ttag ->
               (* TODO: add nested scope for fields if the type has them. *)
               (* Cheat idea: just add "var.field" symbols *)
               Symtable.addvar syms v
                 {symname=v; symtype=ttag; var=true; addr=None};
               (* add symtable entries for record fields, if any. *)
               let rec add_field_sym v (finfo: fieldInfo) =
                 let varstr = v ^ "." ^ finfo.fieldname in
                 Symtable.addvar syms varstr
                   {symname=varstr; symtype=finfo.fieldtype;
                    var=finfo.mut; addr=None};
                 (* recursively add fields-of-fields *)
                 let cdata = StrMap.find finfo.fieldtype.typename tenv in 
                 List.iter (add_field_sym varstr) cdata.fields
               in 
               let the_classdata = StrMap.find ttag.typename tenv in
               List.iter (add_field_sym v) the_classdata.fields;
               (* Add to uninitialized variable set *)
               syms.uninit <- StrSet.add v syms.uninit;
               Ok {st=StmtDecl (v, tyopt, None); decor=syms}
      )
      | Some initexp -> (
        (* TODO: call check_recExpr if it's a record type and should be good! *)
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
             Symtable.addvar syms v
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
                    value="Assignment to immutable var/field " ^ v}]
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
             Error (concat_errors allres)
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
          match Symtable.findproc_opt fname syms with
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
    Error (concat_errors results)
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
let check_pdecl syms tenv modname (pdecl: 'loc procdecl) =
  (* check name for redeclaration *)
  match Symtable.findproc_opt pdecl.name syms with
  | Some (_, scope) when syms.scopedepth = scope ->
     Error [{loc=pdecl.decor; value="Redeclaration of procedure " ^ pdecl.name}]
  | _ -> (
    (* Typecheck arguments *)
    let argchecks = List.map (fun (_, texp) -> check_typeExpr tenv texp)
                      pdecl.params in
    if List.exists Result.is_error argchecks then
      let errs =
        concat_map (
            fun r -> match r with
                     | Ok _ -> []
                     | Error msg -> [{loc=pdecl.decor; value=msg}]
          ) argchecks
      in Error errs
    else
      (* Create symbol table entries for params *)
      let paramentries =
        List.map2 (
            fun (paramname, _) arg ->
            match arg with
            | Error _ -> failwith "Bug: errors in param list should be gone"
            | Ok ttag ->
               {symname = paramname; symtype=ttag; var=false; addr=None}
          ) pdecl.params argchecks in
      (* Typecheck return type. *)
      match check_typeExpr tenv pdecl.rettype with
      | Error msg -> Error [{loc=pdecl.decor; value=msg}]
      | Ok rttag -> (
        (* Create procedure symtable entry.
         * Don't add it to module symbtable node here; caller does it. *)
        let procentry =
          {procname=(if not pdecl.export then modname ^ "." else "")
                    ^ pdecl.name;
           rettype=rttag; fparams=paramentries} in
        (* create new inner scope under the procedure, and add args *)
        (* Woops, it creates a "dangling" scope if proc isn't defined *)
        let procscope = Symtable.new_proc_scope syms procentry in
        (* Should I add the proc to its own symbol table? Don't see why. *)
        (* Did I do this so codegen for recursive calls "just works"? *)
        Symtable.addproc procscope pdecl.name procentry;
        List.iter (fun param -> Symtable.addvar procscope param.symname param)
          paramentries;
        Ok ({name=pdecl.name; params=pdecl.params;
             rettype=pdecl.rettype; export=pdecl.export; decor=procscope},
            procentry)
  ))


(** Check the body of a procedure whose header has already been checked 
  * (and added to the symbol table) *)
let check_proc tenv (pdecl: 'addr st_node procdecl) proc =  
  let procscope = pdecl.decor in
  match check_stmt_seq procscope tenv proc.body with
  | Error errs -> Error errs
  | Ok newslist ->
     (* procedure's decoration is its inner symbol table *)
     (* return check is done afterwards. No it's not, what's up? *)
     let rettype = (Symtable.getproc pdecl.name procscope).rettype in
     if rettype <> void_ttag && not (block_returns proc.body) then 
       Error [{loc=proc.decor;
               value="Non-void procedure " ^ pdecl.name
                     ^ " may not return a value"}]
     else
       Ok {decl=pdecl; body=newslist; decor=procscope}


let rec is_const_expr = function
    (* if true, I could eval and replace it in the AST. But...
     * what if numerics don't match the target? Let LLVM do it. *)
  | ExpConst _ -> true
  | ExpVar (_,_) -> false (* TODO: check in syms if it's a const *)
  | ExpBinop (e1, _, e2) -> is_const_expr e1.e && is_const_expr e2.e
  | ExpUnop (_, e1) -> is_const_expr e1.e
  | _ -> false


(** Check a global declaration statement (needs const initializer) *)
let check_globdecl syms tenv gstmt =
  match gstmt.init with
  | Some initexp when not (is_const_expr initexp.e) ->
     (* TODO: allow non-constant initializer (and generate code for it.) *)
     Error [{loc=initexp.decor;
             value="Global initializer must be constant expression"}]
  | Some _ -> (  
    (* Cheat a little: reconstruct a stmt so I can use check_stmt.
     * It should catch redeclaration and type mismatch errors. 
     * Seems nicer than having the check logic in two places. *)
    match check_stmt syms tenv
            {st=StmtDecl (gstmt.varname, gstmt.typeexp, gstmt.init);
             decor=gstmt.decor} with
    | Error errs -> Error errs
    | Ok {st=dst; decor=dc} -> (
      match dst with
      | StmtDecl (v, topt, eopt) ->
         Ok {varname=v; typeexp=topt; init=eopt; decor=dc}
      | _ -> failwith "BUG: checking StmtDecl didn't return StmtDecl"
  ))
  | None -> Error [{loc=gstmt.decor;
                    value="Globals must be initialized when declared"}]


(** Check imported module specs and add global var & proc symbols. *)
let add_imports syms tenv specs istmts = 
  (* Should I make types global? No, let them be parameterized also *)
  (* Even if you open a module, you should remember which module the 
   * function came from, for error messages *)
  (* In other words, as vars have in_proc, funcs should have in_module. 
   * But wouldn't (global) variables need it too? *)
  (* Maybe vars can have a 'parent_struct' that could either be a 
     proc or a type or a module. *) 
  let add_import istmt = 
    let (modname, prefix) = match istmt with
      | Using (modname, aliasopt) -> (
        match aliasopt with
        | Some alias -> (modname, alias ^ ".")
        | None -> (modname, modname ^ "." ) )
      | Open modname -> (modname, "") in
    let the_spec = StrMap.find modname specs in
    (* Iterate over global variable declarations and add those *)
    List.map (
        fun (gdecl: 'st globaldecl) ->
        let refname = prefix ^ gdecl.varname in
        let fullname = modname ^ "." ^ gdecl.varname in
        match check_typeExpr tenv gdecl.typeexp with
          | Error msg ->
             (* Yes, this is where modspecs get semantically checked. *)
             Error [{value=msg; loc=gdecl.decor}] 
          | Ok ttag -> (
            match Symtable.findvar_opt refname syms with
            | Some (_, _) ->
               Error [{value=("Duplicated extern variable " ^ refname);
                       loc=gdecl.decor}]
            | None ->
               let entry = {
                   symname = fullname; symtype = ttag; 
                   var = true; addr = None
                 } in
               Symtable.addvar syms refname entry;
               if refname <> fullname then
                 Symtable.addvar syms fullname entry;
               Ok syms (* doesn't get used *)
      )) the_spec.globals
    (* iterate over procedure declarations and add those. *)
    @ (List.map (
           fun (pdecl: 'sd procdecl) ->
           let refname = prefix ^ pdecl.name in
           let fullname = modname ^ "." ^ pdecl.name in
           (* check_pdecl now gets module name prefix from AST. *)
           match check_pdecl syms tenv modname pdecl 
           (* { pdecl with name=(prefix ^ pdecl.name) } *) with
           | Ok (_, entry) ->
              print_string ("Adding imported proc symbol: " ^ refname ^ "\n");
              Symtable.addproc syms refname entry;
              if refname <> fullname then 
                Symtable.addproc syms fullname entry;
              Ok syms
           | Error errs -> Error errs
         ) the_spec.procdecls
      ) (* end add_import *)
  in
  match concat_errors (concat_map add_import istmts) with
  | [] -> Ok syms
  | errs -> Error errs


(** Check a struct declaration, generating classData for the tenv. *)
let check_typedef modname tenv (tydef: locinfo typedef) = 
  (* TODO: handle recursive type declarations *)
  match tydef with
  | Struct sdecl ->
     (* check for nonexistent types, field redecl *)
     let rec check_fields flist acc = match flist with
       | [] -> Ok (List.rev acc)
       | fdecl :: rest ->
          match check_typeExpr tenv fdecl.fieldtype with
          | Error e ->
             Error [{loc=fdecl.decor; (* Maybe don't need this prefix *)
                     value="Field type error: " ^ e}]
          | Ok ttag -> 
          (* match StrMap.find_opt fdecl.fieldtype.classname tenv with
          | None ->
             if fdecl.fieldtype.classname = sdecl.typename then
               Error [{ loc=fdecl.decor;
                        value="Recursively defined types not implemented: "
                              ^ typeExpr_to_string fdecl.fieldtype }]
             else
               Error [{ loc=fdecl.decor;
                      value="Undeclared field type " ^
                              typeExpr_to_string fdecl.fieldtype }]
          | Some fclass -> *)
             if List.exists (fun (fi : fieldInfo) ->
                    fi.fieldname = fdecl.fieldname) acc then
               Error [{ loc=fdecl.decor;
                        value="Field redeclaration " ^ fdecl.fieldname }]
             else 
               let finfo =
                 {fieldname=fdecl.fieldname; priv=fdecl.priv;
                  mut=fdecl.mut;
                  fieldtype = ttag
                 }
               in check_fields rest (finfo::acc)
     in
     match check_fields sdecl.fields [] with
     | Error e -> Error e
     | Ok flist -> Ok
        {
          classname = sdecl.typename;
          in_module = modname;
          muttype = List.exists (fun fdecl -> fdecl.mut) sdecl.fields;
          params = [];
          implements = [];
          (* later can generate field info with same type variables as outer *)
          fields = flist
        }

(** Check one entire module, generating new versions of each component. *)
let check_module syms tenv ispecs (dmod: ('ed, 'sd) dillmodule) =
  (* Check import statements and load modspecs into symtable
     (they've been loaded from .dms files by the top level) *)
  match add_imports syms tenv ispecs dmod.imports with
  | Error errs -> Error errs 
  | Ok syms -> (  (* It's the same symtable node that's passed in... *)
    (* Add new scope so imports will be topmost in the module scope. *)
    let syms = Symtable.new_scope syms in
    (* create tenv entry (classdata) for a struct declaration *)
    (* fold typedefs into new type environment. *)
    let typesrlist = List.map (check_typedef dmod.name tenv) dmod.typedefs in
    if List.exists Result.is_error typesrlist then
      Error (concat_errors typesrlist)
    else 
      let tenv = List.fold_left
                   (fun map (cdata: classData) ->
                     StrMap.add cdata.classname cdata map)
                   tenv (concat_ok typesrlist) in
      (* spam syms into the decor of the struct, not that it will
         be needed...maybe delete typedefs from the second AST
         and turn the methods into just functions? *) 
      let newtypedefs = List.map (fun td ->
                            match td with
                            | Struct sdecl ->
                               let newfields = List.map (fun fd ->
                                                   {fd with decor=syms})
                                                 sdecl.fields in
                               Struct {sdecl with fields=newfields})
                          dmod.typedefs in
      (* Check global declarations *)
      let globalsrlist = List.map (check_globdecl syms tenv) dmod.globals in
      if List.exists Result.is_error globalsrlist then
        Error (concat_errors globalsrlist)
      else
        let newglobals = concat_ok globalsrlist in
        (* Check procedure decls first, to add to symbol table *)
        let pdeclsrlist = List.map (fun proc ->
                              check_pdecl syms tenv dmod.name proc.decl)
                            dmod.procs in
        if List.exists Result.is_error pdeclsrlist then
          Error (concat_errors pdeclsrlist)
        else
          let newpdecls = 
            List.map (fun ((pd: 'a st_node procdecl), pentry) ->
                Symtable.addproc syms pd.name pentry;
                pd) 
              (concat_ok pdeclsrlist) in
          (* Check procedure bodies *)
          let procsrlist = List.map2 (check_proc tenv) newpdecls dmod.procs in
          if List.exists Result.is_error procsrlist then
            Error (concat_errors procsrlist)
          else
            let newprocs = concat_ok procsrlist in
            (* Made it this far, assemble the newly-decorated module. *)
            Ok {name=dmod.name; imports=dmod.imports;
                typedefs=newtypedefs;
                globals=newglobals; procs=newprocs
              }
  )

(** Auto-generate the interface object for a module, to be serialized. *)
let create_module_spec (the_mod: (typetag, 'a st_node) dillmodule) =
  {
    name = the_mod.name;
    imports = List.map (function
                  | Using (mn, alias) -> Using (mn, alias)
                  | Open mn -> Using (mn, None)) the_mod.imports;
    (* I want to make all names fully qualified in the spec file. *)
    (* Idea: keep a map of module name->symtable and "open" symbol->module *)
    (* but anyway, do types need to remember which module they're defined in?
     * then I can easily produce the unqual. name of any type. 
     * Same for symtable entries for procs. *)
    typedefs = the_mod.typedefs;
    globals =
      List.map (fun gdecl ->
          { decor = gdecl.decor;
            varname = gdecl.varname;
            typeexp = 
              (* regenerate a typeExpr from symtable type *)
              let vttag =
                (fst (Symtable.findvar gdecl.varname gdecl.decor)).symtype in
              { modname = Some (vttag.modulename);
                classname = vttag.typename }
          }
        ) the_mod.globals;
    procdecls =
      List.map (fun proc -> proc.decl) the_mod.procs
  }
