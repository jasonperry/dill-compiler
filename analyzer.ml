(** Semantic analyzer for datlang *)

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
let rec match_params (formal: (string * typetag) list) (actual: typetag list) =
  match (formal, actual) with
  | ([], []) -> true
  | (_, []) | ([], _) -> false
  | ((_, ftag)::frest, atag::arest) ->
     (* Later, this could inform code generation of template types *)
     ftag = atag && match_params frest arest

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
  | ExpConst (FloatVal _) ->
     Ok (redeco_exp ex 
           {tclass=StrMap.find "float" tenv;
            paramtypes=[]; array=false; nullable=false})
  | ExpConst (IntVal _) ->
     Ok (redeco_exp ex
           {tclass=StrMap.find "int" tenv;
            paramtypes=[]; array=false; nullable=false})
  | ExpVar s -> (
    match Symtable.findvar_opt s syms with
    | Some (ent, _) -> Ok (redeco_exp ex ent.symtype)
    | None -> Error {loc=ex.decor; value="Undefined variable " ^ s}
  )
  | ExpBinop (e1, oper, e2) -> (
    (* TODO: check that operation is defined on types *)
    match check_expr syms tenv e1 with
    | Ok ({e=_; decor=ty1} as e1) -> (
      match check_expr syms tenv e2 with
      | Ok ({e=_; decor=ty2} as e2) ->
         if ty1 = ty2 then
           Ok {e=ExpBinop (e1, oper, e2); decor=ty1}
         else
           Error {loc=ex.decor;
                  value = ("Type mismatch: " ^ typetag_to_string ty1
                           ^ ", " ^ typetag_to_string ty2)}
      | Error e -> Error e
    )
    | Error e -> Error e
  )
  | ExpUnop (_, exp) ->
     (* TODO: check if op is allowed on e *)
     check_expr syms tenv exp
  | ExpCall (fname, args) -> (
     (* recursively check argument exprs and store types in list. *)
     let args_res = List.map (check_expr syms tenv) args in
     (* Concatenate errors from args check and bail out if any *)
     let err_strs =
       List.fold_left
         (fun es res -> match res with
                        | Ok _ -> es
                        | Error {loc=_; value} -> es ^ "\n" ^ value
         ) "" args_res in
     if err_strs <> "" then
       (* check_expr doesn't return a list, so stitch into one. *)
       Error { loc=ex.decor; value=err_strs }
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
            Error {loc=ex.decor;
                   value="Argument match failure for " ^ fname} )
       | None -> Error {loc=ex.decor;
                        value="Unknown procedure name " ^ fname}
  )
  | ExpNullAssn _ ->
     Error {loc=ex.decor;
            value="Null-check assignment not allowed in this context"}

(** Check for a redeclaration (name exists at same scope) *)
let is_redecl varname syms =
  match Symtable.findvar_opt varname syms with
  | None -> false
  | Some (_, scope) -> scope = syms.scopedepth

(** Check for special case of assignment expression used in conditionals. *)
let check_assign_expr syms tenv ex =
  match ex.e with
  | ExpNullAssn (decl, varname, ex) -> (
    match check_expr syms tenv ex with
    | Error err -> Error err
    | Ok {e=_; decor=ety} as goodex -> 
      (* if a var, add it to the symbol table. 
       * It can't be a redeclaration, it's the first thing in the scope! *)
      if decl then  (* OCaml has this case? *)
        Symtable.addvar syms {symname=varname; symtype=ety; var=true};
      goodex
  )
  | _ -> failwith "Bug: call to check_assign_expr with wrong expr type"


(* Mash list of errors to a single error with list *)
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
  | StmtDecl (v, tyopt, initexp) -> (
    (* Should I factor this logic into a try_add symtable method *)
    match Symtable.findvar_opt v syms with
    | Some (_, scope) when scope = syms.scopedepth ->
       Error [{loc=stm.decor; value="Redeclaration of variable " ^ v}]
    | Some _ | None -> (
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
                               ^ "does not match initializer type:"
                               ^ typetag_to_string ettag}]
            | Error msg -> Error [{loc=stm.decor; value=msg}] )
          | None -> Ok ettag in
        match tycheck_res with
        | Ok ety -> 
           (* syms is mutated, so don't need to return it *)
           Symtable.addvar syms {symname=v; symtype=ety; var=true};
           Ok {st=StmtDecl (v, tyopt, e2); decor=syms}
        | Error errs -> Error errs
  )))

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
     let thensyms = Symtable.new_scope syms in 
     let condres = match condexp.e with
       (* special case of an assignment expression. May add to the symbol
        * table.*)
       | ExpNullAssn (_, _, _) -> check_assign_expr thensyms tenv condexp
       | _ -> check_expr syms tenv condexp in
     (* don't go on unless condition is good, because it creates scope *)
     (* I guess it's a one-item scope, other blocks inherit from it *)
     match condres with
     | Error err -> Error [err]
     | Ok newcond -> (
       match check_stmt_seq thensyms tenv thenbody with
       | Error errs -> Error errs
       | Ok newthen -> (
         (* Need to make new scope for each of these. *)
         let newelsifs = (* this will be a big concat. *) [] in
         let newelseopt =
           match elseopt with 
           | None -> None
           | Some stmts -> None in
         Ok {st=StmtIf (newcond, newthen, newelsifs, newelseopt);
             decor=syms} (* still the outer symtable node *)
     )))
     (* need to annotate whether it returns? Probably easier to just
      * have a separate block_returns checker. It doesn't need to do anything 
      * deep. *)
  | StmtCall _ -> Error [{loc=stm.decor; value="Call check not implemented"}]
  | StmtBlock _ ->
     (* Will need to create new scope. *)
     Error [{loc=stm.decor; value="Block statement check not implemented"}]

and check_stmt_seq syms tenv sseq =
  let results = List.map (check_stmt syms tenv) sseq in 
  if List.exists Result.is_error results then
    (* If any errors, make one error list out of all. *)
    concat_errors results
  else
    (* Make one Ok out of all the statements. NOT a stmt_result. *)
    Ok (List.concat_map Result.to_list results)
     
  
