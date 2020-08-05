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
  | Some cdata -> Ok ({ tclass=cdata; paramtypes=[]; array=false })
  | None -> Error ("Unknown type " ^ tyname)

type expr_result = ((expr * typetag), string located) Stdlib.result

let rec check_exp syms (tenv: typeenv) (e: expr) =
  match e.value.e with
  (* The type info in constants is already there...ok I guess *)
  | ExpConst (FloatVal _) ->
     Ok (e, {tclass = StrMap.find "float" tenv;
             paramtypes = []; array = false} )
  | ExpConst (IntVal _) ->
     Ok (e, {tclass = StrMap.find "int" tenv;
             paramtypes = []; array = false} )
  | ExpVar s -> (
    match Symtable.findvar_opt s syms with
    | Some (ent, _) -> Ok (e, ent.symtype)
    | None -> Error {loc=e.loc; value="Undefined variable " ^ s}
  )
  | ExpBinop (e1, _, e2) -> (
    (* TODO: check that operation is defined on types *)
    match check_exp syms tenv e1 with
    | Ok (_, ty1) -> (
      match check_exp syms tenv e2 with
      | Ok (_, ty2) ->
         if ty1 = ty2 then
           Ok (e, ty1)
         else
           Error {loc=e.loc;
                  value = ("Type mismatch: " ^ typetag_to_string ty1
                           ^ ", " ^ typetag_to_string ty2)}
      | Error e -> Error e
    )
    | Error e -> Error e
  )
  | ExpUnop (_, exp) ->
     (* TODO: check if op is allowed on e *)
     check_exp syms tenv exp
  | ExpCall (fname, args) ->
     (* recursively typecheck argument expressions and store types in list. *)
     let args_checked = List.map (check_exp syms tenv) args in
     (* Concatenate errors from args check and bail out if any *)
     let err_strs =
       List.fold_left
         (fun es res -> match res with
                        | Ok _ -> es
                        | Error {loc=_; value} -> es ^ "\n" ^ value
         ) "" args_checked in
     if err_strs <> "" then
       Error { loc=e.loc; value=err_strs }
     else
       (* Hard to make a one-liner since I'm also picking out just the snd *)
       let argtypes =
         List.concat_map
           (fun res -> match res with
                       | Ok (_, ty) -> [ty]
                       | Error _ -> []
           ) args_checked in
       (* find and match procedure *)
       match Symtable.findproc fname syms with
       | Some (pe, _) -> (
          if match_params pe.fparams argtypes then
            Ok (e, pe.rettype)
          else
            (* TODO: make it print out the arg list *)
            Error {loc=e.loc; value="Argument match failure for " ^ fname} )
       | None -> Error {loc=e.loc; value="Unknown procedure name " ^ fname}


type stmt_result = ((stmt * st_node), string located) Stdlib.result

let check_stmt syms (tenv: typeenv) (st: stmt) =
  match st.value with
    
    (* Declaration: check for redeclaration, check the exp, make sure
     * types match if declared. *)
  | StmtDecl (v, tyopt, initexp) -> (
    match Symtable.findvar_opt v syms with
    | Some (_, scope) when scope = syms.scopedepth ->
       Error {loc=st.loc; value="Redeclaration of variable " ^ v}
    | Some _ | None -> (
      match check_exp syms tenv initexp with
      | Error err -> Error err
      | Ok (e2, ettag) -> (
        let tycheck_res = (* I might want more lets to make it cleaner *) 
          match tyopt with
          | Some dty -> (
            match check_typeExpr tenv dty with
            | Ok ttag ->
               (* May need a more sophisticated comparison here later. *)
               if ttag = ettag then Ok ttag
               else
                 Error ("Declared type: " ^ typetag_to_string ttag
                        ^ " for variable " ^ v
                        ^ "does not match initializer type:"
                        ^ typetag_to_string ettag)
            | Error msg -> Error msg )
          | None -> Ok ettag in
        match tycheck_res with
        | Ok ety -> 
           (* syms is mutated, so don't need to return it *)
           Symtable.addvar syms { symname=v; symtype=ety; var=true };
           Ok ({loc=st.loc; value=StmtDecl (v, tyopt, e2)}, syms)
        | Error msg -> Error {loc=st.loc; value=msg}
  )))

  | StmtAssign (v, e) -> (
     (* Typecheck e, look up v, make sure types match *)
     match check_exp syms tenv e with
     | Error err -> Error err  (* error branch is same for stmt and exp *)
     | Ok (e, ettag) -> ( (* want to shadow e with new version. *)
       (* How about object field assignment? See .org for discussion. *)
       match Symtable.findvar_opt v syms with
       | None -> Error {loc=st.loc; value="Unknown variable " ^ v}
       | Some (sym, _) -> (* scope doesn't matter here? *)
          (* Type error is more fundamental, give priority to report it. *)
          if sym.symtype <> ettag then
            Error {loc=st.loc;
                   value="Assignment type mismatch: "
                         ^ typetag_to_string sym.symtype ^ " can't store "
                         ^ typetag_to_string ettag}
          else if sym.var = false then
            Error {loc=st.loc;
                   value="Cannot assign to non-var " ^ "v"}
          else
            Ok ({loc=st.loc; value=StmtAssign (v, e)}, syms)
  ))

  | StmtReturn eopt -> (
    match syms.in_proc with
    | None ->
       Error {loc=st.loc;
              value="Return statement not allowed "
                    ^ "outside of procedure context"}
    | Some inproc -> (
      match eopt with
      | None -> if inproc.rettype = void_ttag then
                  Ok ({loc=st.loc; value=StmtReturn eopt}, syms)
                else
                  Error {loc=st.loc;
                         value="Cannot return void; function return type is "
                               ^ typetag_to_string inproc.rettype}
      | Some e -> 
         (* have to have optional return type expression for void. *)
         match check_exp syms tenv e with
         | Error err -> Error err
         | Ok (e, ettag) -> (
           if ettag <> inproc.rettype then
             Error {loc=st.loc;
                    value="Wrong return type "
                          ^ typetag_to_string ettag ^ ", needed "
                          ^ typetag_to_string inproc.rettype}
           else Ok({loc=st.loc; value=StmtReturn (Some e)}, syms)
  )))
     (* have to check if type is return type of enclosing function *)
     (* then check_proc will only need to make sure all paths return. Yay! *)
  | StmtIf _ -> Error {loc=st.loc; value="If check not implemented"}
  | StmtCall _ -> Error {loc=st.loc; value="Call check not implemented"}


