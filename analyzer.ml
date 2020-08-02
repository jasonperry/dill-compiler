(** Semantic analyzer for datlang *)

open Types
open Ast
open Symtable1

exception SemanticError of string


(** Initial symbol table *)
(* later just make this in the top-level analyzer function *)
let root_st = Symtable.empty 

(** Initial type environment *)
let base_tenv =
  StrMap.empty
  |> StrMap.add "int" { classname="int"; mut=false; params=[];
                        implements=[] } (* later: "Arith" *)
  |> StrMap.add "float" { classname="int"; mut=false; params=[];
                          implements=[] }


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

type expr_result = ((expr * typetag), string) Stdlib.result

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
    | None -> Error ("Undefined variable " ^ s)
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
           Error ("Type mismatch: " ^ typetag_to_string ty1
                ^ ", " ^ typetag_to_string ty2)
      | Error m -> Error m 
    )
    | Error m -> Error m
  )
  | ExpUnop (_, e) ->
     (* TODO: check if op is allowed on e *)
     check_exp syms tenv e
  | ExpCall (fname, args) ->
     (* recursively typecheck argument expressions and store types in list. *)
     let args_checked = List.map (check_exp syms tenv) args in
     (* Concatenate errors from args check and bail out if any *)
     let errs =
       List.fold_left
         (fun es res -> match res with
                        | Ok _ -> es
                        | Error m -> es ^ "\n" ^ m
         ) "" args_checked in
     if errs <> "" then
       Error errs
     else
       (* get all procs with matching name *)
       let (procs, _) = Symtable.findprocs fname syms in
       (* get argument types (no errors if this far *)
       let argtypes =
         List.concat_map
           (fun res -> match res with
                       | Ok (_, ty) -> [ty]
                       | Error _ -> []
           ) args_checked in
       (* search for a proc with matching argument list *)
       let rec searchmatch proclist =
         match proclist with
         | [] -> Error ("No matching signature for procedure " ^ fname)
         | p :: rest -> (
            if match_params p.fparams argtypes then
              Ok (e, p.rettype)
            else
              searchmatch rest
         )
       in
       if procs = [] then
         Error ("Unknown procedure name " ^ fname)
       else
         searchmatch procs
       (* Do I need to save the types of the argument expressions? *)

        
     
