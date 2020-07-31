(** Semantic analyzer for datlang *)

open Types
open Ast

(* decorated AST structures *)
exception SemanticError of string

(* BUT I only want types to be defined at the module level, not nested!
 * (at least not mor deeply.) *)
(* I could have the same structure, just don't spawn children as often.
 * Or I could just start with one global map. *)
(* Though I should probably have some idea of modules early on. *)
(* The structure of this also will relate to recursively defined types. *)
type typeenv = classdata StrMap.t
let base_tenv =
  StrMap.empty
  |> StrMap.add "int" { classname="int"; mut=false; params=[];
                        implements=[] } (* later: "Arith" *)
  |> StrMap.add "float" { classname="int"; mut=false; params=[];
                          implements=[] }

let typetag_to_string tt =
  tt.tclass.classname
  ^ List.fold_left
      (fun s (_, vval) ->
        s ^ "<" ^ vval ^ "> "
      ) "" tt.paramtypes
(* Symtable idea: a map for current scope, parent and children nodes *)
(* how mutable is appropriate? per-scope, it doesn't need to be
 * because it's made from scratch. *)
(* Need to keep a "handle" to the root one *)
(* analyzer functions won't search "down" *)
(* Node has immutable parent pointer and mutable children (child scopes) 
 * list? Functions that create a new scope assign a new list to their scope. *)

type st_entry = {
    symname: string;
    symtype: typetag;
    (* when I generate code, will I need a (stack or heap) location? *)
    mut: bool  (* think this can be used from here. *)
  }

type st_procentry = {
    procname: string;
    rettype: typetag;
    fparams: (string * typetag) list
  }

(** Match a formal with actual parameter list, for typechecking procedure
  * calls. *)
let rec match_params (formal: (string * typetag) list) (actual: typetag list) =
  match (formal, actual) with
  | ([], []) -> true
  | (_, []) | ([], _) -> false
  | ((_, ftag)::frest, atag::arest) ->
     ftag = atag && match_params frest arest

(** Symbol table node that makes a tree data structure. *)
type st_node = {
    scopedepth: int; (* New idea, just record depth *)
    (* have to make these mutable if I record a new scope under the
     * parent before it's filled. *)
    mutable syms: st_entry StrMap.t;
    mutable fsyms: (st_procentry list) StrMap.t;
    parent: st_node option; (* root has no parent *)
    mutable children: st_node list
  }

module Symtable = struct
  
  let empty: st_node = {
      scopedepth = 0;
      syms = StrMap.empty;
      (* can have a list of functions for a given name *)
      fsyms = StrMap.empty;
      parent = None;
      children = []
    }

  (** Add (variable) symbol to current scope of a node. *)
  let addvar nd (entry: st_entry) = 
    (* NOTE! This eliminates any previous binding, caller must check first. *)
    nd.syms <- StrMap.add entry.symname entry nd.syms

  (** Add procedure to current scope of a node. *)
  let addproc nd entry =
    match StrMap.find_opt entry.procname nd.fsyms with
    | None ->
       nd.fsyms <- StrMap.add entry.procname [entry] nd.fsyms
    | Some plist ->
       nd.fsyms <- StrMap.add entry.procname (entry::plist) nd.fsyms
  
  let rec findvar_opt name nd =
    match StrMap.find_opt name nd.syms with
    | Some entry -> Some (entry, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findvar_opt name parent
      | None -> None
    )

  let rec findprocs name nd =
    match StrMap.find_opt name nd.fsyms with
    | Some proclist -> (proclist, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findprocs name parent
      | None -> ([], 0)
    )
  
  let new_scope nd =
    let newnode = {
        scopedepth = nd.scopedepth + 1;
        syms = StrMap.empty;
        fsyms = StrMap.empty;
        parent = Some nd;
        children = []
      } in
    nd.children <- newnode :: nd.children;
    newnode

end (* module Symtable *)

(* later just make this in the top-level analyzer function *)
let root_st = Symtable.empty 

(* Analysis pass populates symbol table, including with types. 
 * Hopefully all possibilities of error can be caught in this phase. *)

(* type checked_node =
  | E of expr * typetag
  | S of stmt (* no, the stmt has to have checked sub-exprs *)
  | P of proc *)

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
     let res = List.map (check_exp syms tenv) args in
     (* Concatenate errors and bail out if any *)
     let errs =
       List.fold_left
         (fun es res -> match res with
                        | Ok _ -> es
                        | Error m -> es ^ "\n" ^ m
         ) "" res in
     if errs <> "" then
       Error errs
     else
       (* look up functions *)
       let (procs, _) = Symtable.findprocs fname syms in
       (* get argument types (no errors if this far *)
       let argtypes =
         List.concat_map
           (fun res -> match res with
                       | Ok (_, ty) -> [ty]
                       | Error _ -> []
           ) res in
       (* search for matching argument list *)
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

        
     
