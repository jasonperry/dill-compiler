(** Symbol table definitions (could have different for different phases) *)

open Types

exception SymbolError of string

(* Types can only be defined at the module level, not nested. *)
(* Start with one global (later per-module) type environment. *)
(* The structure of this also will relate to recursively defined types. *)
type typeenv = classdata StrMap.t

(* Symtable idea: a map for current scope, parent and children nodes *)
(* how mutable is appropriate? per-scope, it doesn't need to be
 * because it's made from scratch. *)
(* Need to keep a "handle" to the root one *)
(* analyzer functions won't search "down" *)
(* Node has immutable parent pointer and mutable children (child scopes) 
 * list? Functions that create a new scope assign a new list to their scope. *)

(** Symbol table entry type for a variable. *)
type st_entry = {
    symname: string;
    symtype: typetag;
    (* when I generate code, will I need a (stack or heap) location? *)
    mut: bool  (* think this can be used from here. *)
  }

(** Symbol table entry type for a procedure. *)
type st_procentry = {
    procname: string;
    rettype: typetag;
    fparams: (string * typetag) list
  }

(** Symbol table node that makes a tree data structure. *)
type st_node = {
    scopedepth: int; (* New idea, just record depth *)
    (* have to make these mutable if I record a new scope under the
     * parent before it's filled. *)
    mutable syms: st_entry StrMap.t;
    (* mutable fsyms: (st_procentry list) StrMap.t; *)
    mutable fsyms: st_procentry StrMap.t;
    parent: st_node option; (* root has no parent *)
    mutable children: st_node list
  }

(** Values and functions for the st_node type. *)
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
       (* nd.fsyms <- StrMap.add entry.procname [entry] nd.fsyms *)
       nd.fsyms <- StrMap.add entry.procname entry nd.fsyms
    | Some _ ->
       raise (SymbolError ("redefinition of procedure \"" ^ entry.procname
                          ^ "\""))
       (* nd.fsyms <- StrMap.add entry.procname (entry::plist) nd.fsyms *)
  
  let rec findvar_opt name nd =
    match StrMap.find_opt name nd.syms with
    | Some entry -> Some (entry, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findvar_opt name parent
      | None -> None
    )

  (* 
  (** Find procs matching a name (at a single scope depth only) *)
  let rec findprocs name nd =
    match StrMap.find_opt name nd.fsyms with
    | Some proclist -> (proclist, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findprocs name parent
      | None -> ([], 0)
    ) *)

  (** Find a procedure by name. Should it raise instead? *)
  let rec findproc name nd =
    match StrMap.find_opt name nd.fsyms with
    | Some proc -> Some (proc, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findproc name parent
      | None -> None
    )

  (** Create a new nested scope node and return it. *)
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

