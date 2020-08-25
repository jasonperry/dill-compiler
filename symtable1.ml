(** Symbol table definitions (could have different for different phases) *)

open Types (* as T *)

exception SymbolError of string

(* Types can only be defined at the module level, not nested. *)
(* Start with one global (later per-module) type environment. *)
(* The structure of this also will relate to recursively defined types. *)
type typeenv = classdata StrMap.t

(** Initial type environment (known classes) *)
let base_tenv =
  StrMap.empty
  |> StrMap.add "void" void_class (* defined in Types *)
  |> StrMap.add "int" int_class
  |> StrMap.add "float" float_class
  |> StrMap.add "bool" bool_class

(* Symtable idea: a map for current scope, parent and children nodes *)
(* how mutable is appropriate? per-scope, it doesn't need to be
 * because it's made from scratch. *)
(* Need to keep a "handle" to the root one *)
(* analyzer functions won't search "down" *)
(* Node has immutable parent pointer and mutable children (child scopes) 
 * list? Functions that create a new scope assign a new list to their scope. *)

(** Symbol table entry type for a variable. *)
type 'a st_entry = {
    symname: string;
    symtype: typetag;
    (* when I generate code, will I need a (stack or heap) location? *)
    var: bool;  (* "var" semantics means it can be reassigned. OR
                 * mutating methods called? *)
    addr: 'a option
  }

(** Symbol table entry type for a procedure. *)
type 'a st_procentry = {
    procname: string;
    rettype: typetag;  (* there's a void typetag *)
    (* could it be just a list of types, no names? but st_entry also
     * has the mutability info, very convenient. *)
    fparams: 'a st_entry list
  }

(** Symbol table node that makes a tree data structure. *)
type 'a st_node = {
    scopedepth: int; (* New idea, just record depth *)
    (* have to make these mutable if I record a new scope under the
     * parent before it's filled. *)
    mutable syms: 'a st_entry StrMap.t;
    mutable fsyms: 'a st_procentry StrMap.t;  (* No overloading! *)
    parent: 'a st_node option; (* root has no parent *)
    mutable parent_init: StrSet.t; (* vars initialized from higher scope *)
    in_proc: 'a st_procentry option;
    mutable children: 'a st_node list;
    mutable uninit: StrSet.t
  }

(** Values and functions for the st_node type. *)
(* module type SYMTABLE = sig
  val make_empty : unit -> 'a st_node
  val addvar : 'a st_node -> 'a st_entry -> unit
  val addproc : 'a st_node -> 'a st_procentry -> unit
  val findvar_opt : string -> 'a st_node -> ('a st_entry * int) option
  val findproc :
    string -> 'a st_node -> ('a st_procentry * int) option
  val new_scope : 'a st_node -> 'a st_node
  val new_proc_scope : 'a st_node -> 'a st_procentry -> 'a st_node
end *)

module Symtable (* : SYMTABLE *) = struct

  (* I ran up against a generalization error when I made this a value *)
  let make_empty () = {
      scopedepth = 0;
      syms = StrMap.empty;
      (* can have a list of functions for a given name *)
      fsyms = StrMap.empty;
      parent = None;
      parent_init = StrSet.empty;
      in_proc = None;
      children = [];
      uninit = StrSet.empty
    }

  (** Add (variable) symbol to current scope of a node. *)
  let addvar nd entry = 
    (* NOTE! This eliminates any previous binding, caller must check first. *)
    nd.syms <- StrMap.add entry.symname entry nd.syms

  (** Set address of existing symbol. *)
  let set_addr nd varname addr =
    (* should only be done for symbols in this scope..fail is a bug *)
    nd.syms <-
      StrMap.update varname
        (function
         | Some entry -> Some { entry with addr=Some addr }
         | None -> failwith ("BUG: Varname " ^ " not found for addr"))
        nd.syms     
  
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

  (* Use this in typechecking. *)
  let rec findvar_opt name nd =
    match StrMap.find_opt name nd.syms with
    | Some entry -> Some (entry, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findvar_opt name parent
      | None -> None
    )

  (* Use this in codegen. *)
  let findvar name nd =
    match findvar_opt name nd with
    | Some ent -> ent
    | None -> raise Not_found

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
        parent_init = StrSet.empty;
        in_proc = nd.in_proc;
        children = [];
        (* No copy constructor so... *)
        uninit = StrSet.union StrSet.empty nd.uninit
      } in
    nd.children <- newnode :: nd.children;
    newnode

  (** Create a scope for a new procedure (sets the procedure context) *)
  let new_proc_scope nd procentry =
    let newnode = {
        scopedepth = nd.scopedepth + 1;
        syms = StrMap.empty;
        fsyms = StrMap.empty;
        parent = Some nd;
        parent_init = StrSet.empty;
        in_proc = Some procentry;
        children = [];
        uninit = StrSet.fold StrSet.add StrSet.empty nd.uninit
      } in
    nd.children <- newnode :: nd.children;
    newnode    

  (* Need new_proc_scope to create a procedure scope. *)

end (* module Symtable *)

