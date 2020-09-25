(** Symbol table definitions (could have different for different phases) *)

open Common
open Types (* as T *)

exception SymbolError of string

(* Types can only be defined at the module level, not nested. *)
(* Start with one global (later per-module) type environment. *)
(* The structure of this also will relate to recursively defined types. *)
type typeenv = classdata StrMap.t

(** Initial type environment (known classes) *)
let base_tenv =
  StrMap.empty
  |> StrMap.add void_class.classname void_class (* defined in Types *)
  |> StrMap.add int_class.classname int_class
  |> StrMap.add float_class.classname float_class
  |> StrMap.add bool_class.classname bool_class

(* Symtable concept: a map for current scope, parent and children nodes *)

(** Symbol table entry type for a variable. *)
type 'addr st_entry = {
    symname: string;
    symtype: typetag;
    (* when I generate code, will I need a (stack or heap) location? *)
    var: bool;  (* "var" semantics means it can be reassigned. OR
                 * mutating methods called? No, they're different *)
    (* may_mut: bool; *)
    addr: 'addr option
    (* instead of an option, how about an "addr decorated" version *)
  }

(** Symbol table entry type for a procedure. *)
type 'addr st_procentry = {
    procname: string;
    rettype: typetag;  (* there's a void typetag *)
    (* could it be just a list of types, no names? but st_entry also
     * has the mutability info, very convenient. *)
    fparams: 'addr st_entry list
  }

(** Symbol table tree node for a single scope *)
type 'addr st_node = {
    scopedepth: int; (* Just keeping the depth should be enough *)
    mutable syms: 'addr st_entry StrMap.t;
    mutable fsyms: 'addr st_procentry StrMap.t;  (* No overloading! *)
    mutable uninit: StrSet.t; (* vars declared but not initted in this scope *)
    mutable parent_init: StrSet.t; (* vars from higher scope that are initted *)
    parent: 'addr st_node option; (* root has no parent *)
    mutable children: 'addr st_node list;
    in_proc: 'addr st_procentry option;
  }

let st_node_to_string node =
  let rec ts' pad nd = 
    pad ^ "{ (" 
    ^ StrMap.fold (fun _ ent s -> ent.symname ^ ", " ^ s) nd.syms ""
    ^ ")\n" ^ pad ^ "  ("
    ^ StrMap.fold (fun _ ent s -> ent.procname ^ ", " ^ s) nd.fsyms ""
    ^ ")\n"
    ^ String.concat "" (List.map (ts' (pad ^ "    ")) nd.children)
    ^ pad ^ "}\n" in
  ts' "" node

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

  (* top-level value can't have unbound type parameter *)
  let make_empty () = {
      scopedepth = 0;
      syms = StrMap.empty;
      (* can have a list of functions for a given name *)
      fsyms = StrMap.empty;
      parent = None;
      parent_init = StrSet.empty;
      in_proc = None;
      (* in_module = modname; *) (* just insert fully qualified name. *)
      children = [];
      uninit = StrSet.empty
    }

  (** Add (variable) symbol to current scope of a node. *)
  let addvar nd symname entry = 
    (* NOTE! This eliminates any previous binding, caller must check first. *)
    nd.syms <- StrMap.add symname entry nd.syms

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
  let addproc nd pname entry =
    match StrMap.find_opt pname nd.fsyms with
    | None ->
       nd.fsyms <- StrMap.add pname entry nd.fsyms
    | Some _ -> (* should be caught by analyzer *)
       raise (SymbolError ("redefinition of procedure \"" ^ entry.procname
                           ^ "\""))

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

  (** Find a procedure by name. Option version for analyzer. *)
  let rec findproc_opt name nd =
    match StrMap.find_opt name nd.fsyms with
    | Some proc -> Some (proc, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findproc_opt name parent
      | None -> None
    )

  let findproc name nd =
    match findproc_opt name nd with
    | Some (entry, depth) -> (entry, depth)
    | None -> raise Not_found

  (** For codegen. Get a proc's symtable entry when it must exist. *)
  let getproc name nd =
    StrMap.find name nd.fsyms

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

  (*
  (** Create  scope for a new module (sets module name) *)
  let new_module_scope nd modname = 
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
    newnode *)
  
  (** Create a scope for a new procedure (sets "in_proc") *)
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

end (* module Symtable *)

