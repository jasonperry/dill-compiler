(** Symbol table definitions (could have different for different phases) *)

open Common
open Types (* as T *)

exception SymbolError of string

(* Types can only be defined at the module level, not nested. *)
(* Start with one global (later per-module) type environment. *)
(* The structure of this also will relate to recursively defined types. *)
type typeenv = classData PairMap.t

(** Initial type environment (primitive types) *)
let base_tenv =
  (* Maybe put this in the types module. *)
  PairMap.empty
  (* Maybe just add the string name for the scope *)
  |> PairMap.add ("", void_class.classname) void_class
  |> PairMap.add ("", int_class.classname) int_class
  |> PairMap.add ("", float_class.classname) float_class
  |> PairMap.add ("", byte_class.classname) byte_class
  |> PairMap.add ("", bool_class.classname) bool_class
  |> PairMap.add ("", null_class.classname) null_class
  |> PairMap.add ("", string_class.classname) string_class
  |> PairMap.add ("", option_class.classname) option_class
  |> PairMap.add ("", array_class.classname) array_class

let string_of_tenv tenv =
  String.concat ", " (
    List.map (fun ((mn, tn), _) -> mn ^ "::" ^ tn)
      (PairMap.bindings tenv)
  )

(* Symtable concept: a map for current scope, parent and children nodes *)

(** Symbol table entry type for a variable. *)
type 'addr st_entry = {
    symname: string;
    symtype: typetag;
    (* 'var' is what's checked for any local assignment *)
    var: bool;
    (* Function parameters are not vars, they can't be reassigned,
     * but they might be mutable, so we do need separate fields 
     * (it's not part of the type but the symbol) *)
    mut: bool;
    (* store an address (stack or heap) for code generation. *)
    addr: 'addr option
  }

(** Symbol table entry type for a procedure. *)
type 'addr st_procentry = {
    procname: string;
    rettype: typetag;  (* there's a void typetag *)
    (* could it be just a list of types, no names? but st_entry also
     * has the mutability info, very convenient. *)
    fparams: 'addr st_entry list
  }

(** Symbol table entry for a type variable. No address decor needed. *)
type st_tvarentry = {
  tvarname: string;
  implements: string list
}

(** Symbol table tree node for a single scope *)
type 'addr st_node = {
    (* The scope depth is compared to check for redeclaration. *)
    scopedepth: int; 
    mutable syms: 'addr st_entry StrMap.t;
    mutable fsyms: 'addr st_procentry StrMap.t;  (* No overloading! *)
    mutable tvars: st_tvarentry StrMap.t;
    (* vars declared but not initted in this scope. *)
    mutable uninit: StrSet.t;
    (* vars from higher scope that are initted in this scope.
       Need this for analyzing if all if or case blocks init a value *)
    mutable parent_init: StrSet.t;
    (* The root node has no parent *)
    parent: 'addr st_node option; 
    mutable children: 'addr st_node list;
    (* containing proc needed to check return statements and for codegen. *)
    in_proc: 'addr st_procentry option;
  }

let st_node_to_string node =
  let rec ts' pad nd = 
    pad ^ string_of_int nd.scopedepth ^ "{ vars: ("
    ^ String.concat ","
        (List.map (fun entry -> (snd entry).symname) (StrMap.bindings nd.syms))
    ^ ")\n" ^ pad ^ "   procs: ["
    ^ String.concat ","
        (List.map (fun entry -> (snd entry).procname) (StrMap.bindings nd.fsyms))
    ^ "]\n"
    ^ String.concat "" (List.map (ts' (pad ^ "   ")) nd.children)
    ^ pad ^ "}\n" in
  ts' "" node

(** Values and functions for the st_node type. *)
(* Had specificity problems with this, maybe don't need a signature. *)
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
      tvars = StrMap.empty;
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
         | None ->
            failwith ("BUG: Varname " ^ varname ^ " not found for set_addr"))
        nd.syms

  (** Add type variable to symbol table node. *)
  let addtvar nd varname impls =
    match StrMap.find_opt varname nd.tvars with
    | None ->
       nd.tvars <- StrMap.add varname {tvarname=varname; implements=impls} nd.tvars
    | Some _ -> (* Is caught by analyzer but just in case *)
       raise (SymbolError ("redefinition of type parameter " ^ varname))
        
  (** Add procedure to current scope of a node. *)
  let addproc nd pname entry =
    match StrMap.find_opt pname nd.fsyms with
    | None ->
       nd.fsyms <- StrMap.add pname entry nd.fsyms
    | Some _ -> (* should be caught by analyzer *)
       raise (SymbolError ("redefinition of procedure \"" ^ entry.procname
                           ^ "\""))

  (** Option-return symtable lookup, for typechecking. *)
  let rec findvar_opt name nd =
    match StrMap.find_opt name nd.syms with
    | Some entry -> Some (entry, nd.scopedepth)
    | None -> (
      match nd.parent with
      | Some parent -> findvar_opt name parent
      | None -> None
    )

  (** Exception-throwing symtable lookup, for use in codegen. *)
  let findvar name nd =
    match findvar_opt name nd with
    | Some ent -> ent
    | None -> raise Not_found

  (** Option-return type variable lookup. *)
  let rec findtvar_opt varname node =
    match StrMap.find_opt varname node.tvars with
    | Some entry -> Some (entry, node.scopedepth)
    | None -> (
        match node.parent with
        | Some parent -> findtvar_opt varname parent
        | None -> None
      )
  
  (** Option-return procedure lookup. *)
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
        (* for efficiency, since there's no nested scopes for type variables,
           should it just get the parent's tvars? *)
        tvars = nd.tvars;
        parent = Some nd;
        parent_init = StrSet.empty;
        in_proc = nd.in_proc;
        children = [];
        (* No copy constructor so... *)
        uninit = StrSet.union StrSet.empty nd.uninit
      } in
    nd.children <- newnode :: nd.children;
    newnode


  (** Create a scope for a new procedure (sets "in_proc") *)
  let new_proc_scope nd procentry =
    let newnode = {
        scopedepth = nd.scopedepth + 1;
        syms = StrMap.empty;
        fsyms = StrMap.empty;
        tvars = StrMap.empty; 
        parent = Some nd;
        parent_init = StrSet.empty;
        in_proc = Some procentry;
        children = [];
        uninit = StrSet.fold StrSet.add StrSet.empty nd.uninit
      } in
    nd.children <- newnode :: nd.children;
    newnode

end (* module Symtable *)

