
(* May need more structured type data, so here is a module for it. *)

(** in-place type variables for generics, including constraints *)
type typevar = {
    varname: string;
    interfaces: string list
  }

(** Entry for a class of types, as defined by a record or etc. *)
type classdata = {
    classname: string;
    mut: bool;
    params: typevar list;
    implements: string list
  }

(** Entry for specific type of a declared var or expression *)
type typetag = {
    (* what to do for function type? *)
    (* typename: string; *)
    tclass: classdata;
    paramtypes: (string * string) list; (* typevars that are resolved. *)
    array: bool;   (* array type (the only native container type for now) *)
    (* size: int;  (* 4 if a reference type? 8? *) *) 
  }
