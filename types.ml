(** Types for type info, seems this will be used end-to-end *)

(* could put these in a "Common" module. *)
module StrMap = Map.Make(String)
module StrSet = Set.Make(String)

(** in-place type variables for generics, including constraints *)
type typevar = {
    varname: string;
    interfaces: string list
  }

(** The specification for a class of types, as defined by a record or etc. *)
type classdata = {
    classname: string;
    mut: bool;
    params: typevar list; (* generic params *)
    implements: string list (* interfaces *)
    (* also need all method signatures. *)
  }

(** Unique name of a concrete type. *)
type typetag = {
    (* what to do for function type? *)
    (* typename: string; *)
    tclass: classdata;
    paramtypes: (string * string) list; (* generics that are resolved. *)
    array: bool;   (* array type (the only native container type for now) *)
    (* size: int;  (* 4 if a reference type? 8? *) *)
    nullable: bool;
  }

(** Convert a type tag to printable format. *)
let typetag_to_string tt =
  List.fold_left
    (fun s (_, vval) -> s ^ "<" ^ vval ^ "> ") "" tt.paramtypes
  ^ tt.tclass.classname
  ^ (if tt.array then "[]" else "")
  ^ (if tt.nullable then "?" else "")

(* Class definitions for built-in types, and tags for convenience. *)
let void_class =  { classname="void"; mut=false; params=[];
                    implements=[] }
let void_ttag = {tclass = void_class; paramtypes=[];
                 array=false; nullable=false}

let int_class = {classname="int"; mut=false; params=[];
                 implements=[] } (* later: "Arith" *)
let int_ttag = {tclass=int_class;
                paramtypes=[]; array=false; nullable=false}

let bool_class = {classname="bool"; mut=false; params=[];
                  implements=[]}
let bool_ttag = {tclass=bool_class; paramtypes=[]; array=false;
                 nullable=false}

let float_class = {classname="float"; mut=false; params=[];
                   implements=[]}
let float_ttag = {tclass=float_class; paramtypes=[]; array=false;
                  nullable=false}
(* whether the variable can be mutated is a feature of the symbol table. *)
