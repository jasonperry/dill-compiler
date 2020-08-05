(** Types for type info, seems this will be used end-to-end *)

(* could put this in a "Common" module. *)
module StrMap = Map.Make(String)


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
    paramtypes: (string * string) list; (* typevars that are resolved. *)
    array: bool;   (* array type (the only native container type for now) *)
    (* size: int;  (* 4 if a reference type? 8? *) *) 
  }

(** Convert a type tag to printable format. *)
let typetag_to_string tt =
  tt.tclass.classname
  ^ List.fold_left
      (fun s (_, vval) ->
        s ^ "<" ^ vval ^ "> "
      ) "" tt.paramtypes

(* The built-in types are kind of important. I may want to put them 
 * somewhere else. *)
let void_class =  { classname="void"; mut=false; params=[];
                    implements=[] }

(** type tag bound to a name for easy access. *)
(* Should I have a way to generate tags from classes? *)
let void_ttag = {tclass = void_class; paramtypes=[];
                 array=false}

