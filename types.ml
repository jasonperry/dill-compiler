(** Types for type info, seems this will be used end-to-end *)

(** in-place type variables for generics, including constraints *)
type typevar = {
    varname: string;
    interfaces: string list
  }

(** Type information about a single record field. *)
and fieldInfo = {
    fieldname: string;
    priv: bool;
    mut: bool;
    fieldClass: classData
  }

(** The specification for a class of types, as defined by a record or etc. *)
and classData = {
    classname: string;
    muttype: bool;  (* in structs, inferred from field mutability *)
    params: typevar list; (* generic params *)
    implements: string list; (* interfaces *)
    (* When we do generics, need to link the field type parameters. *)
    fields: fieldInfo list
    (* also need all method signatures. *)
  }

(** Unique name of a concrete type. *)
and typetag = {
    (* what to do for function type? *)
    (* typename: string; *)  (* kept in the dictionary *)
    tclass: classData;
    paramtypes: (string * string) list; (* generics that are resolved. *)
    array: bool;   (* array type (the only native container type for now) *)
    (* size: int;  (* 4 if a reference type? 8? *) *)
    nullable: bool; (* will this be part of the classdata? *)
  }

(** Generate a type for a typetag for a class (and later, specify generics *)
let specify_type classdata _ (* "instants" *) =
  (* should I make this work for built-in types? *)
  { tclass=classdata;
    paramtypes = []; (* need to match up variable names *)
    array = false;
    nullable = false;
  }
      

(** Convert a type tag to printable format. *)
let typetag_to_string tt =
  List.fold_left
    (fun s (_, vval) -> s ^ "<" ^ vval ^ "> ") "" tt.paramtypes
  ^ tt.tclass.classname
  ^ (if tt.array then "[]" else "")
  ^ (if tt.nullable then "?" else "")

(* Class definitions for built-in types, and tags for convenience. *)
let void_class =  { classname="Void"; muttype=false; params=[];
                    implements=[]; fields=[] }
let void_ttag = {tclass = void_class; paramtypes=[];
                 array=false; nullable=false}

let int_class = {classname="Int"; muttype=false; params=[];
                 implements=[]; fields=[] } (* later: "Arith" *)
let int_ttag = {tclass=int_class;
                paramtypes=[]; array=false; nullable=false}

let bool_class = {classname="Bool"; muttype=false; params=[];
                  implements=[]; fields=[]}
let bool_ttag = {tclass=bool_class; paramtypes=[]; array=false;
                 nullable=false}

let float_class = {classname="Float"; muttype=false; params=[];
                   implements=[]; fields=[]}
let float_ttag = {tclass=float_class; paramtypes=[]; array=false;
                  nullable=false}
(* whether the variable can be mutated is a feature of the symbol table. *)
