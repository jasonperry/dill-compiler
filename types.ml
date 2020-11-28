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
    (* classname: string; (* do I even need it? *) *)
    ttag: typetag;  (* later, a typetag /template/ (or just subst tvars) *)
    muttype: bool;  (* in structs, inferred from field mutability *)
    params: typevar list; (* generic params *)
    implements: string list; (* interfaces *)
    (* When we do generics, need to link the field type parameters. 
       (possibly just by varname) *)
    fields: fieldInfo list
    (* also need all method signatures. *)
  }

(** Unique name of a concrete type. *)
and typetag = {
    (* what to do for function type? *)
    modulename: string;
    typename: string;
    (* tclass: classData; *)
    (* TODO: have an "unresolved" typetag. *)
    paramtypes: typetag list; (* resolved generics. *)
    array: bool;   (* array type (the only native container type for now) *)
    (* size: int;  (* 4 if a reference type? 8? *) *)
    nullable: bool; (* will this be part of the classdata? *)
  }


(** Generate a type for a typetag for a class (and later, specify generics *)
let gen_ttag classdata _ (* "instants" (probably map) *) =
  (* later: substitute class types *)
  classdata.ttag
     

(** Convert a type tag to printable format. *)
let rec typetag_to_string (tt: typetag) =
  if tt.paramtypes <> [] then 
    "<"
    ^ List.fold_left
        (fun s pt -> s ^ "," ^ (typetag_to_string pt)) "" tt.paramtypes
    ^ ">"
  else ""
  ^ tt.modulename ^ "."
  ^ tt.typename
  ^ if tt.array then "[]" else ""
  ^ if tt.nullable then "?" else ""


(* Class definitions for built-in types, and tags for convenience. *)
let void_ttag = { modulename = ""; typename="Void"; paramtypes=[];
                  array=false; nullable=false }
let void_class =  { ttag=void_ttag; muttype=false; params=[];
                    implements=[]; fields=[] }

let int_ttag = { modulename = ""; typename="Int";
                 paramtypes=[]; array=false; nullable=false }
let int_class = { ttag=int_ttag; muttype=false; params=[];
                  implements=[]; fields=[] } (* later: "Arith" *)

let bool_ttag = { modulename=""; typename="Bool"; paramtypes=[];
                  array=false; nullable=false }
let bool_class = { ttag=bool_ttag; muttype=false; params=[];
                   implements=[]; fields=[] }

let float_ttag = { modulename=""; typename="Float"; paramtypes=[];
                   array=false; nullable=false }
let float_class = { ttag=float_ttag; muttype=false; params=[];
                    implements=[]; fields=[]}
(* whether the variable can be mutated is a feature of the symbol table. *)
