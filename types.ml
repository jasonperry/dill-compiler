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
    fieldtype: typetag (* classData, formerly *)
  }

(** The specification for a class of types, as defined by a record or etc. *)
and classData = {
    classname: string; (* do I even need it? It's the dict key *)
    in_module: string; (* to make it self-contained for generating ttags. *)
      (* anyway, if we have extensions, still need to reference the original
       * module where the class was defined. *)
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
    array: bool;   (* array type (going away) *)
    (* size: int;  (* 4 if a reference type? 8? *) *)
    nullable: bool; (* will this be part of the classdata? *)
  }


(** Generate a type for a typetag for a class (and later, specify generics *)
let gen_ttag (classdata: classData) _ (* mapping to type vars *) =
  (* later: substitute class types *)
  {
    modulename = classdata.in_module;
    typename = classdata.classname;
    paramtypes = [];
    (* array and nullable types won't be part of the class, they're
       specified in declarations. *)
    array = false;  
    nullable = false;
  }


(** Convert a type tag to printable format. *)
let rec typetag_to_string (tt: typetag) =
  if tt.paramtypes <> [] then 
    "<"
    ^ String.concat ","
        (List.map (fun pt -> typetag_to_string pt) tt.paramtypes)
    ^ ">"
  else ""
  ^ tt.modulename ^ "."
  ^ tt.typename
  ^ if tt.array then "[]" else ""
  ^ if tt.nullable then "?" else ""


(* Class definitions for built-in types, and tags for convenience. *)
let void_class =  { classname="Void"; in_module = "";
                    muttype=false; params=[]; implements=[]; fields=[] }
let void_ttag = gen_ttag void_class []

let int_class = { classname="Int"; in_module = ""; muttype=false; params=[];
                  implements=[]; fields=[] } (* later: "Arith" *)
let int_ttag = gen_ttag int_class []

let bool_class = { classname="Bool"; in_module = ""; muttype=false; params=[];
                   implements=[]; fields=[] }
let bool_ttag = gen_ttag bool_class []

let float_class = { classname="Float"; in_module=""; muttype=false; params=[];
                    implements=[]; fields=[]}
let float_ttag = gen_ttag float_class []
(* whether the variable can be mutated is a feature of the symbol table. *)
