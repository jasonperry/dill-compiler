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
    fieldtype: typetag
  }

(** The specification for a class of types, built from a type declaration *)
and classData = {
    classname: string; (* do I even need it? It's the dict key *)
    in_module: string; (* to make it self-contained for generating ttags. *)
      (* also for extensions, types need to "know" the original
       * module where they were defined. *)
    muttype: bool;  (* true if any field or variant is mutable *)
    params: typevar list; (* generic params *)
    (* Impls are no longer part of the type definition, so we'll get rid 
       of this. Only possibility is constraints for the type variables. 
       Need to think about that. *)
    (* implements: string list;  *)
    (* When we do generics, need to link params to the field type variables. 
       (possibly just by var name) *)
    fields: fieldInfo list;
    subtypes: (string * typetag) list (* variants *)
  }

(** Unique specification of a concrete type. It's what's checked for
  * a match with other types. *)
and typetag = {
    (* what to do for function type? *)
    modulename: string;
    typename: string;  (* TODO: check if this will include ? *)
    tclass: classData;
    (* Will I need an "unresolved" typetag for generics? *)
    paramtypes: typetag list; (* resolved generics. *)
    array: bool;   (* array type (going away) *)
    (* size: int;  (* 4 if a reference type? 8? *) *)
    nullable: bool; (* will this be part of the classdata? *)
  }

(** delete this if it turns out not to be needed. *)
let is_record_type ttag =
  ttag.tclass.fields <> []

(*
(** Should only need this for printing out, not internally. *)
let typename (ttag: typetag) =
  ttag.modulename ^ "::" ^ ttag.typename
 *)

(** Generate a type for a typetag for a class (and later, specify generics *)
let gen_ttag (classdata: classData) _ (* mapping to type vars *) =
  (* later: substitute class types *)
  {
    modulename = classdata.in_module;
    typename = classdata.classname;
    tclass = classdata;
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
       ^ tt.modulename ^ "::" ^ tt.typename
       ^ (if tt.array then "[]" else "")
       ^ if tt.nullable then "?" else ""


(* Class definitions for built-in types, and tags for convenience. *)
let null_class = { classname="NullType"; in_module = "";
                   muttype=false; params=[]; fields=[];
                   subtypes=[] }
let null_ttag = gen_ttag null_class []
(* NOTE: void is not a type! Maybe it shouldn't be one in Dill, just have
 * procs that return nothing. *)
let void_class =  { classname="Void"; in_module = ""; muttype=false;
                    params=[]; fields=[]; subtypes=[] }
let void_ttag = gen_ttag void_class []

let int_class = { classname="Int"; in_module = ""; muttype=false; params=[];
                  fields=[]; subtypes=[] } (* later: "Arith" *)
let int_ttag = gen_ttag int_class []

let bool_class = { classname="Bool"; in_module = ""; muttype=false; params=[];
                   fields=[]; subtypes=[] }
let bool_ttag = gen_ttag bool_class []

let float_class = { classname="Float"; in_module=""; muttype=false; params=[];
                    fields=[]; subtypes=[] }
let float_ttag = gen_ttag float_class []

let string_class = { classname="String"; in_module=""; muttype=false;
                     params=[]; fields=[]; subtypes=[] }
let string_ttag = gen_ttag string_class []
(* whether the variable can be mutated is a feature of the symbol table. *)
