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
    fields: fieldInfo list; (* should be map? *)
    variants: (string * typetag option) list (* variant name and type if any *)
  }

(** Unique specification of a concrete type. It's what's checked for
  * a match with other types. *)
and typetag = {
    (* what to do for function type? *)
    modulename: string;
    typename: string; 
    tclass: classData;
    (* Will I need an "unresolved" typetag for generics? *)
    paramtypes: typetag list; (* resolved generics. *)
    array: bool;   (* array type *)
    (* size: int;  (* probably not here, might need a recursive flag *) *)
    nullable: bool;
  }


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
    "("
    ^ String.concat ","
        (List.map (fun pt -> typetag_to_string pt) tt.paramtypes)
    ^ ")"
  else ""
       ^ tt.modulename ^ "::" ^ tt.typename
       ^ (if tt.array then "[]" else "")
       ^ if tt.nullable then "?" else ""


(* Class definitions for built-in types, and tags for convenience. *)
let null_class = { classname="NullType"; in_module = "";
                   muttype=false; params=[]; fields=[];
                   variants=[] }
let null_ttag = gen_ttag null_class []
(* NOTE: void is not a type! Maybe it shouldn't be one in Dill, just have
 * procs that return nothing. *)
let void_class =  { classname="Void"; in_module = ""; muttype=false;
                    params=[]; fields=[]; variants=[] }
let void_ttag = gen_ttag void_class []

let int_class = { classname="Int"; in_module = ""; muttype=false; params=[];
                  fields=[]; variants=[] } (* later: "Arith" *)
let int_ttag = gen_ttag int_class []

let bool_class = { classname="Bool"; in_module = ""; muttype=false; params=[];
                   fields=[]; variants=[] }
let bool_ttag = gen_ttag bool_class []

let float_class = { classname="Float"; in_module=""; muttype=false; params=[];
                    fields=[]; variants=[] }
let float_ttag = gen_ttag float_class []

let string_class = { classname="String"; in_module=""; muttype=false;
                     params=[]; fields=[]; variants=[] }
let string_ttag = gen_ttag string_class []
(* whether the variable can be mutated is a feature of the symbol table. *)


                           (* helper functions *)

(** Try to fetch field info from a classdata. *)
let get_cdata_field cdata fname =
  List.find_opt (fun (fi: fieldInfo) -> fi.fieldname = fname) cdata.fields

(** Try to fetch field info from a typetag *)
let get_ttag_field ttag fname =
  if ttag.nullable then None
  else if ttag.array then (
    if fname = "length" then
      Some { fieldname="length"; priv=false; mut=false; fieldtype=int_ttag }
    else None
  )
  else get_cdata_field ttag.tclass fname


let is_primitive_type ttag =
  (* would it be better to just look for the fixed set of primitive types? 
     Maybe not, because that will expand (Int64, etc.) *)
  not ttag.array && not ttag.nullable
  && ttag.tclass.fields = [] && ttag.tclass.variants = []
  
(* These are useful b/c you can't just check the fields to see if
 * the "outermost" type is struct or variant *)
let is_struct_type ttag =
  (not ttag.array) && (not ttag.nullable) && ttag.tclass.fields <> []

(* Hmm, should I make a nullable count as a variant type here? *)
let is_variant_type ttag =
  (not ttag.array) && (not ttag.nullable) && ttag.tclass.variants <> []
    

(*
(** Should only need this for printing out, not internally. *)
let typename (ttag: typetag) =
  ttag.modulename ^ "::" ^ ttag.typename
 *)
