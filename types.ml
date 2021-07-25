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

(** The specification for a class of types, built from a type declaration *)
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
    fields: fieldInfo list;
    subtypes: (string * typetag) list
    (* also need all method signatures. No, not in the latest design! *)
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
                   muttype=false; params=[]; implements=[]; fields=[];
                   subtypes=[] }
let null_ttag = gen_ttag null_class []
(* NOTE: void is not a type! Maybe it shouldn't be one in Dill, just have
 * procs that return nothing. *)
let void_class =  { classname="Void"; in_module = "";
                    muttype=false; params=[]; implements=[]; fields=[];
                    subtypes=[] }
let void_ttag = gen_ttag void_class []

let int_class = { classname="Int"; in_module = ""; muttype=false; params=[];
                  implements=[]; fields=[];
                  subtypes=[] } (* later: "Arith" *)
let int_ttag = gen_ttag int_class []

let bool_class = { classname="Bool"; in_module = ""; muttype=false; params=[];
                   implements=[]; fields=[];
                   subtypes=[] }
let bool_ttag = gen_ttag bool_class []

let float_class = { classname="Float"; in_module=""; muttype=false; params=[];
                    implements=[]; fields=[];
                    subtypes=[] }
let float_ttag = gen_ttag float_class []

let string_class = { classname="String"; in_module=""; muttype=false;
                     params=[]; implements=[]; fields=[];
                   subtypes=[] }
let string_ttag = gen_ttag string_class []
(* whether the variable can be mutated is a feature of the symbol table. *)
