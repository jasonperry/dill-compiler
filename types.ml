(** Types for type info, seems this will be used end-to-end *)

(** in-place type variables for generics, with signature impl requirements *)
type typevar = {
    varname: string;
    impls: string list (* probably should be a set later. *)
  }

(** Type information about a single record field. *)
and fieldInfo = {
    fieldname: string;
    priv: bool;
    mut: bool;
    fieldtype: typetag
  }

and kindData =
  | Primitive (* Ooo! *)
  | Struct of fieldInfo list
  | Variant of (string * typetag option) list
  | Newtype of typetag
  | Hidden

(** The specification for a class of types, built from a type declaration *)
and classData = {
    classname: string;
    in_module: string; (* for extensions, types need to "know" the original
                        * module where they were defined. *)
    opaque: bool;
    muttype: bool;  (* true if any field or variant is mutable *)
    rectype: bool;
    (* When we do generics, need to link params to the field type variables. 
       (possibly just by var name) *)
    params: typevar list; (* generic params *)
    (* Impls are no longer part of the type definition *)
    (* implements: string list;  *)
    kindData: kindData
  }

(** Unique specification of a concrete type. It's what's checked for
  * a match with other types. *)
and typetag = {
    (* what to do for function type? *)
    modulename: string;
    typename: string;  (* Is this redundant? Just use the classdata? *)
    (* must be mutable so it can be updated in recursive definitions. *)
    mutable tclass: classData;
    (* Will I need an "unresolved" typetag for generics? *)
    paramtypes: typetag list; (* resolved generics. *)
    array: bool;   (* array type *)
    (* size: int;  (* probably not here, might need a recursive flag *) *)
    nullable: bool;
  }


(** helper to pull out the field assuming it's a struct type *)
let get_fields cdata = match cdata.kindData with
  | Struct flist -> flist
  | _ -> failwith ("BUG: " ^ cdata.classname ^ " is not a struct type")

(** helper to pull out the variants assuming it's a variant type *)
let get_variants cdata = match cdata.kindData with
  | Variant vts -> vts
  | _ -> failwith ("BUG: " ^ cdata.classname ^ " is not a variant type")



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
let null_class = { classname="NullType"; in_module = ""; kindData = Primitive;
                   opaque=false; muttype=false; rectype=false; params=[]; }
let null_ttag = gen_ttag null_class []
(* NOTE: void is not a type! Maybe it shouldn't be one in Dill, just have
 * procs that return nothing. *)
let void_class =  { classname="Void"; in_module = ""; muttype=false;
                    opaque=false; kindData=Primitive; rectype=false; params=[]; }
let void_ttag = gen_ttag void_class []

let int_class = { classname="Int"; in_module = ""; muttype=false; rectype=false;
                  opaque=false; kindData=Primitive; params=[]; }
let int_ttag = gen_ttag int_class []

let float_class = { classname="Float"; in_module=""; muttype=false; rectype=false;
                    params=[]; opaque=false; kindData=Primitive; }
let float_ttag = gen_ttag float_class []

let byte_class = { classname="Byte"; in_module=""; muttype=false; rectype=false;
                   params=[]; opaque=false; kindData=Primitive; }
let byte_ttag = gen_ttag byte_class []

let bool_class = { classname="Bool"; in_module = ""; muttype=false; rectype=false;
                   params=[]; opaque=false; kindData=Primitive; }
let bool_ttag = gen_ttag bool_class []

let string_class = { classname="String"; in_module=""; muttype=false; rectype=false;
                     opaque=false; params=[]; kindData=Primitive; }
let string_ttag = gen_ttag string_class []
(* whether the variable can be mutated is a feature of the symbol table. *)


                           (* helper functions *)

(** Try to fetch field info from a classdata. *)
let get_cdata_field cdata fname =
  match cdata.kindData with
  | Struct fields -> 
    List.find_opt (fun (fi: fieldInfo) -> fi.fieldname = fname) fields
  | _ -> failwith "BUG: attempt to get field from non-struct type"

(** Try to fetch field info from a typetag *)
let get_ttag_field ttag fname =
  if ttag.tclass.kindData = Hidden then None
  else if ttag.nullable then None
  else if ttag.array then (
    if fname = "length" then
      Some { fieldname="length"; priv=false; mut=false; fieldtype=int_ttag }
    else None
  )
  else get_cdata_field ttag.tclass fname

(* Probably don't need these now that I explicitly encode. *)
let is_primitive_type ttag = ttag.tclass.kindData = Primitive
  
(* These are useful b/c you can't just check the fields to see if
 * the "outermost" type is struct or variant *)
let is_struct_type ttag = match ttag.tclass.kindData with
  | Struct _ -> true
  | _ -> false

(* Hmm, should I make a nullable count as a variant type here? *)
let is_variant_type ttag = match ttag.tclass.kindData with
  | Variant _ -> true
  | _ -> false

 
