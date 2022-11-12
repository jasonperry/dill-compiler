(** Type types for the type system *)

(** Type information about a single record field. *)
type fieldInfo = {
    fieldname: string;
    priv: bool;
    mut: bool;
    fieldtype: typetag
  }

(** Data needed by the different kinds of types (fields, variants, etc.) *)
and kindData =  (* will array and option be their own kind now? *)
  | Primitive
  | Struct of fieldInfo list
  | Variant of (string * typetag option) list
  | Newtype of typetag
  | Hidden

(** The specification for a class of types, built from a type declaration *)
and classData = {
    classname: string;
    in_module: string; (* for extensions, classes need to "know" the original
                        * module where they were defined. *)
    opaque: bool;
    muttype: bool;  (* true if any field or variant is mutable *)
    rectype: bool;
    (* When we do generics, need to link params to the field type variables. 
       (possibly just by var name) *)
    nparams: int;
    (* params: typevar list; (* generic params. could it just be the number? *) *)
    kindData: kindData
  }

(** Typetag is the in-place specification of a type. It's what's
    checked for a match with other types. *)
and namedtypeinfo = {
  modulename: string;
  mutable tclass: classData;
  typeargs: typetag list; (* may or may not be resolved *)
}

and typetag = 
  | Typevar of string
  | Namedtype of namedtypeinfo

      
(* old, pre-generic definition. *)
(* and typetag = {
    (* Later: function types? Just a pair of types? *)
    modulename: string; 
    typename: string;  (* Is this redundant? Just use the classdata? *)
    (* must be mutable so it can be updated in recursive definitions. *)
    mutable tclass: classData;
    (* Will I need an "unresolved" typetag for generics? *)
    paramtypes: typetag list; (* resolved generics. *)
    array: bool;   (* array type *)
    (* size: int;  (* probably not here, might need a recursive flag *) *)
    nullable: bool;
   } *)

(** Generate a type for a typetag for a class (and later, specify generics)
  * No, we don't specify, right? But need to generate variables. *)
let gen_ttag (classdata: classData) argtypes (* concrete or names from context *) =
  (* later: substitute class types *)
  Namedtype {
    modulename = classdata.in_module;
    tclass = classdata;
    typeargs = argtypes (* Is it right to copy these directly? *)
  }


(* Class definitions for built-in types, and tags for convenience. *)
let null_class = { classname="NullType"; in_module = ""; kindData = Primitive;
                   opaque=false; muttype=false; rectype=false; nparams=0; }
let null_ttag = gen_ttag null_class []
(* NOTE: void is not a type! Maybe it shouldn't be one in Dill, just have
 * procs that return nothing. *)
let void_class =  { classname="Void"; in_module = ""; muttype=false;
                    opaque=false; kindData=Primitive; rectype=false; nparams=0; }
let void_ttag = gen_ttag void_class []

let int_class = { classname="Int"; in_module = ""; muttype=false; rectype=false;
                  opaque=false; kindData=Primitive; nparams=0; }
let int_ttag = gen_ttag int_class []

let float_class = { classname="Float"; in_module=""; muttype=false; rectype=false;
                    nparams=0; opaque=false; kindData=Primitive; }
let float_ttag = gen_ttag float_class []

let byte_class = { classname="Byte"; in_module=""; muttype=false; rectype=false;
                   nparams=0; opaque=false; kindData=Primitive; }
let byte_ttag = gen_ttag byte_class []

let bool_class = { classname="Bool"; in_module = ""; muttype=false; rectype=false;
                   nparams=0; opaque=false; kindData=Primitive; }
let bool_ttag = gen_ttag bool_class []

let string_class = { classname="String"; in_module=""; muttype=false; rectype=false;
                     opaque=false; nparams=0; kindData=Primitive; }
let string_ttag = gen_ttag string_class []
(* whether the variable can be mutated is a feature of the symbol table. *)


(* Class definitions for built in generic types. Not clear if it's OK
   to call them primitive. *)
let option_class = { classname="Option"; in_module="";
                     kindData=Struct ([{fieldname="length"; priv=false; mut=false;
                                       fieldtype=int_ttag}]);
                     opaque=true; muttype=false; rectype=false; nparams=1; }
let array_class = { classname="Array"; in_module=""; kindData=Primitive;
                     opaque=true; muttype=false; rectype=false; nparams=1; }


(** Convert a type tag to printable format. *)
let rec typetag_to_string = function
  | Namedtype tinfo ->
    if tinfo.tclass = option_class then
      typetag_to_string (List.hd tinfo.typeargs) ^ "?"
    else if tinfo.tclass = array_class then
      typetag_to_string (List.hd tinfo.typeargs) ^ "[]"
    else
      tinfo.modulename ^ "::" ^ tinfo.tclass.classname
      ^ (if tinfo.tclass.nparams > 0 then 
           "("
           ^ String.concat ","
             (List.map (fun pt -> typetag_to_string pt) tinfo.typeargs)
           ^ ")"
         else "")
  | Typevar t -> t


                           (* helper functions *)

(** helper to pull out the field assuming it's a struct type *)
let get_fields cdata = match cdata.kindData with
  | Struct flist -> flist
  | _ -> failwith ("BUG: " ^ cdata.classname ^ " is not a struct type")


(** helper to pull out the variants assuming it's a variant type *)
let get_variants cdata = match cdata.kindData with
  | Variant vts -> vts
  | _ -> failwith ("BUG: " ^ cdata.classname ^ " is not a variant type")


(** Try to fetch field info from a classdata. *)
let get_cdata_field cdata fname =
  match cdata.kindData with
  | Struct fields -> 
    List.find_opt (fun (fi: fieldInfo) -> fi.fieldname = fname) fields
  | _ -> failwith "BUG: attempt to get field from non-struct type"

(** Try to fetch field info from a typetag *)
let get_ttag_field ttag fname =
  match ttag with
  | Typevar _ -> None
  | Namedtype tinfo ->
    if tinfo.tclass.kindData = Hidden then None
    (* No longer need special case for Array or Option *)
    else get_cdata_field tinfo.tclass fname

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

 
(** Exact type comparison. Need this because we have recursively
    defined classes--can't equality-compare those. *)
let rec types_equal (t1: typetag) (t2: typetag) =
  match (t1, t2) with
  | (Typevar _, Typevar _) -> true (* true?? *)
  | (Namedtype tinfo1, Namedtype tinfo2) -> 
    (tinfo1.modulename = tinfo2.modulename
     && tinfo1.tclass.classname = tinfo2.tclass.classname
     (* Now we do recurse on the type variables. *)
     && List.for_all2 types_equal tinfo1.typeargs tinfo2.typeargs)
  | _ -> false

(** Ensure first argument is of equal or more specific type than second. *)
let subtype_match (subtag: typetag) (supertag: typetag) =
  (* easy case exact match *)
  types_equal subtag supertag
  (* Only other case for now: match if supertype is nullable *)
  || (match supertag with
      | Namedtype tinfo -> tinfo.tclass = option_class &&
                           types_equal (List.hd tinfo.typeargs) subtag
      | _ -> false)
(* Specific type is one of the types in a union. This doesn't apply anymore. *)
  (* || List.exists ((=) subtag) supertag.tclass.variants *)
