(** Code generation module *)

open Common
open Ast
open Types
open Symtable1
open Llvm

exception CodegenError of string

(* Trying not to make a new context per module. OK so far. *)
let context = global_context() 
let float_type = double_type context
let int_type = i32_type (* i64_type *) context
let int64_type = i64_type context
let bool_type = i1_type context
let byte_type = i8_type context
let void_type = void_type context
(* LLVM doesn't like pointers to void, use this for polymorphic ptrs *)
let voidptr_type = pointer_type (i8_type context) 
let nulltag_type = i8_type context
let varianttag_type = i32_type context

let is_pointer_value llval = classify_type (type_of llval) = TypeKind.Pointer
let is_pointer_type llval = classify_type llval = TypeKind.Pointer

(* Implement comparison for typetag so we can make a map of them. *)
(* Note: haven't done this yet, still using the string pair for basetype *)
module TypeTag = struct
  type t = typetag
  let compare t1 t2 =
    String.compare (typetag_to_string t1) (typetag_to_string t2)
end

module TtagMap = Map.Make(TypeTag)

(** type environment to store lltypes and field/tag offsets for named
    classes. Entries built by add_lltype. Used a lot by ttag_to_lltype *)
module Lltenv = struct
  (* fieldmap is used for both struct offsets and union tags. *)
  (* ...could it skip the typetags and get lltype directly??? Maybe only if
     the lltype is fully specified. *)
  type fieldmap = (int * typetag) StrMap.t
  (* Maps modulename, typename pair to the LLVM type and field map. *)
  type lltentry = {
    lltype: lltype;
    fieldmap: fieldmap;
    tvslots: int list list array
  }
  type t = (* (lltype * fieldmap) *) lltentry PairMap.t  
  let empty: t = PairMap.empty
  let add = PairMap.add
  (* Can I have a function to take a typetag and pull in_module and
     classname out of that, so I don't have to awkwardly pass pairs?
     Yes, could, but REMEMBER: the LLtenv is only used for looking up
     *classes*.  Array and nullable types are generated at the point
     of use. *)
  (* Return just the LLVM type for a given type name. *)
  let find = PairMap.find
  let find_opt = PairMap.find_opt
  let find_lltype tkey tmap = (PairMap.find tkey tmap).lltype
  (* Look up the base typename for a class. *)
  let find_lltype_opt tkey tmap =
    Option.map (fun ent -> ent.lltype) (PairMap.find_opt tkey tmap)
  let find_class_lltype tclass tmap =
    (PairMap.find (tclass.in_module, tclass.classname) tmap).lltype
  (* Get the mapping of fields to types for a struct type. *)
  let find_class_fieldmap tclass tmap =
    (PairMap.find (tclass.in_module, tclass.classname) tmap).fieldmap
  (* Get the offset of a record field from a type's field map. *)
  let find_field tkey fieldname tmap =
    let ent = PairMap.find tkey tmap in
    StrMap.find fieldname ent.fieldmap
end

(** Process a classData to generate a new llvm type entry for lltenv *)
let rec add_lltype the_module  (* returns (classdata, Lltenv.fieldmap) *)
    (types: classData PairMap.t) (lltypes: Lltenv.t) layout (cdata: classData)
    =
    match Lltenv.find_opt (cdata.in_module, cdata.classname) lltypes with
    (* TESTME: don't think this can happen; make it trigger an error and test. *)
  | Some ent -> ent
  | None -> (
      debug_print ("generating lltype for " ^ cdata.classname);
      let primtype_entry lltype : Lltenv.lltentry =
        { lltype=lltype; fieldmap=StrMap.empty; tvslots=[||] } in
      match (cdata.in_module, cdata.classname) with
      (* need special case for primitive types. Should handle this with some
       * data structure, so it's consistent among modules *)
      (* These are only hit when we recurse, so maybe we shouldn't? *)
      | ("", "Void") -> primtype_entry void_type
      | ("", "Int") -> primtype_entry int_type
      | ("", "Float") -> primtype_entry float_type
      | ("", "Byte") -> primtype_entry byte_type
      | ("", "Bool") -> primtype_entry bool_type
      | ("", "String") -> primtype_entry (pointer_type (i8_type context))
      | ("", "NullType") -> primtype_entry nulltag_type (* causes crash? *) 
      | _ ->
        (* Process non-primitive type.
           1. create named struct lltype to fill in later *)
        let context = module_context the_module in
        (* guess we always use the qualified type name in llvm *)
        let typename = cdata.in_module ^ "::" ^ cdata.classname in
        let llstructtype =
          match type_by_name the_module typename with
          | None -> named_struct_type context typename
          | Some llty -> llty  (* how could it already exist? See above also *)
        in
        (* Create map from type variables to the "slots" they appear in
           (will be converted to an array when done) *)
        (* TODO: with tuples, each may be a pair. Arrays different too *)
        let slotmap: (string * int list list) array = Array.init
            (List.length cdata.tparams)
            (fun i -> (List.nth cdata.tparams i, [])) in
        (* Pull out fields; same for both struct and variant types *)
        let fielddata =
          match cdata.kindData with
          | Struct fields ->
            (* mutability info about struct fields not needed for codegen, so we
               filter it out. *)
            List.map (fun fi -> (fi.fieldname, [fi.fieldtype])) fields
          | Variant vts -> vts (* variants are already a list for each variant *)
          | _ -> []
        in 
        (* 2. generate list of (name, lltype, offset, type) for fields *)
        let ftypeinfo = List.mapi (fun i (fieldname, ftys) ->
            (* Inner loop because variants can have a tuple of types *)
            let flltys = List.map (fun fttag ->
                match fttag with
                | Typevar tv ->
                  (* Append a new entry to the slots list for this tv *)
                  let tvix, (_, prevmap) = array_find_index_ex slotmap
                      (fun (v, _) -> v = tv) in
                  Array.set slotmap tvix (tv, prevmap @ [[i]]); (* needs j too for tuples *)
                  (voidptr_type, Typevar tv)
                | Namedtype tinfo ->
                  let mname, tname =
                    tinfo.tclass.in_module, tinfo.tclass.classname in
                  let fllty = match Lltenv.find_opt (mname, tname) lltypes with
                    | Some fent ->
                      debug_print ("#CG add_lltype: existing type for field "
                                   ^ string_of_lltype fent.lltype);
                      (* If this field takes type args, for each one take its slots
                         list and add the entries to the parent slot list. *)
                      List.iteri (fun fi fttag -> match fttag with
                          (* Look up field typearg (which should be a variable)
                             in this's slotmap *) 
                          | Namedtype _ ->
                            failwith "type arg in class supposed to be a typevar"
                          | Typevar ftv ->
                            (* get index and slots of typevar in parent type. *)
                            let tvix, (_, prevmap) = array_find_index_ex slotmap
                                (fun (v, _) -> v = ftv) in
                            (* get the field's slotmap for that type param's position *)
                            let fslots = Array.get fent.tvslots fi in
                            (* append slot address to parent field number for each *)
                            let pfslots = List.map (fun faddr -> i::faddr) fslots in
                            Array.set slotmap tvix (ftv, prevmap @ pfslots)
                        ) tinfo.typeargs;
                      fent.lltype
                  (* If the field's lltype isn't generated yet, either recurse
                     or, if it's a recursive type, fetch the named type *)
                  | None ->
                    if tinfo.tclass.rectype then
                      let ftypename = mname ^ "::" ^ tname in
                      match type_by_name the_module ftypename with
                      | Some llfieldtype -> pointer_type llfieldtype
                      | None ->
                        (* if it's an external rectype, add it as normal *)
                        if mname = cdata.in_module then (
                          debug_print ("#CG: recursive field type " ^ ftypename
                                       ^ " not found, adding named struct lltype.");
                          pointer_type (named_struct_type context ftypename)
                        )
                        else 
                          (* mname not included because local types have no
                             module prefix in the tenv. Think is is the right way *)
                          (add_lltype the_module types lltypes layout
                             (PairMap.find ("", tname) types)).lltype
                    else
                      (add_lltype the_module types lltypes layout
                         (PairMap.find ("", tname) types)).lltype
                  in
                  (* check for non-base types and add them if needed. *)
                  (* currently allows array of nullable but no nullable array *)
                  let fllty =
                      if is_option_type fttag then
                        struct_type context [| nulltag_type; fllty |]
                      else fllty in
                  (fllty, fttag)
              ) ftys
            in
            match flltys with 
            (* Field has no typetag only for variant types *)
            | [] -> (fieldname, void_type, i, void_ttag)
            | [(llty, ttag)] -> (fieldname, llty, i, ttag)
            | flltypes ->  (* make struct type for variant tuple *)
              let llvtup = struct_type context
                  (Array.of_list (List.map fst flltypes)) in
              (* wishful thinking: that I don't need the ttags for
                     each type in the variant tuple. *)
              (fieldname, llvtup, i, void_ttag)  (* TESTME: doing without tag. *)
              (* Create array type for the field if needed. *)
              (* TESTME: not reached because Array is now a class.
                       Other array types created in ttag_to_lltype.
                 test if we need this. *)
              (*let fieldlltype =
                    if is_array_type fty then
                      struct_type context
                        [| int_type; pointer_type (array_type ty1 0) |]
                    else ty1 in
                    (fieldname, fieldlltype, i, fty)) *)
          ) fielddata
        in
        (* 3. Create the mapping from field names to offset and type. *)
        (* do we still need the high-level type? maybe for lookup info. *)
        let fieldmap =
          List.fold_left (fun fomap (fname, _, i, ftype) ->
              StrMap.add fname (i, ftype) fomap
            ) StrMap.empty ftypeinfo in
        match cdata.kindData with 
        (* 4. generate the llvm named struct type *)
        (* Fields have already been generated, but may want to split it out
           into a more sensible separate function for each kind. *)
        | Struct _ ->
          struct_set_body llstructtype
            (List.map (fun (_, lty, _, _) -> lty) ftypeinfo
             |> Array.of_list) false; (* false: don't use packed structs. *)
          debug_print ("generated struct type body: "
                       ^ string_of_lltype llstructtype);
          if cdata.rectype then
            (* recursive types are reference types *)
            { lltype=(pointer_type llstructtype); fieldmap=fieldmap;
              tvslots=Array.map snd slotmap }
          else 
            { lltype=llstructtype; fieldmap=fieldmap;
              tvslots=Array.map snd slotmap }
        (* Variant case: struct of tag + optional byte array for the union *)
        | Variant _ ->
          (* Compute max size of any of the variant subtypes. *)
          let maxsize =
            List.fold_left (fun max llvarty ->
                let typesize =
                  if llvarty = void_type then Int64.of_int 0
                  else Llvm_target.DataLayout.abi_size llvarty layout
                in if typesize > max then typesize else max
              )
              (Int64.of_int 0)
              (List.map (fun (_, llvarty, _, _) -> llvarty) ftypeinfo)
          in
          debug_print (cdata.classname ^ " max variant size: "
                       ^ Int64.to_string maxsize);
          (* compute two-field struct type (tag and data value) *)
          (* TODO: optimize to have just the tag (enum) if max size is zero. *)
          (* let vstructtype = named_struct_type context typename in *)
          struct_set_body llstructtype
            (if maxsize = Int64.zero then 
               [| varianttag_type |]
             else
               [| varianttag_type;
                  (* Voodoo magic: adding 4 bytes fixes my double problem. *)
                  array_type (i8_type context) (Int64.to_int maxsize + 4) |])
            false;
          if cdata.rectype then
            { lltype=(pointer_type llstructtype); fieldmap=fieldmap;
              tvslots=Array.map snd slotmap }
          else
            { lltype=llstructtype; fieldmap=fieldmap;
              tvslots=Array.map snd slotmap }
        (* FIXME: these cases should go above, I think. *)
        | Hidden ->
          (* Unknown implementation, must be treated as void pointer *)
          primtype_entry voidptr_type
        | _ -> (* TODO: opaque type and newtype *)
          (* Now it's an opaque type, but I really don't want to assume.
             need to put an opaque marker in classData?
             Maybe go with a kind variant instead of just lists that can be empty? *)
          failwith ("BUG: missing codegen for class type " ^ cdata.classname)
    )

(** change all locations of a type variable in an llvm struct type to a
    specified (pointer) type. *)
let specify_gtype (llentry: Lltenv.lltentry) tvindex conctype =
  (* TODO: arrays will work differently. *)
  let tvslots = Array.get llentry.tvslots tvindex in
  let newtype = List.fold_left (fun llty tvslot ->
      let rec digloop stty slot =
        match slot with
        | [] -> stty (* only hit if no replacement *)
        | ix::[] ->
          let starr = struct_element_types llty in
          (Array.set starr ix conctype;
           struct_set_body stty starr false;
           stty)
        | ix::next::rest -> 
          let starr = struct_element_types stty in
          (Array.set starr ix (digloop (Array.get starr ix) (next::rest));
           struct_set_body stty starr false;
           stty)
      in digloop llty tvslot
    ) llentry.lltype tvslots
  in newtype (* Don't need an entry for on-the-fly types. Symtable? *)
    
(** Use a type tag to generate the LLVM type, adding to the base type
    AND updating generic pointer types with specific ones if there. *)
let rec ttag_to_lltype lltypes ty = match ty with
  | Typevar _ ->
    voidptr_type
  | Namedtype tinfo -> (
      (* Arrays and Options are just classes now, but codegen is specific for them. *)
      (* For arrays, create struct of size and storage pointer *)
      if is_array_type ty then
        let elttype = ttag_to_lltype lltypes (array_element_type ty) in
        struct_type context
          (* get inner type from class params now! *)
          [| int_type; pointer_type (array_type elttype 0) |]
      (* for option, use a (possibly smaller) tag with a struct *)
      else if is_option_type ty then
        let basetype = ttag_to_lltype lltypes (option_base_type ty) in
        struct_type context [| nulltag_type; basetype |]
      else 
        match Lltenv.find_opt
                (tinfo.tclass.in_module, tinfo.tclass.classname) lltypes with
        | None -> failwith ("BUG: no lltype found for "
                            ^ tinfo.tclass.in_module ^ "::"
                            ^ tinfo.tclass.classname)
        (* Get the lltype for each typearg and replace the voidptr with it. *)
        | Some ent -> List.fold_left (fun llty (i, targ) ->
            match targ with
            | Typevar _ -> llty
            (* entry is the same for every loop? Yeah, it's just a different
               type variable that's being replaced in the lltype. *)
            | Namedtype _ -> specify_gtype ent i (ttag_to_lltype lltypes targ)
          ) ent.lltype (List.mapi (fun i a -> (i, a)) tinfo.typeargs)
    )


(** Wrap a value in an outer type. Used for assigning, passing or
    returning a value for a nullable (Option) type *)
let promote_value the_val outertype builder =
  debug_print ("#CG: promote_value " ^ string_of_lltype (type_of the_val)
               ^ " to type " ^ string_of_lltype outertype);
  (* so far, promotion only to nullable. *)
  (* should put in a new way to check since it's using the lltype now? *)
  (* if not (outertype.nullable) then
    failwith "BUG: can only promote value to nullable type for now"
     else *)
  (* Note that this does allocate the struct type. *)
  let alloca = build_alloca outertype "promotedaddr" builder in
  let tagval =
    (* It seems I can get away with checking just the LLVM type here. *)
    if is_null the_val then const_int nulltag_type 0
      else const_int nulltag_type 1 in
  let tagaddr = build_struct_gep alloca 0 "tagaddr" builder in
  ignore (build_store tagval tagaddr builder);
  (* Only build a store for the value if it's not null. *)
  if not (is_null the_val) then ( 
    let valaddr = build_struct_gep alloca 1 "valaddr" builder in
      ignore (build_store the_val valaddr builder));
  (* Now reload the whole thing for the result. *)
  build_load alloca "promotedval" builder


(** Generate a garbage collected array alloca *)
let build_gc_array_malloc eltType llsize name the_module builder =
  match lookup_function "GC_malloc" the_module with
  | None -> failwith "BUG: GC_malloc llvm function not found"
  | Some llmalloc ->
    let datasize = build_mul llsize (size_of eltType) "malloc_size" builder in
    let dataptr = build_call llmalloc [|datasize|] "mallocbytes" builder in
    build_bitcast dataptr (pointer_type eltType) name builder


let build_gc_malloc eltType name the_module builder =
  match lookup_function "GC_malloc" the_module with
  | None -> failwith "BUG: GC_malloc llvm function not found"
  | Some llmalloc ->
    let dataptr = build_call llmalloc [|size_of eltType|] "mallocbytes" builder
    in
    build_bitcast dataptr (pointer_type eltType) name builder


(** Rewritten equality comparison function for any fixed-size concrete type. *)
let gen_eqcompare val1 val2 valty (* lltypes *) _ builder =
  (* make true and false result blocks at the beginning, for short-circuiting. *)
  let the_function = block_parent (insertion_block builder) in
  (* let true_bb = append_block context "eqcomp_true" the_function in *)
  let false_bb = append_block context "eqcomp_false" the_function in
  let true_bb = insert_block context "eqcomp_true" false_bb in
  (* TESTME: builder's insertion point is still before the new blocks? *)
  let rec cmp_walk val1 val2 valty done_bb =
    (* First, check indirection and possible pointer equality. *)
    (* A fixed-size type will never be pointed more than once, right? *)
    let val1, val2 = match classify_type (type_of val1),
                           classify_type (type_of val2) with
    | TypeKind.Pointer, TypeKind.Pointer -> 
      (* if both pointers and the same, we can stop. *)
      let pointereq = build_icmp Icmp.Eq val1 val2 "pointereq" builder in
      (* builder won't move to the inserted block, will it? *)
      let next_bb = insert_block context "eqcomp_next" done_bb in
      (* branch to true or next *) 
      ignore (build_cond_br pointereq done_bb next_bb builder);
      (* move builder to start of next block *)
      position_at_end next_bb builder;
      (* loads for new val1 and val2 *)
      (build_load val1 "val1load" builder,
       build_load val2 "val2load" builder)
    | TypeKind.Pointer, _ ->
      (build_load val1 "val1load" builder, val2)
    | _, TypeKind.Pointer ->
      (val1, build_load val2 "val2load" builder)
    | _, _ -> (val1, val2)
    in
    (* let cmp_res = *) match classify_type (type_of val1) with
    | TypeKind.Integer ->
      let res = build_icmp Icmp.Eq val1 val2 "int_eq" builder in
      ignore (build_cond_br res done_bb false_bb builder);
    | TypeKind.Double ->
      let res = build_fcmp Fcmp.Oeq val1 val2 "float_eq" builder in
      ignore (build_cond_br res done_bb false_bb builder);
    | _ ->
      if is_struct_type valty then
        let fields = get_struct_fields valty in
        let rec fields_loop i =
          (* No extractvalue needed if I just load from the gep pointer? *)
          (* let field1ref = build_struct_gep val1 i "f1ptr" builder in
               let field2ref = build_struct_gep val2 i "f2ptr" builder in *)
          (* but will it be double-pointed if a pointer?
               Trying just extracting always *)
          let fval1 = build_extractvalue val1 i "fval1" builder in
          let fval2 = build_extractvalue val2 i "fval2" builder in
          let fieldtype = (List.nth fields i).fieldtype in 
          let next_bb = if i < List.length fields - 1
            then insert_block context "fieldcmp" done_bb
            else done_bb in
          cmp_walk fval1 fval2 fieldtype next_bb;
          if i < List.length fields - 1 then (
            position_at_end next_bb builder;  (* no-op if at end *)
            fields_loop (i+1)
          )
        in fields_loop 0
      else if is_variant_type valty then
        (* Could check the first field regardless, then if it's a variant type
           insert the cast, then compare as usual! *)
        (* For tuples in variants, may be two different struct types.
           Is it enough just to compare the tag and know other code will
           never be reached? Oh, may have to cast it! Not a generics issue! *)
        (* The issue is, will we ever be loading tuple types that we don't know
           the type of? Wait, even if the tags match, how do I load? *)
        failwith "lemme get back to ya"
      else failwith ("Unexpected type in comparison:  "
                     ^ typetag_to_string valty ^ ", "
                     ^ string_of_lltype (type_of val1) ^ ", "
                     ^ string_of_lltype (type_of val2))
  in
  cmp_walk val1 val2 valty true_bb;
  let phi_block = append_block context "eqcomp_phi" the_function in
  position_at_end true_bb builder;
  ignore (build_br phi_block builder);
  position_at_end false_bb builder;
  ignore (build_br phi_block builder);
  position_at_end phi_block builder;
  let phi = build_phi [(const_int bool_type 1, true_bb);
                       (const_int bool_type 0, false_bb)] "eq_phi" builder in
  debug_print (string_of_llvalue the_function);
  phi

    
(*
(** Generate an equality comparison. This could get complex. *)
let rec gen_eqcomp val1 val2 valty lltypes builder =
  match valty with
  | Typevar _ ->
    failwith "!BUG (codegen): can't compare generic types for equality"
  | Namedtype _ -> 
    if is_struct_type valty then
      let fields = get_struct_fields valty in
    let rec checkloop i prevcmp =
      (* generate next field compare value, generate AND with previous *)
      (* later: optimize to not need to generate a const starting value *)
      if i = List.length fields then
        prevcmp
      else
        (* get the pointer. assume structs are pointers? *)
        let field1val =
          (* I'll have a separate comp for any pointer type, but is this more
           * efficient for a pointer to a struct? *)
          if is_pointer_value val1 then 
            let field1ptr = build_struct_gep val1 i "f1ptr" builder in
            build_load field1ptr "f1val" builder
          else
            build_extractvalue val1 i "f1val" builder in
        let field2val = 
          if is_pointer_value val2 then 
            let field1ptr = build_struct_gep val2 i "f2ptr" builder in
            build_load field1ptr "f2val" builder
          else
            build_extractvalue val2 i "f2val" builder in
        (* might be good to make "fields" an array *)
        let fieldtype = (List.nth fields i).fieldtype in 
        let cmpval = gen_eqcomp field1val field2val fieldtype lltypes builder in
        (* Could using branches so we can short-circuit be faster? *)
        let andval = build_and prevcmp cmpval "cmpand" builder in
        checkloop (i+1) andval
    in
    checkloop 0 (const_int bool_type 1) (* starter true value *)
  else if is_variant_type valty then (
    let variants = get_type_variants valty in
    (* check tag, then load and cast the value tuple if it exists and 
       generate comparison for that. *)
    let var1tag =
      if is_pointer_value val1 then
        let tagPtr = build_struct_gep val1 0 "tag1ptr" builder in
        build_load tagPtr "tag1val" builder
      else
        build_extractvalue val1 0 "tag1val" builder in
    let var2tag =
      if is_pointer_value val2 then
        let tagPtr = build_struct_gep val2 0 "tag2ptr" builder in
        build_load tagPtr "tag2val" builder
      else
        build_extractvalue val2 0 "tag2val" builder in
    if Array.length (struct_element_types (type_of val1)) == 1 then 
      build_icmp Icmp.Eq var1tag var2tag "tagcomp" builder
    else
      (debug_print "variant has values in it, building out compare";
       let start_bb = insertion_block builder in 
       let parent_function = block_parent start_bb in
       (* first "then", if the tag doesn't match *)
       (* let first_then = append_block context "then" parent_function in *)
       let ncases = List.length variants in
       let rec genblocks i =
         if i == 0 then []
         else
           let condblock = append_block context "tagcond" parent_function in
           position_at_end condblock builder; (* needed? *)
           let thenblock =
             append_block context ("tagthen_" ^ Int.to_string i) parent_function in
           position_at_end thenblock builder;
           condblock :: thenblock :: genblocks (i-1)
       in
       let caseblocks = genblocks ncases in
       let cont_block = append_block context "caseeq_cont" parent_function in
       debug_print ("Generated blocks for " ^ Int.to_string ncases ^ " cases.");
       (* avoid nesting: "then" case is if they are unequal, second if it's 0, *)
       position_at_end start_bb builder;
       let tag_eq = build_icmp Icmp.Eq var1tag var2tag "tag_eq" builder in
       ignore (build_cond_br tag_eq (List.hd caseblocks) cont_block builder);
       (* check which variant it is and branch to comparison for that type. *)
       let rec gen_caseblocks caseval blocks =
         match blocks with
         | [] -> []
         | cond_bb :: then_bb :: rest -> (
             position_at_end cond_bb builder;
             (* Oh, it tests in each block whether to go on or match the next *)
           let condval =
             build_icmp Icmp.Eq (const_int varianttag_type caseval) var1tag
               ("tagcmp_" ^ Int.to_string caseval) builder in
           let next_bb = match rest with
             | [] -> cont_block
             | next_bb :: _ -> next_bb in
           ignore (build_cond_br condval then_bb next_bb builder);
           position_at_end then_bb builder;
           (* cast, then compare *)
           let variant = List.nth variants caseval in
           let compval, then_end_bb = 
             match variant with 
             | (_, []) ->
                debug_print ("#CG-eqcomp: no value attached to this case");
                (const_int bool_type 1, then_bb)
             | (_, vttags) ->
               debug_print "#CG-eqcomp: Variant has value(s), generating compare";
               List.iter (fun varty -> ) vttags;
                let llvarty = ttag_to_lltype lltypes varty in
                (* generate the pointer to the variant's value with cast *)
                let gen_varval_ptr theval =
                  let varptr =
                    if is_pointer_value theval then
                      build_struct_gep theval 1 "varptr" builder
                    else
                      (* Easiest way is just to store so we can cast a pointer *)
                      let valalloca =
                        build_alloca (ttag_to_lltype lltypes valty)
                          "varstruct" builder in
                      ignore (build_store theval valalloca builder);
                      build_struct_gep valalloca 1 "varptr" builder
                  in
                  build_bitcast varptr (pointer_type llvarty)
                    "typedvarp" builder
                in 
                let varval1 = gen_varval_ptr val1 in
                let varval2 = gen_varval_ptr val2 in
                let compval = gen_eqcomp varval1 varval2 varty lltypes builder in
                let then_end_bb = insertion_block builder in
                (compval, then_end_bb)
           in
           position_at_end then_end_bb builder;
           ignore (build_br cont_block builder);
           debug_print ("Generated then block for case " ^ Int.to_string caseval);
           (* The condition may jump to the merge block also; add to the phi list *)
           if next_bb == cont_block then
             (condval, cond_bb)
             :: (compval, then_end_bb) :: gen_caseblocks (caseval+1) rest
           else
             (compval, then_end_bb) :: gen_caseblocks (caseval+1) rest)
         | _ :: [] ->
            failwith "BUG: odd number of case blocks"
       in (* end gen_caseblocks *)
       let phiList = 
         (tag_eq, start_bb)
         :: gen_caseblocks 0 caseblocks in
       (* Yay, I get to make a phi! The phi is of all the compare results. *)
       position_at_end cont_block builder;
       debug_print "#CG: building phi value";
       (* I wonder if the error is a bug in if-then? *)
       let phi = build_phi phiList "finalcmp" builder in
       phi
  )) (* end of variant type equality code *)
  else (* primitive type comparisons. check for pointer *)
    let val1 = if is_pointer_value val1 then
                 build_load val1 "val1" builder
               else val1 in
    let val2 = if is_pointer_value val2 then
                 build_load val2 "val2" builder
               else val2 in 
    if (type_of val1) = int_type || (type_of val1) = byte_type then
      build_icmp Icmp.Eq val1 val2 "eqcomp" builder
    else if (type_of val2) = float_type then
      build_fcmp Fcmp.Oeq val1 val2 "eqcomp" builder
    else 
      (* for records, could I just dereference if needed and compare the 
       * array directly? Don't think so in LLVM, that's a vector op. *)
      failwith ("Equality for type " ^ typetag_to_string valty
                ^ ": " ^ string_of_lltype (type_of val1) ^ " not supported yet")
      *)

(** Generate value of a constant expression. Currenly used for global var 
    initializer and case branches *)
let rec gen_constexpr_value lltypes (ex: typetag expr) =
  (* How many types will this support? Might need a tenv later *)
  if ex.decor = int_ttag then
    match ex.e with
    | ExpLiteral (IntVal n) -> const_of_int64 int_type n true
    | ExpUnop (OpNeg, e) -> const_neg (gen_constexpr_value lltypes e)
    | ExpBinop (e1, op, e2) -> (
      let c1 = gen_constexpr_value lltypes e1 in
      let c2 = gen_constexpr_value lltypes e2 in
      match op with (* TODO: make a map for these so don't need the long switch *)
      | OpPlus -> const_add c1 c2
      | OpMinus -> const_sub c1 c2
      | OpTimes -> const_mul c1 c2
      | OpDiv -> const_sdiv c1 c2
      | _ -> failwith "Unimplemented Int const binop"
    )
    | _ -> failwith "Unimplemented Int const expression"
  else if ex.decor = float_ttag then
    match ex.e with
    | ExpLiteral (FloatVal x) -> const_float float_type x
    | ExpUnop (OpNeg, e) -> const_fneg (gen_constexpr_value lltypes e)
    | _ -> failwith "Unimplemented Float const expression"
  else if ex.decor = byte_ttag then
    match ex.e with
    | ExpLiteral (ByteVal c) -> const_int byte_type (int_of_char c)
    | _ -> failwith "Unsupported Byte const expression"
  else if ex.decor = bool_ttag then
    match ex.e with
    | ExpLiteral (BoolVal b) -> const_int bool_type (if b then 1 else 0)
    | _ -> failwith "Unsupported Bool const expression"
  else
    (* struct type *)
    match ex.e with
    | ExpRecord fieldlist -> 
       (* Iterate over the fields and write the value in an llvalue array *)
      let lltype = Lltenv.find_class_lltype (get_type_class ex.decor)
          lltypes in
      let fieldmap = Lltenv.find_class_fieldmap (get_type_class ex.decor)
          lltypes in
      let valarray = Array.make (List.length fieldlist)
          (const_int int_type 0) in
      List.iter (fun (fname, fexp) ->
          let (offset, _) = StrMap.find fname fieldmap in
          let fieldval = gen_constexpr_value lltypes fexp in
          Array.set valarray offset fieldval
        ) fieldlist;
      const_named_struct lltype valarray
    | _ -> failwith "Unimplemented constexpr type"
    

(** Emit array bounds-checking instructions *)
let gen_bounds_check ixval arraysize the_module builder =
  (* Do the compares to zero and the array size *)
  let zerocheck = build_icmp Icmp.Slt
      ixval (const_int int_type 0) "zerobound" builder in
  let sizecheck = build_icmp Icmp.Sge
      ixval arraysize "sizebound" builder in
  let checkres = build_or zerocheck sizecheck "boundcmp" builder in
  (* add all jump targets at once (seems cleaner that way) *)
  let cond_spot = insertion_block builder in
  let this_function = block_parent cond_spot in
  let failblock = append_block context "boundsfail" this_function in
  let okblock = append_block context "boundsok" this_function in
  let contblock = append_block context "boundscont" this_function in
  (* move back and insert the conditional jump *)
  position_at_end cond_spot builder;
  build_cond_br checkres failblock okblock builder |> ignore;
  (* build the fail block *)
  position_at_end failblock builder;
  match lookup_function "exit" the_module with
  | None -> failwith "BUG: could not find exit function"
  | Some exitfunc -> (
      (* Made up failure exit code for array OOB *)
      build_call exitfunc [|const_int int_type 111|] "" builder
      |> ignore;
      build_br contblock builder |> ignore;
      (* build the OK block with just a jump to the continuation *)
      position_at_end okblock builder;
      build_br contblock builder |> ignore;
      position_at_end contblock builder
    )

(** Find the target address of a varexp from symtable entry and
    field type information *)
let rec get_varexp_alloca the_module builder varexp syms lltypes =
  let ((varname, ixs), fields) = varexp in
  debug_print ("#CG: get_varexp_alloca for varexp under var " ^ varname);
  let (entry, _) =  Symtable.findvar varname syms in
  match entry.addr with 
  | None -> failwith ("BUG: get_varexp_alloca: alloca address not present for "
                      ^ entry.symname)
  | Some alloca ->
    (* traverse indices and record fields to generate the final alloca. *)
    let rec field_allocas flds ixs (parentty: typetag) alloca =
      debug_print ("#CG: field_allocas with parent type: "
                    ^ typetag_to_string parentty);
      (* 1. if there are array index expressions [], then load and
         strip off array type *)
      let rec ix_allocas prevalloca parentty ixs = 
        match ixs with
        | [] -> (prevalloca, parentty)
        | ixexpr :: rest ->
          debug_print ("#CG: computing index expression into "
                        ^ string_of_llvalue prevalloca);
          let ixval = gen_expr the_module builder syms lltypes ixexpr in
          (* get the array at index 1. alloca is the address of the struct. *)
          let arraydata = build_struct_gep prevalloca 1 "arraydata" builder in
          (* have to load to get the actual pointer to the llvm array *)
          let dataptr = build_load arraydata "dataptr" builder in
          (* Load the array size to do the bounds check. *)
          let arraysize = build_load
              (build_struct_gep prevalloca 0 "sizeptr" builder)
              "arraysize" builder
          in
          gen_bounds_check ixval arraysize the_module builder;
          (* gep to the 0th element first to "follow the pointer" *)
          let newalloca, newty =
            (build_gep dataptr [|(const_int int_type 0); ixval|]
               "elementtptr" builder,
             (array_element_type parentty)) in
          debug_print ("#CG: index expr alloca: " ^ string_of_llvalue newalloca
                       ^ "\n   type: " ^ typetag_to_string newty);
          ix_allocas newalloca newty rest
      in
      let (alloca, parentty) = ix_allocas alloca parentty ixs in (* newty) = *)
      (* 2. get the field offset if there is one. *)
      match flds with
      | [] -> (alloca, parentty)
      | (fld, ixopt)::rest -> 
        debug_print ("#CG: computing field offset in type: "
                     ^ typetag_to_string parentty);
        (* Get just the class of parent type so we can find its field info.
           Analysis determined it's not a nullable. *)
        (* Would we ever need to get the alloca for a generic (just
           the pointer)? *)
        let ptypekey = (get_type_modulename parentty,
                        get_type_classname parentty) in
        (* If it's the built-in array.length, it has no further fields,
           we're done. *)
        (* the test for = "length" should be redundant. *)
        if (is_array_type parentty) && fld = "length" then
          (build_struct_gep alloca 0 "length" builder, int_ttag)
        else (
          (* check if pointer load needed first, for recursive type. *)
          (* May need to generalize this for generic types too *)
          (* it's always a pointer, don't need to load? *)
          let alloca = if
            (* is_pointer_type (element_type (type_of alloca)) *)
            is_recursive_type parentty
            then 
              build_load alloca "pointed-deref" builder
            else alloca in
          (* Look up field offset in Lltenv, emit gep *)
          let offset, fieldtype = Lltenv.find_field ptypekey fld lltypes in
          let alloca = build_struct_gep alloca offset "field" builder in
          debug_print ("get_varexp_alloca: generated struct gep for '" ^ fld
                       ^ "' for type " ^ string_of_lltype (type_of alloca));
          (*  Get more specific type for field if generic; it becomes the
              parent type for the next iteration *)
          let fieldtype, alloca = 
            match fieldtype with
            | Namedtype _ -> (fieldtype, alloca)
            | Typevar tv ->
              (* Cast generic pointer to specific type pointer *)
              let fieldtype = specify_typevar parentty tv in
              debug_print ("#CG get_varexp_alloca: Specified field type to "
                           ^ typetag_to_string fieldtype);
              (* I guess I'm not adding an extra indirection if it's a pointer
                 type already, so only load if it's not. *)
              (* Don't know if that was the right decision, wherever it
                 was made. *)
              let spec_lltype = ttag_to_lltype lltypes fieldtype in
              let alloca =
                if not (is_pointer_type spec_lltype) then 
                  build_load alloca "generic-load" builder 
                else alloca in
              let alloca = 
                build_bitcast alloca (pointer_type spec_lltype)
                  "generic_cast" builder in
              (fieldtype, alloca) 
          in 
          debug_print "#CG get_varexp_alloca: recursing";
          field_allocas rest ixopt fieldtype alloca )
    in
    (* top-level call *)
    field_allocas fields ixs entry.symtype alloca


(** Generate LLVM code for an expression *)
and gen_expr the_module builder syms lltypes (ex: typetag expr) = 
  match ex.e with
  | ExpLiteral NullVal -> const_int nulltag_type 0 (* maybe used now *)
  | ExpLiteral (IntVal i) -> const_of_int64 int_type i true (* signed *)
  | ExpLiteral (FloatVal f) -> const_float float_type f
  | ExpLiteral (ByteVal c) -> const_int byte_type (int_of_char c)
  | ExpLiteral (BoolVal b) -> const_int bool_type (if b then 1 else 0) 
  | ExpLiteral (StringVal s) ->
    (* It will build the instruction /and/ return the ptr value *)
    build_global_stringptr s "sconst" builder

  | ExpVal (e) ->
    (* val(exp) is the nullable wrapper, so promote to the null-tag container. *)
    let evalue = gen_expr the_module builder syms lltypes e in
    let nullabletype = ttag_to_lltype lltypes ex.decor in 
    promote_value evalue nullabletype builder 

  | ExpVar (((varname, _), _) as varexp) -> (
      (* gets complicated with arrays and fields; call out to helper function *)
      let (alloca, _) =
        get_varexp_alloca the_module builder varexp syms lltypes in
      debug_print ("#CG: ExpVar: varexp alloca created for type "
                   ^ typetag_to_string ex.decor ^ " with alloca "
                   ^ string_of_llvalue alloca);
      let res =
        (* should not load if of generic type! generic02.dl *)
        if not (is_generic_type ex.decor) then 
          build_load alloca (varname ^ "-exp-load") builder 
        else alloca in
      (debug_print "#CG: finished generating VarExp"; res)
    )
  (* prior code to deal with refs was here *)

  | ExpRecord fieldlist ->
    (* Get the LLVM struct type from the lltenv *)
    let typekey = (get_type_modulename ex.decor,
                   get_type_classname ex.decor) in
    let llty = Lltenv.find_lltype typekey lltypes in
    let recaddr =
      (* recursive record types are heap-allocated. *)
      if is_recursive_type ex.decor then
        (* llty is already the pointer type *)
        build_gc_malloc (element_type llty) "rectype" the_module builder
      else 
        build_alloca llty "recaddr" builder in
    List.iter (fun (fname, fexp) ->
        (* have to use the map from field names to numbers *)
        let fexpval = gen_expr the_module builder syms lltypes fexp in
        (* get the pointer to the field from the allocated struct *)
        let fieldptr =
          build_struct_gep recaddr
            (fst (Lltenv.find_field typekey fname lltypes))
            "fieldptr" builder in
        (* check if null promotion is needed; the field lltype might be an opaque
           pointer, so use the typename to fetch the actual type from the lltenv *)
        let fieldtype = element_type (type_of fieldptr) in
        debug_print ("#CG ExpRecord: field and expr types: "
                     ^ string_of_lltype fieldtype ^ ", "
                     ^ string_of_lltype (type_of fexpval));
        let finalval =
          if fieldtype = type_of fexpval
          then fexpval
          else if is_pointer_type fieldtype then (
            (* generic (pointer) field and value is pointer - just cast
               to the void pointer *)
            if is_pointer_type (type_of fexpval) then
              build_bitcast fexpval voidptr_type "genfield" builder
            else (
              (* generic field type and value is value - store *)
              debug_print ("#CG ExpRecord: need store for generic field");
              let fieldaddr =
                build_alloca (type_of fexpval) "fieldaddr" builder in
              let _ = build_store fexpval fieldaddr builder in
              (* cast to the generic pointer *)   
              build_bitcast fieldaddr voidptr_type "fieldarg" builder 
            ))
          (* need a better way to determine when to promote? *)
          else (
            debug_print ("#CG ExpRecord: field value promotion needed");
            promote_value (*castedval*) fexpval fieldtype builder )
        in
        debug_print ("ExpRecord: field value store: " ^ string_of_llvalue
                       (build_store finalval fieldptr builder));
      ) fieldlist;
    (* recursive types return the pointer, otherwise the value *)
    (* I think for consistency: all rectype expressions are pointers. *)
    if is_recursive_type ex.decor then
      recaddr
    else 
      build_load recaddr "recordval" builder


  | ExpVariant (variant, etup) ->
    let tyname = get_type_classname ex.decor in
    let tymod = get_type_modulename ex.decor in
    debug_print ("** Generating variant expression code of type " ^ tyname);
    (* 1. Look up lltype and allocate struct *)
    let tyent = Lltenv.find (tymod, tyname) lltypes in
    (* 2. Look up variant type, allocate struct, store tag value *)
    debug_print ("#CG: variant lltype: " ^ string_of_lltype tyent.lltype);
    let typesize =  (* TODO: have one sizeof function for the whole codegen *)
      if is_pointer_type tyent.lltype then 
        Array.length (struct_element_types (element_type tyent.lltype))
      else 
        Array.length (struct_element_types tyent.lltype)
    in
    debug_print ("#CG: Got variant typesize of " ^ string_of_int typesize);
    let (tagval, subty) = StrMap.find variant tyent.fieldmap in
    let structsubty =
      struct_type context
        (if typesize = 1 || subty = void_ttag
         then [| varianttag_type |]
         else
           let llsubty = ttag_to_lltype lltypes subty in
           [| varianttag_type; llsubty |]
        ) in
    debug_print ("  variant subtype struct: " ^ string_of_lltype structsubty);
    let structaddr =
      if is_recursive_type ex.decor then
        build_gc_malloc structsubty "variantSubAddr" the_module builder 
      else 
        build_alloca structsubty "variantSubAddr" builder
    in 
    let tagaddr = build_struct_gep structaddr 0 "tag" builder in
    ignore (build_store (const_int varianttag_type tagval) tagaddr builder);
    (* 3. generate code for expr (if exists) and store in the value slot *)
    (match etup with
     | [] -> ()   
     | e :: _ ->  (* FIXME: handle the full tuple *)
       (* Think we need to hint this to the variant subtype 
        * (for instance, so "null" will be promoted *)
       let expval =
         let eval1 = gen_expr the_module builder syms lltypes e in
         debug_print "finished codegen for variant field";
         if not (types_equal e.decor subty) then
           let nullabletype = ttag_to_lltype lltypes subty in 
           promote_value eval1 nullabletype builder
         else eval1 in
       let valaddr = build_struct_gep structaddr 1 "varVal" builder in
       ignore (build_store expval valaddr builder)
    );
    (* 4. cast the pointer to the general struct type and load the whole thing *)
    (* It still wants the cast even if no value (because named struct?) *)
    let castedaddr =
      if is_recursive_type ex.decor then
        build_bitcast structaddr tyent.lltype "varstruct" builder
      else
        build_bitcast structaddr (pointer_type tyent.lltype) "varstruct" builder in
    debug_print ("Casted variant struct addr " ^ string_of_llvalue structaddr
                 ^ " ter " ^ string_of_llvalue castedaddr);
    if is_recursive_type ex.decor then
      castedaddr
    else build_load castedaddr "filledVariant" builder
  (* it's stored anyway, so why not just use the pointer? *)
  (* because semantics, and LLVM can elide load/store anyway. *)
  (* castedaddr *)

  | ExpSeq elist ->
    let eltType = ttag_to_lltype lltypes (List.hd elist).decor in
    debug_print ("eltType: " ^ typetag_to_string ((List.hd elist).decor));
    debug_print ("eltType: " ^ string_of_lltype eltType);
    (* alloca for the raw array data. why is it including the  *)
    let datalloca = (* build_array_alloca *) (* build_array_malloc *)
      build_gc_array_malloc eltType
        (const_int int_type (List.length elist)) "arrdata"
        the_module builder in
    List.iteri (fun i e ->
        let v = gen_expr the_module builder syms lltypes e in
        let ep = build_gep datalloca [|const_int int_type i|] "i" builder in
        debug_print(string_of_llvalue (build_store v ep builder));
      ) elist;
    (* create the struct *)
    let structalloca = build_alloca (ttag_to_lltype lltypes ex.decor)
        "array_struct" builder in
    let lenptr = build_struct_gep structalloca 0 "lenptr" builder in
    let dataptr = build_struct_gep structalloca 1 "dataptr" builder in
    debug_print ("(a) " ^ string_of_llvalue dataptr);
    (* cast the 0-length array pointer to the sized type of the data *)
    let dataptr = build_bitcast dataptr (pointer_type (type_of datalloca))
        "arrptr" builder in
    debug_print ("(b) " ^ string_of_llvalue dataptr);
    ignore (build_store (const_int int_type (List.length elist))
              lenptr builder);
    (* this didn't help. *)
    (* let datalloca = build_gep datalloca [| const_int int_type 0 |]
                      "0ptr" builder in *)
    ignore (build_store datalloca dataptr builder);
    build_load structalloca "array_struct" builder


  | ExpUnop (op, e1) -> (
      (* there are const versions of the ops I could try to put in later, 
       * for optimization. *)
      let e1val = gen_expr the_module builder syms lltypes e1 in
      if e1.decor = int_ttag then 
        match op with
        (* type checker should catch negating an unsigned. *)
        | OpNeg -> build_neg e1val "inegated" builder
        | OpBitNot -> build_not e1val "bitnotted" builder
        | _ -> failwith "BUG: Codegen type error in unary op (int)"
      else if e1.decor = float_ttag then
        match op with
        | OpNeg -> build_fneg e1val "fnegated" builder
        | _ -> failwith "BUG: Codegen type error in unary op (float)"
      else if e1.decor = bool_ttag then 
        match op with 
        | OpNot -> build_not e1val "boolnotted" builder
        | _ -> failwith "BUG: Codegen type error in unary op (bool)"
      else
        failwith "BUG: Unknown type in unary op"
    )

  | ExpBinop (e1, op, e2) -> (
      let e1val = gen_expr the_module builder syms lltypes e1 in
      let e2val = gen_expr the_module builder syms lltypes e2 in
      (* TODO: call implemented operator for type. (when we do operators) *)
      if e1.decor = int_ttag then
        match op with
        | OpTimes -> build_mul e1val e2val "imultemp" builder
        | OpDiv -> build_sdiv e1val e2val "sdivtemp" builder
        | OpPlus -> build_add e1val e2val "iaddtemp" builder
        | OpMinus -> build_sub e1val e2val "isubtemp" builder
        | OpMod -> build_srem e1val e2val "modtemp" builder
        | OpEq -> build_icmp Icmp.Eq e1val e2val "ieqtemp" builder
        | OpNe -> build_icmp Icmp.Ne e1val e2val "inetemp" builder
        | OpLt -> build_icmp Icmp.Slt e1val e2val "ilttemp" builder
        | OpGt -> build_icmp Icmp.Sgt e1val e2val "igttemp" builder
        | OpLe -> build_icmp Icmp.Sle e1val e2val "iletemp" builder
        | OpGe -> build_icmp Icmp.Sge e1val e2val "igetemp" builder
        | OpBitAnd -> build_and e1val e2val "andtemp" builder
        | OpBitOr -> build_or e1val e2val "ortemp" builder
        | OpBitXor -> build_xor e1val e2val "xortemp" builder
        | _ -> failwith "int binop Not implemented yet"
      else if e1.decor = float_ttag then
        match op with
        | OpTimes -> build_fmul e1val e2val "fmultemp" builder
        | OpDiv -> build_fdiv e1val e2val "fdivtemp" builder
        | OpPlus -> build_fadd e1val e2val "faddtemp" builder
        | OpMinus -> build_fsub e1val e2val "fsubtemp" builder
        (* | OpEq -> build_fcmp Fcmp.Oeq e1val e2val "feqtemp" builder *)
        | OpLt -> build_fcmp Fcmp.Ult e1val e2val "flttemp" builder
        | OpLe -> build_fcmp Fcmp.Ule e1val e2val "fletemp" builder
        | OpGt -> build_fcmp Fcmp.Ugt e1val e2val "fgttemp" builder
        | OpGe -> build_fcmp Fcmp.Uge e1val e2val "fgetemp" builder
        | _ -> failwith "float binop Not implemented yet"
      else if e1.decor = bool_ttag then
        match op with
        | OpAnd -> build_and e1val e2val "bandtemp" builder
        | OpOr -> build_or e1val e2val "bortemp" builder
        | OpEq -> build_icmp Icmp.Eq e1val e2val "beqtemp" builder
        | OpNe -> build_icmp Icmp.Ne e1val e2val "bnetemp" builder
        | _ -> failwith "BUG: type error in boolean binop"
        (* Try to support equality comparison for everything. *)
      else if op = OpEq then
        gen_eqcompare e1val e2val e1.decor lltypes builder
      else
        failwith "unknown type for binary operation"
    )

  | ExpCall (fname, args) ->
    let (callee, llargs) = 
      gen_call the_module builder syms lltypes (fname, args) in
    let retval = build_call callee llargs "calltmp" builder in
    (* Need to potentially load/cast if function is generic.
       Promotion to nullable taken care of in assignment, because
       that's the only place that can happen? Or have I discovered
       a missing case? *)
    debug_print ("#CG: matching to return type " ^ typetag_to_string ex.decor);
    let rettype = ttag_to_lltype lltypes ex.decor in
    if rettype <> (type_of retval) then
      if is_pointer_type (type_of retval) then
        if is_pointer_type rettype then
          build_bitcast retval rettype "retcast" builder
        else
          let retptr =
            build_bitcast retval (pointer_type rettype) "retcast" builder in
          build_load retptr "retval" builder
      else
        failwith "BUG: expected pointer (generic) type for return val"
        (* but I still have to cast it to the lltype *)
    else retval

  | ExpNullAssn (_, _, _) ->
    failwith "BUG: null assign found outside condition"


(** Generate LLVM for a function call (used in both expr and stmt) *)
and gen_call the_module builder syms lltypes (fname, args) =
  (* 1. Look up function in symtable (names should be unique) *)
  let (fentry, _) = Symtable.findproc fname syms in
  match lookup_function fentry.procname the_module with
  | None -> failwith "BUG: unknown function name in codegen"
  | Some llfunc ->
    (* 2. Construct llvm values for arguments (may cast/store/promote) *)
    (* TODO: get lltypes of params also, for casting *)
    let llargs =
      List.map2 (fun (mut, (argexpr: typetag expr)) fparam ->
          (* TODO: Just eval the argexpr and then determine if
             load/store needed? *) 
          (* 2.a: if mutable, arg must be a varexp; pass the var's address. *)
          if mut then
            match argexpr.e with
            | ExpVar _ -> (   (* (v, vlds) *)
                (* Incomplete--needs to handle field/array expressions. *)
                let varentry, _ =
                  Symtable.findvar (exp_to_string argexpr) syms in
                match varentry.addr with
                | Some alloca ->
                  (* I think this is where I promote. *)
                  (* if varentry.symtype.nullable <> argexpr.decor.nullable then *)
                  if is_option_type argexpr.decor then
                    failwith "Not yet supporting mutable nullable args"
                  else 
                    alloca
                | None -> failwith "BUG: alloca not found for mutable arg"
              )
            | _ -> failwith "BUG: non-var mut argument found in codegen"
          else (
            (* 2.b: If not mutable, just get the llvalue of the expression *)
            debug_print
              "#CG gen_call: generating immutable argument expression";
            let argty = argexpr.decor in
            let paramty = fparam.symtype in
            let argval = gen_expr the_module builder syms lltypes argexpr in
            (* 2.b.1: exact equal types or matching typeclass (no!) *)
            if types_equal argty paramty
            (* but now, is_generic_type detects deeper-buried type variables.
               This will happen only if an exact match. Should we "cast all
               the way down"? *)
            || not (is_generic_type argty)
               && not (is_generic_type paramty)
               && get_type_class argty = get_type_class paramty
            then (
              debug_print ("#CG gen_call: exact or class match argument type"
                           ^ typetag_to_string argty ^ ","
                           ^ typetag_to_string paramty);
              (* Could still be lltype mismatch (AFAIK just due to
                 instantiated generic as argument. But test *)
              if is_pointer_value argval
              && not (is_pointer_type (ttag_to_lltype lltypes paramty))
                 (* else if is_generic_type argty then ( *)
              then (
                (* this can only happen when passing an /instantiated/ generic
                   to a concrete argument of matching type, right? *)
                debug_print "#CG gen_call: generic-to-concrete arg pass";
                let argptr = build_bitcast argval
                    (pointer_type (ttag_to_lltype lltypes paramty))
                    "argptr" builder in 
                build_load argptr "argval" builder
              )
              else 
                argval
            )
            (* Maybe don't check if generic at all here, just pointers
               and casting. *)
            (* 2.b.1: parameter type is generic. *)
            else if is_generic_type paramty then (
              (* case of both generic, just different type variable *)
              if is_generic_type argty then argval
              else (
                if is_pointer_type (type_of argval) then (
                  debug_print "#CG gen_call: casting pointer to generic arg";
                  build_bitcast argval voidptr_type "genarg" builder
                ) else (
                  debug_print "#CG gen_call: storing value for generic arg";
                  let argaddr =
                    build_alloca (type_of argval) "argaddr" builder in
                  let _ = build_store argval argaddr builder in 
                  build_bitcast argaddr voidptr_type "genarg" builder
                )))
            (* Remaining case is union/nullable type; promote value *)
            else (
              debug_print "#CG gen_call: promoting arg value to nullable";
              let nullabletype = ttag_to_lltype lltypes fparam.symtype in
              promote_value argval nullabletype builder ))
        ) args fentry.fparams
      |> Array.of_list in
    (llfunc, llargs) (* actual build is different if expr or stmt *)


(** Generate LLVM code for a statement *)
let rec gen_stmt the_module builder lltypes
    (stmt: (typetag, 'a st_node, 'tt) stmt) =
  let syms = stmt.decor in
  match stmt.st with
  | StmtDecl (varname, _, eopt) -> (
    (* technically, decl should only lookup in this scope. 
     * But we don't care in codegen, right, it's all correct? *)
    (* print_string ("looking up " ^ varname ^ " for decl codegen\n"); *)
    let (entry, _) = Symtable.findvar varname syms in
    let allocatype = ttag_to_lltype lltypes entry.symtype in
    debug_print("StmtDecl: allocatype for decl of " ^ varname ^ ": "
                ^ string_of_lltype allocatype);
    (* Make a separate builder to insert the alloca at top of the function *)
    (* would like to put it at the end, before the terminator, but didn't
       figure that out yet *)
    let declpos = builder_at context
        (instr_begin (entry_block (block_parent (insertion_block builder)))) in
    (* at end didn't work, it was after the terminator *)
    (* let declpos = builder_at_end context
        (entry_block (block_parent (insertion_block builder))) in *)
    let alloca =
      build_alloca allocatype varname declpos in 
    Symtable.set_addr syms varname alloca;
    match eopt with
    | None -> ()
    | Some initexp ->
       (* desugar to an assignment statement to avoid code duplication. *)
       gen_stmt the_module builder lltypes
         {st=StmtAssign (((varname, []), []), initexp); decor=syms}
  )

  | StmtAssign (varexp, ex) -> (
    let alloca, vetype =
      get_varexp_alloca the_module builder varexp syms lltypes in
    debug_print ("StmtAssign lvalue addr: " ^ string_of_llvalue alloca);
    let expval = gen_expr the_module builder syms lltypes ex in
    debug_print ("StmtAssign: Generated RHS expr: " ^ string_of_lltype (type_of expval));
    debug_print ("StmtAssign: Alloca type: " ^ string_of_lltype (type_of alloca));
    (* cases to handle nullable types and pointer casts *)
    if is_option_type vetype = is_option_type ex.decor then
      (* indirection level is the same, so just directly assign the value *)
      debug_print ("StmtAssign store: "
                   ^ string_of_llvalue (build_store expval alloca builder))
    else (
      (* will have to handle pointer types too for record type? yes. *)
      debug_print "StmtAssign: null promotion seemingly required";
      let nullabletype = ttag_to_lltype lltypes vetype in 
      let promotedval = promote_value expval nullabletype builder in
      ignore (build_store promotedval alloca builder) )
  )

  | StmtNop -> () (* will I need to generate so labels work? *)

  | StmtReturn eopt -> (
    (match eopt with
     | None -> ignore (build_ret_void builder)
     | Some rexp ->
       (* Could I find the llvm function itself and use just lltype info? *)
       let rettype =
         (Option.get stmt.decor.in_proc).rettype in
        let expval =
          let ev = gen_expr the_module builder syms lltypes rexp in
          if rexp.decor = rettype then ev
          (* need to wrap the value if it's a (nullable) subtype. *)
          else (
            debug_print ("StmtReturn: Promoting return value "
                         ^ Llvm.string_of_llvalue ev);
            let supertype = ttag_to_lltype lltypes rettype in 
            promote_value ev supertype builder  )
        in
        let retval =
          (* If type is opaque, need to return a void pointer. *)
          if is_opaque_type rettype then
            (debug_print ("-- Generating opaque return value for " ^ exp_to_string rexp);
             let retvalAddr =
               (* TODO: detect if it's already stored on the heap. How? *)
               build_gc_malloc (type_of expval) "retvalAddr" the_module builder in
             ignore (build_store expval retvalAddr builder);
             build_bitcast retvalAddr voidptr_type "retvalAddr_void" builder)
            (* what if value is already a pointer? will I double-point it? *)
          else expval in
        debug_print (string_of_llvalue retval);
        ignore (build_ret retval builder)
    );
    (* Add a basic block after in case a break is added afterwards. *)
    let this_function =
      Option.get (lookup_function
                    (Option.get syms.in_proc).procname the_module) in
    let retcont_bb = append_block context "retcont" this_function in
    position_at_end retcont_bb builder;
  )

  | StmtIf (cond, thenblock, elsifs, elsopt) -> (
    (* Evaluate a condition, possibly inserting declaration and value store 
     * in the then block for conditional-null assignments. *)
    let start_bb = insertion_block builder in
    let the_function = block_parent start_bb in
    let then_bb = append_block context "then" the_function in
    let blocksyms = (List.hd thenblock).decor in
    position_at_end start_bb builder;
    let condval =
      gen_cond the_module syms lltypes cond then_bb blocksyms builder in
    (* need this because a (variant) comparison in the cond can add bb's *)
    let new_start_bb = insertion_block builder in 
    position_at_end then_bb builder;
    List.iter (gen_stmt the_module builder lltypes) thenblock;
    (* code insertion could add new blocks to the "then" block. *)
    let new_then_bb = insertion_block builder in
    (* elsif generating code *)
    let gen_elsif (cond, (block: (typetag, 'b, 'tt) stmt list)) =
      (* however, need to insert conditional jump and jump-to-merge later *)
      let cond_bb = append_block context "elsifcond" the_function in
      position_at_end cond_bb builder;
      let then_bb = append_block context "elsifthen" the_function in
      let blocksyms = (List.hd block).decor in
      let condval =
        gen_cond the_module syms lltypes cond then_bb blocksyms builder in
      position_at_end then_bb builder;
      List.iter (gen_stmt the_module builder lltypes) block;
      (condval, cond_bb, then_bb, insertion_block builder) (* for jumps *)
    in
    let elsif_blocks = List.map gen_elsif elsifs in
    (* generating dummy else block regardless. *)
    let else_bb = append_block context "else" the_function in
    position_at_end else_bb builder;
    (match elsopt with
     | Some elseblock ->
        List.iter (gen_stmt the_module builder lltypes) elseblock
     | None -> ());
    (* position at end of else block. *)
    let new_else_bb = insertion_block builder in
    let merge_bb = append_block context "ifcont" the_function in
    (* Still loop to the /original/ then block! *)
    let firstelse =
      match elsif_blocks with
      | [] -> else_bb
      | (_, condblk, _, _) :: _ -> condblk in
    (* Way down here, we finally build the top branch. *)
    position_at_end new_start_bb builder;
    ignore (build_cond_br condval then_bb firstelse builder);
    position_at_end new_then_bb builder;
    ignore (build_br merge_bb builder);
    (* Add conditional and unconditional jumps between elsif blocks 
     * (the blocks had to be created first) *)
    let rec add_elsif_jumps = function
      | [] -> ()
      | (condval, condblk, thenblk, endblk) :: rest ->
         position_at_end condblk builder;
         (match rest with
          | [] ->
             ignore (build_cond_br condval thenblk else_bb builder);
          | (_, nextblk, _, _) :: _ -> 
             ignore (build_cond_br condval thenblk nextblk builder);
         );
         position_at_end endblk builder;
         ignore (build_br merge_bb builder);
         add_elsif_jumps rest
    in 
    add_elsif_jumps elsif_blocks;
    position_at_end new_else_bb builder;
    ignore (build_br merge_bb builder);
    position_at_end merge_bb builder
  )

  | StmtCase (matchexp, cblocks, elseopt) -> (
    debug_print "** Generating case statement";
    let start_bb = insertion_block builder in
    let the_function = block_parent start_bb in
    (* generate value of the expression to match (the top one) *)
    (* testing if pointer here and loading seems to fix things. *)
    let matchval =
      let mv = gen_expr the_module builder syms lltypes matchexp in
      if is_pointer_value mv then
        build_load mv "matchval" builder
      else mv in
    (* Need to store the match val also, to have the pointer  *)
    (* TODO: optimize to omit this if it's an enum-only variant *)
    (* TODO: it's an extra load/store if it's a pointer - optimize? *)
    let matchaddr =
      build_alloca (type_of matchval) "matchaddr" builder in
    ignore (build_store matchval matchaddr builder);
    let fieldmap =
      match PairMap.find_opt (get_type_modulename matchexp.decor,
                              get_type_classname matchexp.decor) lltypes with
      | None -> None
      | Some tyent -> Some tyent.fieldmap in
    (* Get the conditional value for matching against the case. *)
    let gen_caseexp caseexp =
      match caseexp.e with
      | ExpVariant (vname, _) ->
        debug_print ("Generating case comparison on "
                     ^ string_of_llvalue matchval);
         (* only compare the tags; the load of the value into the
            variable is done in the block body *)
        let matchtagval = build_extractvalue matchval 0 "matchtag" builder in 
        let fieldmap = Option.get fieldmap in
        (* compare tag value of case to tag of the matchval *)
        let casetag = fst (StrMap.find vname fieldmap) in
        debug_print ("Comparing case tag " ^ string_of_int casetag
                     ^ " with value tag" ^ string_of_llvalue matchtagval);
        build_icmp
          Icmp.Eq (const_int varianttag_type casetag) matchtagval
          "casecomp" builder
      | ExpVal {e=ExpVar(_, _); decor=_} ->
         (* 'val(x)' matches whenever the tag value is 1 (non-null) *)
         let matchtagval = build_extractvalue matchval 0 "matchtag" builder in
         build_icmp
           Icmp.Eq (const_int nulltag_type 1) matchtagval
           "valcomp" builder
      | ExpLiteral NullVal ->
         let matchtagval = build_extractvalue matchval 0 "matchtag" builder in
         build_icmp
           Icmp.Eq (const_int nulltag_type 0) matchtagval
           "nullcomp" builder
      (* other value types. *)
      | _ ->
         let caseval = gen_constexpr_value lltypes caseexp in
           (* gen_expr the_module builder syms lltypes caseexp in *)
         (* maybe a gen_compare? *)
         gen_eqcompare matchval caseval matchexp.decor lltypes builder
         (* what if it's an ExpCall? Have to see if return value is nullable *)
         (* expCall's decor is the return type, right? *)
         (* don't need to worry about this as long as they're constexprs? *)
    in
    (* generate compare and block code, return the block pointers for jumps *)
    let gen_caseblock caseexp (caseblock: ('ed,'sd,'tt) stmt list) =
      (* however, need to insert conditional jump and jump-to-merge later *)
      let comp_bb = append_block context "casecomp" the_function in
      position_at_end comp_bb builder;
      let blocksyms = (List.hd caseblock).decor in
      debug_print ("case block symtable: " ^ st_node_to_string blocksyms);
      let condval = gen_caseexp caseexp (* casebody_bb blocksyms *) in
      let casebody_bb = append_block context "casebody" the_function in
      (* Need the syms for the variable that's declared to hold the value *)
      position_at_end casebody_bb builder;
      (* If variant holds a value, create alloca and load value *)
      (match caseexp.e with
       | ExpVariant (vname, valvar::_) -> (  (* FIXME: handle rest *)
         match valvar.e with
         | ExpVar ((varname, _), _) -> 
            let fieldmap = Option.get fieldmap in
            let casetype = snd (StrMap.find vname fieldmap) in
            let caselltype = ttag_to_lltype lltypes casetype in
            (* trying with no new alloca, just cast and return the pointer. *)
            (* let alloca = build_alloca caselltype varname builder in
            Symtable.set_addr blocksyms varname alloca; *)
            let varstructty =
              (struct_type context [| varianttag_type; caselltype |]) in
            (* cast the match value to the specific struct type. *)
            let structptr =
              build_bitcast matchaddr (pointer_type varstructty)
                "structptr" builder in
            let valptr = build_struct_gep structptr 1 "valptr" builder in
            (* debug_print (string_of_llvalue structptr); *)
            (* load the value from the struct and store in the variable. *)
            (* Wait! If it's mutable don't I need to just make it the same
               pointer instead? but if it's mutable won't it be a pointer
               type already? Not local records! ok, trying it... *)
            (* let caseval = build_load valptr "caseval" builder in 
            ignore (build_store caseval alloca builder) *)
            Symtable.set_addr blocksyms varname valptr; 
         | _ -> failwith "Shouldn't happen: no ExpVar in case"
       )
       | ExpVal({e=ExpVar((valvar, _), _); decor=_}) ->
          (* let valtype = {matchexp.decor with nullable=false} in
          let vallltype = ttag_to_lltype lltypes valtype in  *)
          (* let alloca = build_alloca vallltype valvar builder in 
          Symtable.set_addr blocksyms valvar alloca; *)
          (* let varstructty =
            (struct_type context [| nulltag_type; vallltype |]) in *)
          (* trying what I asked about above; just get the pointer *)
          let valptr = build_struct_gep matchaddr 1 "valptr" builder in
          Symtable.set_addr blocksyms valvar valptr;
       | _ ->
          (* case doesn't set a variable, just emit the body *)
          ()
      );
      List.iter (gen_stmt the_module builder lltypes) caseblock;
      (condval, comp_bb, casebody_bb, insertion_block builder)
    in
    let caseblocks = List.map (fun (ce, cb) -> gen_caseblock ce cb) cblocks in
    (* generate jump into first case comparison *)
    let firstcomp_bb = match (List.hd caseblocks) with
      | (_, compblk, _, _) -> compblk in
    position_at_end start_bb builder;
    ignore (build_br firstcomp_bb builder);
    (* generating dummy else block regardless. *)
    let else_bb = append_block context "else" the_function in
    position_at_end else_bb builder;
    (match elseopt with
     | Some elseblock ->
        List.iter (gen_stmt the_module builder lltypes) elseblock
     | None -> ());
    let new_else_bb = insertion_block builder in
    let merge_bb = append_block context "casecont" the_function in
    let rec add_block_jumps = function
      | [] -> ()
      | (condval, condblk, bodyblk, endblk) :: rest ->
         position_at_end condblk builder;
         (match rest with
          | [] ->
             ignore (build_cond_br condval bodyblk else_bb builder);
          | (_, nextblk, _, _) :: _ -> 
             ignore (build_cond_br condval bodyblk nextblk builder);
         );
         position_at_end endblk builder;
         ignore (build_br merge_bb builder);
         add_block_jumps rest
    in 
    add_block_jumps caseblocks;
    position_at_end new_else_bb builder;
    ignore (build_br merge_bb builder);
    position_at_end merge_bb builder
  )

  | StmtWhile (cond, body) -> (
    (* test block, loop block, afterloop block. *)
    let the_function = block_parent (insertion_block builder) in 
    let test_bb = append_block context "test" the_function in
    (* jump from current block into this one *)
    ignore (build_br test_bb builder);
    (* insert code in test block to compute condition (put test in later) *)
    let loop_bb = append_block context "loop" the_function in
    let blocksyms = (List.hd body).decor in
    position_at_end test_bb builder;
    let condval =
      gen_cond the_module syms lltypes cond loop_bb blocksyms builder in
    (* Create loop block and fill it in *)
    position_at_end loop_bb builder;
    List.iter (gen_stmt the_module builder lltypes) body;
    (* add unconditional jump back to test *)
    let end_loop_bb = insertion_block builder in 
    position_at_end end_loop_bb builder;
    ignore (build_br test_bb builder);
    let merge_bb = append_block context "afterloop" the_function in
    (* Now, add the conditional branch in the test block. *)
    position_at_end test_bb builder;
    ignore (build_cond_br condval loop_bb merge_bb builder);
    position_at_end merge_bb builder
  )
  
  | StmtCall {decor=_; e=ExpCall (fname, args)} ->
    debug_print "StmtCall: entering...";
    let (callee, llargs) = 
      gen_call the_module builder syms lltypes (fname, args) in
    debug_print "#CG StmtCall: generated argument llvalues.";
    (* Call as a statement; return value ignored *)
    ignore (build_call callee llargs "" builder)
      
  | StmtCall _ -> failwith "BUG: StmtCall without CallExpr"
(*  | StmtBlock _ -> failwith "nested block codegen not implemented" *)


(** Generate code for a conditional expression, including possibly null assignment *)
and gen_cond the_module syms lltypes cond thenbb blocksyms builder =
  match cond.e with
  | ExpNullAssn (isdecl, (((varname, _), _) as varexp), nullexp) ->
    let condval = gen_expr the_module builder syms lltypes nullexp in
    let nulltag = build_extractvalue condval 0 "nulltag" builder in
    (* Need an icmp instruction because tag value isn't i1 anymore. *)
    let condres =
      build_icmp Icmp.Ne
        nulltag (const_int nulltag_type 0) "condres" builder in
    (* need to save start_bb's position before adding code to 
            the then block *)
    let start_block = insertion_block builder in
    position_at_end thenbb builder;
    (* desugar a new declaration if needed, then generate code
          * to store the non-null condition result value *)
    if isdecl then
      gen_stmt the_module builder lltypes 
        { st=StmtDecl (varname, None, None); decor=blocksyms };
    let (alloca, _) =
      get_varexp_alloca the_module builder varexp blocksyms lltypes in
    let realval = build_extractvalue condval 1 "condval" builder in
    (* build_load valaddr "realval" builder in *)
    ignore (build_store realval alloca builder);
    (* restore the insertion point to the end of start_bb *)
    position_at_end start_block builder;
    condres
  | _ ->
    let condval = gen_expr the_module builder syms lltypes cond in
    (* If a nullable type, then the condition is to test if it's null *)
    if is_option_type cond.decor then
      let nulltag = build_extractvalue condval 0 "nulltag" builder in
      build_icmp Icmp.Ne
        nulltag (const_int nulltag_type 0) "condres" builder
    else condval

(* 
(** Get a default value for a type. Seems to be needed for unreachable 
  * returns and empty union (nullable) fields. *)
let default_value ttag =
  (* I'll need some kind of ttag->llvm type mapping eventually. *)
  if ttag = int_ttag then const_int int_type 0
  else if ttag = float_ttag then const_float float_type 0.0
  else if ttag = bool_ttag then const_int bool_type 0
  else const_int int_type 0 (* Could we use this for all? *)
  (* else failwith ("Cannot generate default value for type "
                 ^ typetag_to_string ttag) *)
 *)

(** Generate code for a global variable declaration (and constant initializer,
    for now) *)
let gen_global_decl the_module lltypes (gdecl: ('ed,'sd,'tt) globalstmt) =
  let syms = gdecl.decor in
  match gdecl.init with
  | Some ex ->
     let symname = (fst (Symtable.findvar gdecl.varname syms)).symname in
     let gaddr =
       define_global
         symname (gen_constexpr_value lltypes ex) the_module in
     Symtable.set_addr syms gdecl.varname gaddr;
  | None -> failwith "Shouldn't happen, global checked for initializer"


(** Generate llvm function decls for a set of proc symtable entries. *)
(* Used for both locals and imported functions. *)
let gen_fdecls the_module lltypes fsyms =
  StrMap.iter (fun _ procentry ->  (* don't need map keys *)
      let rettype =
        let rawRetType = ttag_to_lltype lltypes procentry.rettype in
        if is_opaque_type procentry.rettype then (
          debug_print ("#CG gen_fdecls: Generating opaque return type for "
                       ^ string_of_lltype rawRetType);
          voidptr_type
        )
        else rawRetType in
      let paramtypes =
        List.map (fun entry ->
            let ptype = ttag_to_lltype lltypes entry.symtype in
            (* if entry.symtype.tclass.opaque then
               voidptr_type *)
            (* if is_primitive_type entry.symtype then ptype
            else pointer_type ptype *) (* simplifying try *)
            (* make it the pointer type if it's passed mutable *)
            if entry.mut then
              if is_option_type entry.symtype then
                (* If nullable we want a nullable pointer to the inner type. *)
                struct_type context [|
                    nulltag_type;
                    pointer_type (Lltenv.find_class_lltype
                                    (get_type_class entry.symtype) lltypes)
                  |]
              else
                pointer_type ptype
            else ptype
          ) procentry.fparams
        |> Array.of_list in
      let llfunctype = function_type rettype paramtypes in
      debug_print ("#CG gen_fdecls: Declaring function " ^ procentry.procname
                   ^ ", of type " ^ string_of_lltype llfunctype);
      (* This is the qualified version (or not, if exported) *)
      (* let llfunc = ( *)
      declare_function procentry.procname llfunctype the_module
      |> ignore
      (* print_endline (string_of_llvalue llfunc) *)
    (* We could set names for arguments here. *)
    ) fsyms  (* returns () *)


(** generate code for a procedure body (its declaration should already
 * be defined) *)
let gen_proc the_module builder lltypes proc =
  let fname = proc.decl.name in
  (* procedure is now defined in its own scope, so "getproc" *)
  let fentry = Symtable.getproc fname proc.decor in 
  match lookup_function fentry.procname the_module with
  | None -> failwith "BUG: llvm function lookup failed"
  | Some llfunc -> 
     (* should I define_function here, not add to the existing decl? *)
     let entry_bb = append_block context "entry" llfunc in
     position_at_end entry_bb builder;
     (* Set address of all arguments in symbol table, creating a new 
      * alloca for things passed by value *)
     List.iteri (fun i (_, varname, _) ->
         let entrybuilder =
           builder_at context (instr_begin (entry_block llfunc)) in
         let is_pointer_arg = is_pointer_value (param llfunc i) in
         let alloca =
           (* trying to lower this to just "is pointer" *)
           if is_pointer_arg then
             let paramentry = List.nth (fentry.fparams) i
             (* cast to the specific object pointer type if it's opaque but known type *)
             (* possibly cannot be done with just llvm info *)
             in if is_opaque_type paramentry.symtype
                && (get_type_class paramentry.symtype).kindData <> Hidden then ( 
               debug_print ("-- Casting opaque argument " ^ varname ^ " to concrete type");
               build_bitcast (param llfunc i)
                 (pointer_type (ttag_to_lltype lltypes paramentry.symtype))
                 varname entrybuilder
             )
             else param llfunc i
           else (build_alloca (type_of (param llfunc i)) varname entrybuilder)
         in
         if not is_pointer_arg then 
           ignore (build_store (param llfunc i) alloca builder);
         Symtable.set_addr proc.decor varname alloca
       ) proc.decl.params;
     List.iter (gen_stmt the_module builder lltypes) (proc.body);
     (* If procecure doesn't end in a terminator, add a void or dummy return *)
     if Option.is_none (block_terminator (insertion_block builder)) then
       (* Checking the LLVM type didn't work, why? *)
       (* if return_type (type_of llfunc) = void_type then ( *)
       if fentry.rettype = void_ttag then ( 
         ignore (build_ret_void builder);
         (* if !_debug then Llvm_analysis.view_function_cfg llfunc; *)
         Llvm_analysis.assert_valid_function llfunc 
       )
       else (
         (* dummy return, for unreachable code such as after ifs where all
          * branches return *)
         let dummyRetval =
           (* at the LLVM level doesn't work here either. Why?
              Seems like return_type includes too much information *)
           (* (const_null (return_type (type_of llfunc))) *)
           if is_opaque_type fentry.rettype then
             (* WAT! It works if I call it twice? *)
             const_null (return_type (return_type (type_of llfunc)))
           else const_null  (ttag_to_lltype lltypes fentry.rettype) in
         ignore (build_ret dummyRetval builder);
           (* ignore (build_ret (default_value fentry.rettype) builder); *)
         Llvm_analysis.assert_valid_function llfunc
       )


(** Generate LLVM code for an analyzed module. *)
let gen_module tenv topsyms llmod
    (modtree: (typetag, 'a st_node, _) dillmodule) =
  (* let llmod = create_module context (modtree.name ^ ".ll") in *)
  (* Llvm.set_target_triple ttriple the_module; *)
  (* Llvm.set_data_layout (Llvm_target.DataLayout.as_string layout) the_module; *)
  let layout = Llvm_target.DataLayout.of_string (data_layout llmod) in
  let builder = builder context in
  (* 1. Generate dict of llvm types from the tenv (imports are added
     to it by the analyzer.) *)
  let lltypes =
    PairMap.fold (fun _ cdata lltenv ->
        (* fully-qualified typename now *)
        let newkey = (cdata.in_module, cdata.classname) in
        (* note that lltydata is a pair type. *)
        let tyent = add_lltype llmod tenv lltenv layout cdata
        in
        debug_print (
            "adding type " ^ (fst newkey) ^ "::" ^ (snd newkey)
            ^ " to lltenv, lltype: " ^ string_of_lltype tyent.lltype);
        Lltenv.add newkey tyent lltenv
      ) tenv Lltenv.empty in
  (* 2. Generate decls from the symtable for imported global variables. *)
  StrMap.iter (fun localname gsym ->
      let gvalue = declare_global
                     (ttag_to_lltype lltypes gsym.symtype)
                     gsym.symname
                     llmod in
      set_externally_initialized true gvalue;
      (* Name maybe not correct? Need the local name of it. *)
      Symtable.set_addr topsyms localname gvalue
    ) topsyms.syms;
  (* 2.5 Generate low-level function declarations (GC alloc and exit) *)
  declare_function "GC_malloc"
    (function_type (pointer_type byte_type) [|int64_type|]) llmod
  |> ignore ;
  declare_function "exit"
    (function_type void_type [|int_type|]) llmod |> ignore;
  (* 3. Generate decls for imported functions (already in root node.) *)
  gen_fdecls llmod lltypes topsyms.fsyms;
  (* if List.length (topsyms.children) <> 1 then
     failwith "BUG: didn't find unique module-level symtable"; *)
  (* 4. Generate decls for this module's global variables. *)
  (* The next symtable node underneath holds this module's proc declarations *)
  let modsyms = List.hd (topsyms.children) in
  List.iter (gen_global_decl llmod lltypes) modtree.globals;
  (* 5. Generate this module's procedure declarations (all at once, so
     they can mutually refer) *)
  gen_fdecls llmod lltypes modsyms.fsyms;
  (* 6. Generate each of the procedures. *)
  List.iter (gen_proc llmod builder lltypes) modtree.procs;
  Llvm_analysis.assert_valid_module llmod;
  (* llmod *)
