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
let int_type = i64_type context
let int32_type = i32_type context
let bool_type = i1_type context
let byte_type = i8_type context
let void_type = void_type context
(* LLVM doesn't like pointers to void, use this for polymorphic ptrs *)
let voidptr_type = pointer_type (i8_type context) 
let nulltag_type = i8_type context
let varianttag_type = i32_type context

let is_pointer_value llval = classify_type (type_of llval) = TypeKind.Pointer

(* Implement comparison for typetag so we can make a map of them. *)
(* Note: haven't done this yet, still using the string pair for basetype *)
module TypeTag = struct
  type t = typetag
  let compare t1 t2 =
    String.compare (typetag_to_string t1) (typetag_to_string t2)
end

module TtagMap = Map.Make(TypeTag)

(* dressed-up type environment to store lltype + field/tag offsets. *)
module Lltenv = struct
  (* fieldmap is used for both struct offsets and union tags. *)
  type fieldmap = (int * typetag) StrMap.t
  (* Maps modulename, typename pair to the LLVM type and field map. *)
  type t = (lltype * fieldmap) TypeMap.t  
  let empty: t = TypeMap.empty
  let add strpair (llvarty, fmap) map = TypeMap.add strpair (llvarty, fmap) map
  (* Can I have a function to take a typetag and pull in_module and
     classname out of that, so I don't have to awkwardly pass pairs?
     Yes, could, but REMEMBER: the LLtenv is only used for looking up
     *classes*.  Array and nullable types are generated at the point
     of use. *)
  (* Return just the LLVM type for a given type name. *)
  let find_lltype tkey tmap = fst (TypeMap.find tkey tmap)
  (* Look up the base typename for a class. *)
  let find_lltype_opt tkey tmap =
    Option.map fst (TypeMap.find_opt tkey tmap)
  let find_class_lltype tclass tmap =
    fst (TypeMap.find (tclass.in_module, tclass.classname) tmap)
  (* Get the mapping of fields to types for a struct type. *)
  let find_class_fieldmap tclass tmap =
    snd (TypeMap.find (tclass.in_module, tclass.classname) tmap)
  (* Get the offset of a record field from a type's field map. *)
  let find_field tkey fieldname tmap =
    let (_, fmap) = TypeMap.find tkey tmap in
    StrMap.find fieldname fmap
end

(** Process a classData to generate a new llvm base type *)
let rec gen_lltype context
    (types: classData TypeMap.t) (lltypes: Lltenv.t) layout (cdata: classData) =
  debug_print ("Generating lltype for " ^ cdata.classname);
  match (cdata.in_module, cdata.classname) with
  (* need special case for primitive types. Should handle this with some
   * data structure, so it's consistent among modules *)
  | ("", "Void") -> void_type, StrMap.empty
  | ("", "Int") -> int_type, StrMap.empty
  | ("", "Float") -> float_type, StrMap.empty
  | ("", "Byte") -> byte_type, StrMap.empty                                   
  | ("", "Bool") -> bool_type, StrMap.empty
  | ("", "String") -> pointer_type (i8_type context), StrMap.empty
  | ("", "NullType") -> nulltag_type, StrMap.empty (* causes crash? *) 
  | _ ->
    (* Process non-primitive type *)
    (* make a list of names/types for either struct or variant fields. *)
    let fielddata =
      match cdata.kindData with
      | Struct fields ->
        (* mutability info about struct fields not needed for codegen) *)
        List.map (fun fi -> (fi.fieldname, Some fi.fieldtype)) fields
      | Variant vts -> vts
      | _ -> []
    in 
    (* Generate list of (name, lltype, offset, type) from fields *)
    let ftypeinfo =
      List.mapi (fun i (fieldname, ftyopt) ->
          match ftyopt with
          (* why would this ever be none? *)
          | None -> (fieldname, void_type, i, void_ttag)
          | Some fty -> (
              let mname, tname = fty.modulename, fty.typename in
              let basetype = match Lltenv.find_lltype_opt
                                     (mname, tname) lltypes with
              | Some basetype -> basetype
              (* In case the field's lltype isn't generated yet, either recurse
                 or just add a pointer if it's recursive *)
              | None ->
                if fty.tclass.rectype then (
                  (* I think this is enough here; but at the end I must have
                     a pointer type for the whole struct *)
                  debug_print "generating untyped pointer for recursive field";
                  voidptr_type )
                else 
                  fst (gen_lltype context types lltypes layout
                         (TypeMap.find (mname, tname) types))
              in
              (* check for non-base types and add them if needed. *)
              (* TODO: decide how to deal with nested or both *)
              (* first idea: array of nullable but no nullable arrays *)
              let ty1 =
                if fty.nullable then
                  struct_type context [| nulltag_type; basetype |]
                else basetype in
              let fieldlltype =
                if fty.array then
                  struct_type context
                    [| int_type; pointer_type (array_type ty1 0) |]
                else ty1 in
              (fieldname, fieldlltype, i, fty))
        ) fielddata in
    (* Create the mapping from field name to offset and type. *)
    (* do we still need the high-level type? maybe for lookup info. *)
    let fieldmap =
      List.fold_left (fun fomap (fname, _, i, ftype) ->
          StrMap.add fname (i, ftype) fomap
        ) StrMap.empty ftypeinfo in
    let typename = cdata.in_module ^ "::" ^ cdata.classname in
    match cdata.kindData with 
    (* generate the llvm named struct type, record case *)
    (* Smells funny because fields not used, may want to split it out
       into a more sensible separate function for each kind. *)
    | Struct _ ->
      let structtype = named_struct_type context typename in
      (* "false" means to not use packed structs. *)
      struct_set_body structtype
        (List.map (fun (_, lty, _, _) -> lty) ftypeinfo
         |> Array.of_list) false;
      if cdata.rectype then
        (* recursive types are reference types *)
        (pointer_type structtype, fieldmap)
      else 
        (structtype, fieldmap)
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
      let structtype = named_struct_type context typename in
      struct_set_body structtype
        (if maxsize = Int64.zero then 
           [| varianttag_type |]
         else
           [| varianttag_type;
              (* Voodoo magic: adding 4 bytes fixes my double problem. *)
              array_type (i8_type context) (Int64.to_int maxsize + 4) |])
        false;
      (structtype, fieldmap)
    | Hidden ->
      (* Unknown implementation, must be treated as void pointer *)
      (voidptr_type, StrMap.empty)
    | _ -> (* TODO: opaque type and newtype *)
      (* Now it's an opaque type, but I really don't want to assume.
         need to put an opaque marker in classData?
         Maybe go with a kind variant instead of just lists that can be empty? *)
      failwith ("BUG: missing codegen for class type " ^ cdata.classname)


(** Use a type tag to generate the LLVM type from the base type. *)
let ttag_to_llvmtype lltypes ttag =
  (* find_opt only for debugging. *)
  (* I think we will look up the field offsets elsewhere *)
  match Lltenv.find_lltype_opt (ttag.modulename, ttag.typename) lltypes with
  | None -> failwith ("BUG: no lltype found for " ^ ttag.modulename
                      ^ "::" ^ ttag.typename)
  | Some basetype ->
     let ttag_with_null =
       if ttag.nullable then
         (* (debug_print ("Generating struct for nullable type: "
                      ^ typetag_to_string ttag);  *)
         struct_type context [| nulltag_type; basetype |]
       else basetype in
     if ttag.array then
       struct_type context
         [| int_type; pointer_type (array_type ttag_with_null 0) |]
     else
       ttag_with_null


(** Wrap a value in an outer type. Used for assigning, passing or
    returning a value for a nullable type *)
let promote_value the_val outertype builder =
  debug_print ("promote_value to type " ^ string_of_lltype outertype);
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
    let dataptr = build_call llmalloc [|size_of eltType|] "mallocbytes" builder in
    build_bitcast dataptr (pointer_type eltType) name builder
  

(** Generate an equality comparison. This could get complex. *)
let rec gen_eqcomp val1 val2 valty lltypes builder =
  if is_struct_type valty then
    let fields = get_fields valty.tclass in
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
    checkloop 0 (const_int bool_type 1)
  else if is_variant_type valty then (
    let variants = get_variants valty.tclass in
    (* check tag, then load and cast the variable type if it exists and 
       compare that. *)
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
       let rec gen_caseblocks caseval blocks =
         match blocks with
         | [] -> []
         | cond_bb :: then_bb :: rest -> (
           position_at_end cond_bb builder;
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
             | (_, Some varty) ->
                debug_print "Variant has attached value, generating val compare...";
                let llvarty = ttag_to_llvmtype lltypes varty in
                (* generate the pointer to the variant's value *)
                let gen_varval_ptr theval =
                  let varptr =
                    if is_pointer_value theval then
                      build_struct_gep theval 1 "varptr" builder
                    else
                      (* Easiest way is just to store so we can cast a pointer *)
                      let valalloca =
                        build_alloca (ttag_to_llvmtype lltypes valty)
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
             | (_, None) ->
                debug_print ("no value attached to this case");
                (const_int bool_type 1, then_bb)
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
       debug_print "building phi value";
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
    if (type_of val1) = int_type then
      build_icmp Icmp.Eq val1 val2 "eqcomp" builder
    else if (type_of val2) = float_type then
      build_fcmp Fcmp.Oeq val1 val2 "eqcomp" builder
    else 
      (* for records, could I just dereference if needed and compare the 
       * array directly? Don't think so in LLVM, that's a vector op. *)
      failwith ("Equality for type " ^ typetag_to_string valty
                ^ ": " ^ string_of_lltype (type_of val1) ^ " not supported yet")


(** Generate value of a constant expression. Currenly used for global var 
    initializer and case branches *)
let rec gen_constexpr_value lltypes (ex: typetag expr) =
  (* How many types will this support? Might need a tenv later *)
  if ex.decor = int_ttag then
    match ex.e with
    | ExpConst (IntVal n) -> const_of_int64 int_type n true
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
    | ExpConst (FloatVal x) -> const_float float_type x
    | ExpUnop (OpNeg, e) -> const_fneg (gen_constexpr_value lltypes e)
    | _ -> failwith "Unimplemented Float const expression"
  else if ex.decor = byte_ttag then
    match ex.e with
    | ExpConst (ByteVal c) -> const_int byte_type (int_of_char c)
    | _ -> failwith "Unsupported Byte const expression"
  else if ex.decor = bool_ttag then
    match ex.e with
    | ExpConst (BoolVal b) -> const_int bool_type (if b then 1 else 0)
    | _ -> failwith "Unsupported Bool const expression"
  else
    (* struct type *)
    match ex.e with
    | ExpRecord fieldlist -> 
       (* Iterate over the fields and write the value in an llvalue array *)
       let lltype = Lltenv.find_class_lltype (ex.decor.tclass) lltypes in
       let fieldmap = Lltenv.find_class_fieldmap ex.decor.tclass lltypes in
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
      build_call exitfunc [|const_int int32_type 111|] "" builder
      |> ignore;
      build_br contblock builder |> ignore;
      (* build the OK block with just a jump to the continuation *)
      position_at_end okblock builder;
      build_br contblock builder |> ignore;
      position_at_end contblock builder
    )

(** Find the target address of a varexp from symtable entry and fields *)
let rec get_varexp_alloca the_module builder varexp syms lltypes =
  let ((varname, ixopt), fields) = varexp in
  let (entry, _) =  Symtable.findvar varname syms in
  match entry.addr with 
  | None -> failwith ("BUG: get_varexp_alloca: alloca address not present for "
                      ^ entry.symname)
  | Some alloca ->
    (* traverse indices and record fields to generate the final alloca. *)
    let rec get_field_alloca flds ixopt parentty alloca =
      (* index expression [] first; strip off array type after indexing *)
      debug_print ("get_varexp_alloca: " ^ string_of_llvalue alloca);
      let (alloca, newty) =
        match ixopt with
        | None -> (alloca, parentty)
        | Some ixexpr ->
          let ixval = gen_expr the_module builder syms lltypes ixexpr in
          (* get the value at index 1. alloca is the address of the struct. *)
          let datafield = build_struct_gep alloca 1 "datafield" builder in
          debug_print (string_of_llvalue datafield);
          (* have to load to get the actual pointer to the llvm array *)
          let dataptr = build_load datafield "dataptr" builder in
          (* Load the array size to do the bounds check. *)
          let arraysize = build_load
              (build_struct_gep alloca 0 "sizeptr" builder)
              "arraysize" builder
          in
          gen_bounds_check ixval arraysize the_module builder;
          (* gep to the 0th element first to "follow the pointer" *)
          (build_gep dataptr [|(const_int int_type 0); ixval|]  
             "elementtptr" builder,
           {parentty with array=false})
      in
      (* next, get the field offset if there is one. *)
      match flds with
      | [] -> (alloca, newty)
      | (fld, ixopt)::rest -> 
        (* Get just the class of parent type so we can find its field info.
           Analysis determined it's not a nullable. *)
        let ptypekey = (parentty.modulename, parentty.typename) in
        (* If array length, it has no further fields, we're done. *)
        (* the test for = "length" should be redundant. *)
        if parentty.array && fld = "length" then
          (build_struct_gep alloca 0 "length" builder, int_ttag)
        else (
          (* check if dereference needed first, for recursive type. *)
          let alloca = if parentty.tclass.rectype
            then 
              build_load alloca "rectype-deref" builder
            else alloca in
          (* Look up field offset in Lltenv, emit gep *)
          let offset, fieldtype = Lltenv.find_field ptypekey fld lltypes in
          debug_print ("get_varexp_alloca: generating struct gep for " ^ fld
                       ^ " for type " ^ string_of_lltype (type_of alloca));
          let alloca = build_struct_gep alloca offset "field" builder in
          (*  Propagate field's typetag to next iteration *)
          debug_print "get_varexp_alloca: recursing";
          get_field_alloca rest ixopt fieldtype alloca )
    in
    (* top-level call *)
    get_field_alloca fields ixopt entry.symtype alloca

(** Generate LLVM code for an expression *)
and gen_expr the_module builder syms lltypes (ex: typetag expr) = 
  match ex.e with
  | ExpConst NullVal -> const_int nulltag_type 0 (* maybe used now *)
  | ExpConst (IntVal i) -> const_of_int64 int_type i true (* signed *)
  | ExpConst (FloatVal f) -> const_float float_type f
  | ExpConst (ByteVal c) -> const_int byte_type (int_of_char c)
  | ExpConst (BoolVal b) -> const_int bool_type (if b then 1 else 0) 
  | ExpConst (StringVal s) ->
    (* It will build the instruction /and/ return the ptr value *)
    build_global_stringptr s "sconst" builder

  | ExpVal (e) ->
    (* val(exp) is the nullable wrapper, so promote to the null-tag container. *)
    let evalue = gen_expr the_module builder syms lltypes e in
    let nullabletype = ttag_to_llvmtype lltypes ex.decor in 
    promote_value evalue nullabletype builder 

  | ExpVar (((varname, _), _) as varexp) -> (
      (* gets complicated with arrays and fields; call out to helper function *)
      let (alloca, _) =
        get_varexp_alloca the_module builder varexp syms lltypes in
      (* only load if primitive type? Oh, it breaks function signatures that 
       * expect value types... and causes other crashes.*)
      (* if is_primitive_type ex.decor then  *)
      debug_print "ExpVar: varexp alloca created";
      build_load alloca (varname ^ "-expr") builder
      (* else alloca *)
    )

  | ExpRecord fieldlist ->
    let typekey = (ex.decor.modulename, ex.decor.typename) in
    let llty = Lltenv.find_lltype typekey lltypes in
    let recaddr =
      (* recursive record types are heap-allocated. *)
      if ex.decor.tclass.rectype then
        (* llty is already the pointer type *)
        build_gc_malloc (element_type llty) "rectype" the_module builder
      else 
        build_alloca llty "recaddr" builder in
    List.iter (fun (fname, fexp) ->
        (* have to use the map from fields to nums *)
        let fexpval = gen_expr the_module builder syms lltypes fexp in
        let fieldaddr =
          build_struct_gep recaddr
            (fst (Lltenv.find_field typekey fname lltypes))
            "fieldaddr" builder in
        (* check if null promotion is needed; the field lltype might be an opaque
           pointer, so use the typename to fetch the actual type from the lltenv *)
        let fieldtype = element_type (type_of fieldaddr) in
        debug_print ("field and expr types: "
                     ^ string_of_lltype fieldtype ^ ", "
                     ^ string_of_lltype (type_of fexpval));
        let finalval =
          if fieldtype = type_of fexpval
          then fexpval
          else (
            debug_print ("field value promotion needed");
            promote_value fexpval fieldtype builder ) in
        (* next: if it's rec, get pointer and cast to the i8*  *)
        (* if fexp.decor.tclass.rectype then *)
        debug_print ("field value store: " ^ string_of_llvalue
                       (build_store finalval fieldaddr builder));
      ) fieldlist;
    (* recursive types return the pointer, otherwise the value *)
    if ex.decor.tclass.rectype then
      recaddr
    else 
      build_load recaddr "recordval" builder


  | ExpVariant ((tymod, tyname), variant, eopt) ->
    debug_print ("Generating variant expression code for " ^ tyname);
    (* 1. Look up lltype and allocate struct *)
    let (llvarty, varmap) = TypeMap.find (tymod, tyname) lltypes in
    (* 2. Look up variant type, allocate struct, store tag value *)
    let typesize = Array.length (struct_element_types llvarty) in
    let (tagval, subty) = StrMap.find variant varmap in
    let structsubty =
      struct_type context
        (if typesize = 1 || subty = void_ttag
         then [| varianttag_type |]
         else
           let llsubty = ttag_to_llvmtype lltypes subty in
           [| varianttag_type; llsubty |]
        ) in
    debug_print ("  subtype struct: " ^ string_of_lltype structsubty);
    let structaddr = build_alloca structsubty "variantSubAddr" builder in 
    let tagaddr = build_struct_gep structaddr 0 "tag" builder in
    ignore (build_store (const_int varianttag_type tagval) tagaddr builder);
    (* 3. generate code for expr (if exists) and store in the value slot *)
    (match eopt with
     | None -> ()
     | Some e ->
       (* Think we need to hint this to the variant subtype 
        * (for instance, so "null" will be promoted *)
       let expval =
         let eval1 = gen_expr the_module builder syms lltypes e in
         if e.decor <> subty then
           let nullabletype = ttag_to_llvmtype lltypes subty in 
           promote_value eval1 nullabletype builder
         else eval1 in
       let valaddr = build_struct_gep structaddr 1 "varVal" builder in
       ignore (build_store expval valaddr builder)
    );
    (* 4. cast specific struct to the general struct and load the whole thing *)
    (* It still wants the cast even if no value (because named struct?) *)
    let castedaddr = build_bitcast structaddr (pointer_type llvarty)
        "varstruct" builder in
    let varval = build_load castedaddr "filledVariant" builder in
    varval 
  (* it's stored anyway, so why not just use the pointer? *)
  (* because semantics, and LLVM can elide load/store anyway. *)
  (* castedaddr *)

  | ExpSeq elist ->
    let eltType = ttag_to_llvmtype lltypes (List.hd elist).decor in
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
    let structalloca = build_alloca (ttag_to_llvmtype lltypes ex.decor)
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
        | OpEq -> build_fcmp Fcmp.Oeq e1val e2val "feqtemp" builder
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
        gen_eqcomp e1val e2val e1.decor lltypes builder
      else
        failwith "unknown type for binary operation"
    )

  | ExpCall (fname, args) ->
    let (callee, llargs) = 
      gen_call the_module builder syms lltypes (fname, args) in
    build_call callee llargs "calltmp" builder

  | ExpNullAssn (_, _, _, _) ->
    failwith "BUG: null assign found outside condition"


(** Generate LLVM for a function call (used in both expr and stmt) *)
and gen_call the_module builder syms lltypes (fname, args) =
  let (fentry, _) = Symtable.findproc fname syms in
  match lookup_function fentry.procname the_module with
  (* lookup assumes procedure names are unique, which is how I intended *)
  | None -> failwith "BUG: unknown function name in codegen"
  | Some llfunc ->
    let llargs =
      List.map2 (fun (mut, argexpr) fparam ->
          (* mutable is pass-by-reference; get the variable expr's alloca *)
          if mut then
            match argexpr.e with
            | ExpVar _ -> (   (* (v, vlds) *)
                (* new idea: if it's already a pointer type just pass it?
                   How to get the lltype? *)
                let varentry, _ =
                  Symtable.findvar (exp_to_string argexpr) syms in
                match varentry.addr with
                | Some alloca ->
                  (* I think this is where I promote. *)
                  (* if varentry.symtype.nullable <> argexpr.decor.nullable then *)
                  if argexpr.decor.nullable then
                    failwith "Not yet supporting mutable nullable args"
                  else 
                    alloca
                | None -> failwith "BUG: alloca not found for mutable arg"
              )
            | _ -> failwith "BUG: non-var mutable argument in codegen"
          else (
            debug_print "gen_call: generating argument expression";
            let argval = gen_expr the_module builder syms lltypes argexpr in
            (* Need to wrap value if passing into a union (nullable) type *)
            if argexpr.decor = fparam.symtype then (
              debug_print "gen_call: correct type argument value generated";
              argval )
            else (
              debug_print "gen_call: promoting arg value";
              let nullabletype = ttag_to_llvmtype lltypes fparam.symtype in
              promote_value argval nullabletype builder ))
        ) args fentry.fparams
      |> Array.of_list in
    (llfunc, llargs) (* actual build is different if expr or stmt *)


let rec gen_stmt the_module builder lltypes (stmt: (typetag, 'a st_node) stmt) =
  let syms = stmt.decor in
  match stmt.st with
  | StmtDecl (varname, _, eopt) -> (
    (* technically, decl should only lookup in this scope. 
     * But we don't care in codegen, right, it's all correct? *)
    (* print_string ("looking up " ^ varname ^ " for decl codegen\n"); *)
    let (entry, _) = Symtable.findvar varname syms in
    let allocatype = ttag_to_llvmtype lltypes entry.symtype in
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
         {st=StmtAssign (((varname, None), []), initexp); decor=syms}
  )

  | StmtAssign (varexp, ex) -> (
    let alloca, vetype =
      get_varexp_alloca the_module builder varexp syms lltypes in
    debug_print ("StmtAssign lvalue addr: " ^ string_of_llvalue alloca);
    let expval = gen_expr the_module builder syms lltypes ex in
    debug_print ("StmtAssign: Generated RHS expr: " ^ string_of_lltype (type_of expval));
    debug_print ("StmtAssign: Alloca type: " ^ string_of_lltype (type_of alloca));
    (* cases to handle nullable types *)
    if vetype.nullable = ex.decor.nullable then
      (* indirection level is the same, so just directly assign the value *)
      ignore (build_store expval alloca builder)
    else
      (* will have to handle pointer types too for record type? *)
      let nullabletype = ttag_to_llvmtype lltypes vetype in 
      let promotedval = promote_value expval nullabletype builder in
      ignore (build_store promotedval alloca builder)
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
            let supertype = ttag_to_llvmtype lltypes rettype in 
            promote_value ev supertype builder  )
        in
        let retval =
          (* If type is opaque, need to return a void pointer. *)
          if rettype.tclass.opaque then
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
    (* TODO: factor this out to use in while loops too *)
    let gen_cond cond thenbb blocksyms =
      match cond.e with
      | ExpNullAssn (isdecl, (((varname, _), _) as varexp), _, nullexp) ->
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
         if cond.decor.nullable then
           let nulltag = build_extractvalue condval 0 "nulltag" builder in
           build_icmp Icmp.Ne
             nulltag (const_int nulltag_type 0) "condres" builder
         else condval
    in
    let start_bb = insertion_block builder in
    let the_function = block_parent start_bb in
    let then_bb = append_block context "then" the_function in
    let blocksyms = (List.hd thenblock).decor in
    position_at_end start_bb builder;
    let condval = gen_cond cond then_bb blocksyms in
    (* need this because a (variant) comparison in the cond can add bb's *)
    let new_start_bb = insertion_block builder in 
    position_at_end then_bb builder;
    List.iter (gen_stmt the_module builder lltypes) thenblock;
    (* code insertion could add new blocks to the "then" block. *)
    let new_then_bb = insertion_block builder in
    (* elsif generating code *)
    let gen_elsif (cond, (block: (typetag, 'b) stmt list)) =
      (* however, need to insert conditional jump and jump-to-merge later *)
      let cond_bb = append_block context "elsifcond" the_function in
      position_at_end cond_bb builder;
      let then_bb = append_block context "elsifthen" the_function in
      let blocksyms = (List.hd block).decor in
      let condval = gen_cond cond then_bb blocksyms in
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
    let start_bb = insertion_block builder in
    let the_function = block_parent start_bb in
    (* generate value of expression to match *)
    let matchval = gen_expr the_module builder syms lltypes matchexp in
    (* Need to store the match val also, to have the pointer  *)
    (* TODO: optimize to omit this if it's an enum-only variant *)
    let matchaddr =
      build_alloca (type_of matchval) "matchaddr" builder in
    ignore (build_store matchval matchaddr builder);
    let fieldmap =
      match TypeMap.find_opt (matchexp.decor.modulename,
                              matchexp.decor.typename) lltypes with
      | None -> None
      | Some (_, fieldmap) -> Some fieldmap in
    (* Get the conditional value for matching against the case. *)
    let gen_caseexp caseexp = 
      match caseexp.e with
      | ExpVariant (_, vname, _) ->
         (* only compare the tags; the load of the value into the
            variable is done in the block body *)
         let matchtagval = build_extractvalue matchval 0 "matchtag" builder in
         let fieldmap = Option.get fieldmap in
         (* compare tag value of case to tag of the matchval *)
         let casetag = fst (StrMap.find vname fieldmap) in
         build_icmp
           Icmp.Eq (const_int varianttag_type casetag) matchtagval
           "casecomp" builder
      | ExpVal {e=ExpVar(_, _); decor=_} ->
         (* 'val(x)' matches whenever the tag value is 1 (non-null) *)
         let matchtagval = build_extractvalue matchval 0 "matchtag" builder in
         build_icmp
           Icmp.Eq (const_int nulltag_type 1) matchtagval
           "valcomp" builder
      | ExpConst NullVal ->
         let matchtagval = build_extractvalue matchval 0 "matchtag" builder in
         build_icmp
           Icmp.Eq (const_int nulltag_type 0) matchtagval
           "nullcomp" builder
      (* other value types. *)
      | _ ->
         let caseval = gen_constexpr_value lltypes caseexp in
           (* gen_expr the_module builder syms lltypes caseexp in *)
         (* wait, is this my first real equality gen? *)
         (* maybe a gen_compare? *)
         gen_eqcomp matchval caseval matchexp.decor lltypes builder
         (* what if it's an ExpCall? Have to see if the return value is nullable *)
         (* expCall's decor is the return type, right? *)
         (* think we don't need to worry about this as long as they're constexprs *)
    in
    (* generate compare and block code, return the block pointers for jumps *)
    let gen_caseblock caseexp (caseblock: ('ed,'sd) stmt list) =
      (* however, need to insert conditional jump and jump-to-merge later *)
      let comp_bb = append_block context "casecomp" the_function in
      position_at_end comp_bb builder;
      let blocksyms = (List.hd caseblock).decor in
      debug_print (st_node_to_string blocksyms);
      let condval = gen_caseexp caseexp (* casebody_bb blocksyms *) in
      let casebody_bb = append_block context "casebody" the_function in
      (* Need the syms for the variable that's declared to hold the value *)
      position_at_end casebody_bb builder;
      (* If variant holds a value, create alloca and load value *)
      (match caseexp.e with
       | ExpVariant (_, vname, Some valvar) -> (
         match valvar.e with
         | ExpVar ((varname, _), _) -> 
            let fieldmap = Option.get fieldmap in
            let casetype = snd (StrMap.find vname fieldmap) in
            let caselltype = ttag_to_llvmtype lltypes casetype in
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
               pointer instead? but if it's mutable wont' it be a pointer
               type already? Not local records! ok, trying it... *)
            (* let caseval = build_load valptr "caseval" builder in 
            ignore (build_store caseval alloca builder) *)
            Symtable.set_addr blocksyms varname valptr; 
         | _ -> failwith "Shouldn't happen: no ExpVar in case"
       )
       | ExpVal({e=ExpVar((valvar, _), _); decor=_}) ->
          (* let valtype = {matchexp.decor with nullable=false} in
          let vallltype = ttag_to_llvmtype lltypes valtype in  *)
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
    position_at_end test_bb builder;
    let condval = match cond.e with
      | ExpNullAssn (_,_,_,_) -> failwith "null assign not yet implemented"
      | _ -> gen_expr the_module builder syms lltypes cond in
    (* Create loop block and fill it in *)
    let loop_bb = append_block context "loop" the_function in
    position_at_end loop_bb builder;
    List.iter (gen_stmt the_module builder lltypes) body;
    (* add unconditional jump back to test *)
    let new_loop_bb = insertion_block builder in (* don't need? *)
    position_at_end new_loop_bb builder;         (* is it there already? *)
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
    debug_print "StmtCall: generated arguments.";
    ignore (build_call callee llargs "" builder)
  | StmtCall _ -> failwith "BUG: StmtCall without CallExpr"

  | StmtBlock _ -> failwith "not implemented"


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
let gen_global_decl the_module lltypes (gdecl: ('ed, 'sd) globalstmt) =
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
        let rawRetType = ttag_to_llvmtype lltypes procentry.rettype in
        if procentry.rettype.tclass.opaque then (
          debug_print ("-- Generating opaque return type for "
                       ^ string_of_lltype rawRetType);
          voidptr_type
        )
        else rawRetType in
      let paramtypes =
        List.map (fun entry ->
            let ptype = ttag_to_llvmtype lltypes entry.symtype in
            (* if entry.symtype.tclass.opaque then
               voidptr_type *)
            (* if is_primitive_type entry.symtype then ptype
            else pointer_type ptype *) (* simplifying try *)
            (* make it the pointer type if it's passed mutable *)
            if entry.mut then
              if entry.symtype.nullable then
                (* If nullable we want a nullable pointer to the inner type. *)
                struct_type context [|
                    nulltag_type;
                    pointer_type (Lltenv.find_class_lltype
                                    entry.symtype.tclass lltypes)
                  |]
              else
                pointer_type ptype
            else ptype
          ) procentry.fparams
        |> Array.of_list in
      let llfunctype = function_type rettype paramtypes in
      debug_print ("-- Declaring function " ^ procentry.procname
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
             in if paramentry.symtype.tclass.opaque
                && paramentry.symtype.tclass.kindData <> Hidden then ( 
               debug_print ("-- Casting opaque argument " ^ varname ^ " to concrete type");
               build_bitcast (param llfunc i)
                 (pointer_type (ttag_to_llvmtype lltypes paramentry.symtype))
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
           if fentry.rettype.tclass.opaque then
             (* WAT! It works if I call it twice? *)
             const_null (return_type (return_type (type_of llfunc)))
           else const_null  (ttag_to_llvmtype lltypes fentry.rettype) in
         ignore (build_ret dummyRetval builder);
           (* ignore (build_ret (default_value fentry.rettype) builder); *)
         Llvm_analysis.assert_valid_function llfunc
       )


(** Generate LLVM code for an analyzed module. *)
let gen_module tenv topsyms layout (modtree: (typetag, 'a st_node) dillmodule) =
  let the_module = create_module context (modtree.name ^ ".ll") in
  (* Llvm.set_target_triple ttriple the_module; *)
  Llvm.set_data_layout (Llvm_target.DataLayout.as_string layout) the_module;
  let builder = builder context in
  (* 1. Generate dict of llvm types from the tenv (imports are added
     to it by the analyzer.) *)
  let lltypes =
    TypeMap.fold (fun _ cdata lltenv ->
        (* fully-qualified typename now *)
        let newkey = (cdata.in_module, cdata.classname) in
        (* note that lltydata is a pair type. *)
        let (lltype, fieldmap) = gen_lltype context tenv lltenv layout cdata in
        debug_print (
            "adding type " ^ (fst newkey) ^ "::" ^ (snd newkey)
            ^ " to lltenv, lltype: " ^ string_of_lltype lltype);
        Lltenv.add newkey (lltype, fieldmap) lltenv
      ) tenv Lltenv.empty in
  (* 2. Generate decls from the symtable for imported global variables. *)
  StrMap.iter (fun localname gsym ->
      let gvalue = declare_global
                     (ttag_to_llvmtype lltypes gsym.symtype)
                     gsym.symname
                     the_module in
      set_externally_initialized true gvalue;
      (* Name maybe not correct? Need the local name of it. *)
      Symtable.set_addr topsyms localname gvalue
    ) topsyms.syms;
  (* 2.5 Generate low-level function declarations (just GC alloc for now) *)
  declare_function "GC_malloc"
    (function_type (pointer_type byte_type) [|int_type|]) the_module
  |> ignore ;
  declare_function "exit"
    (function_type void_type [|int32_type|]) the_module |> ignore;
  (* 3. Generate decls for imported functions (already in root node.) *)
  gen_fdecls the_module lltypes topsyms.fsyms;
  (* if List.length (topsyms.children) <> 1 then
     failwith "BUG: didn't find unique module-level symtable"; *)
  (* 4. Generate decls for this module's global variables. *)
  (* The next symtable node underneath holds this module's proc declarations *)
  let modsyms = List.hd (topsyms.children) in
  List.iter (gen_global_decl the_module lltypes) modtree.globals;
  (* 5. Generate this module's procedure declarations (all at once, so
     they can mutually refer) *)
  gen_fdecls the_module lltypes modsyms.fsyms;
  (* 6. Generate each of the procedures. *)
  List.iter (gen_proc the_module builder lltypes) modtree.procs;
  Llvm_analysis.assert_valid_module the_module;
  the_module
