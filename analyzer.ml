(** Semantic analyzer: check for errors and build type- and symbol- 
  * decorated AST *)

open Common
open Types
open Ast
open Symtable1

exception SemanticError of string

(* Analysis pass populates symbol table and type environment. 
 * Hopefully all possibilities of error can be caught in this phase. *)

(* Symbol table nodes are decorations for statements. *)

let reserved_words = (* Skip "open" and "import". Actually I don't use these *)
  StrSet.of_list [
      "as"; "begin"; "case"; "else"; "elsif"; "endcase"; "endif"; "endwhile";
      "export"; "false"; "if"; "loop"; "modspec"; "module"; "mut"; "nop";
      "null"; "of"; "private"; "proc"; "return"; "struct"; "then"; "true";
      "type"; "val"; "var"; "variant"; "while"
    ]
let reserved_names = StrSet.of_list [ "null"; "true"; "false"; "val" ]
(* Is it enough that these are in the tenv? But could have local types
   with the same classname... Should I prevent the classname altogether? *)
(* let reserved_classnames = StrSet.of_list [ "Array"; "Option" ] *)
let reserved_procnames = StrSet.of_list [ "val" ]

(** make the type expr result return only the tag for now. 
 *  Hopefully there's no need for a rewritten typeExp in the AST. *)
type typeExpr_result = (typetag, string) result

(** Check that a type expression refers to a valid type in the
    environment and that all type variables are declared, then create
    the tag. *)
let rec check_typeExpr syms tenv texp : (typetag, string) result =
  match texp.texpkind with
  | Generic gv -> (
      match Symtable.findtvar_opt gv syms with
      | Some (_, _) ->
        (* Array and Option are regular generic types, but with their
           special syntax the generic variable comes first. *)
        if texp.array then (
          (* case for t?[], we don't allow t[]?  TODO: make it so in syntax. *)
          if texp.nullable then Ok (array_type_of (option_type_of (Typevar gv)))
          else Ok (array_type_of (Typevar gv)))
        else if texp.nullable then Ok (option_type_of (Typevar gv))
        else Ok (Typevar gv)
      | None -> Error ("Undeclared type variable " ^ gv)
    )
  | Concrete ctexp -> (
      (* Types should be in the typeenv keyed by the name used locally. *)
      match PairMap.find_opt (ctexp.modname, ctexp.classname) tenv with
      | None -> Error ("Unknown type " ^ typeExpr_to_string texp)
      | Some cdata ->
        (* Check that type argument lengths are the same. *)
        if List.length ctexp.typeargs <> List.length cdata.tparams then
          Error ("Incorrect number of type arguments for " ^ cdata.classname
                 ^ "; expected "
                 ^ string_of_int (List.length cdata.tparams) ^ ", found "
                 ^ string_of_int (List.length ctexp.typeargs))
        else (
          (* recurse to check the type arguments. *)
          let ress = List.map (check_typeExpr syms tenv) ctexp.typeargs in
          match List.filter Result.is_error ress with 
          | (Error err)::_ -> Error err (* only take first error *)
          | _ ->
            (* substitute type arguments and produce the tag. *)
            let argtags = concat_ok ress in 
            let innerTtag = 
              Namedtype {modulename=cdata.in_module; (* redundant? *)
                         tclass=cdata;
                         typeargs=argtags} in
            (* potentially double-wrap with nullable, then array *)
            let innerTtag = if texp.nullable then
                Namedtype {modulename="";
                           tclass=option_class;
                           typeargs=[innerTtag]}
              else innerTtag in
            if texp.array then
              Ok (Namedtype {modulename="";
                             tclass=array_class;
                             typeargs=[innerTtag]})
            else (Ok innerTtag)
        ))


(** Syntactically determine if an expression is constant *)
let rec is_const_expr = function
  (* if true, I could eval and replace it in the AST. But...
   * what if numerics don't match the target? Let LLVM do it. *)
  | ExpConst _ -> true
  | ExpVar (_,_) -> false (* TODO: check in syms if it's a const *)
  | ExpBinop (e1, _, e2) -> is_const_expr e1.e && is_const_expr e2.e
  | ExpUnop (_, e1) -> is_const_expr e1.e
  | ExpRecord fieldlist ->
     List.for_all (fun (_, e) -> is_const_expr e.e) fieldlist
  | ExpSeq elist ->
     List.for_all (fun e -> is_const_expr e.e) elist
  | _ -> false


(** Expression result type (remember that exprs have a type field) *)
type expr_result = (typetag expr, string located) Stdlib.result

(** Deep check to see if a varexp is something mutable. *)
let is_mutable_varexp syms ((vname, ixopt), flist) =
  let varentry, _ =
    Symtable.findvar vname syms in
  if not (varentry.var && varentry.mut)
  then false
  else
    let rec is_mut_loop partype = function
      | [] -> true
      | (fname, ixopt) :: rest ->
        (* find field in partype and check if mut *)
        (match get_ttag_field partype fname with
         | None -> failwith "is_mutable_varexp: type doesn't have such a field"
         | Some finfo -> 
           if not finfo.mut then false
           else let fieldtype =
                  match ixopt with
                  | Some _ -> array_element_type finfo.fieldtype
                  | None -> finfo.fieldtype
             in
             is_mut_loop fieldtype rest)
    in
    let vartype = match ixopt with
      | Some _ -> array_element_type varentry.symtype
      | None -> varentry.symtype
    in 
    is_mut_loop vartype flist


(** Check semantics of an expression, replacing decor with a type *)
let rec check_expr syms (tenv: typeenv) ?thint:(thint=None)
    (ex: locinfo expr) : expr_result = 
  match ex.e with
  (* The type info in constants is already there...ok I guess *)
  | ExpConst NullVal ->
    Ok {e=ExpConst NullVal; decor=null_ttag}
  | ExpConst (IntVal i) ->
    Ok {e=ExpConst (IntVal i); decor=int_ttag}
  | ExpConst (FloatVal f) ->
    Ok {e=ExpConst (FloatVal f); decor=float_ttag}
  | ExpConst (ByteVal c) ->
    Ok {e=ExpConst (ByteVal c); decor=byte_ttag}
  | ExpConst (BoolVal b) ->
    Ok {e=ExpConst(BoolVal b); decor=bool_ttag}
  | ExpConst (StringVal s) ->
    Ok {e=ExpConst (StringVal s); decor=string_ttag}

  (* The "val" constructor for a nullable *)
  | ExpVal (expr) -> (
      match check_expr syms tenv expr with
      | Error eres -> Error eres
      | Ok echecked ->
        if is_option_type echecked.decor then
          Error {loc=ex.decor;
                 value="Double-nullable typed expressions not allowed"}
        else 
          Ok { e=ExpVal(echecked);
               decor=option_type_of echecked.decor })

  | ExpVar ((varstr, ixopt), fields) -> (
      (* let varstr = exp_to_string ex in *)
      debug_print ("#AN: checking variable expression " ^ exp_to_string ex);
      match Symtable.findvar_opt varstr syms with
      | None -> Error {loc=ex.decor; value="Undefined variable " ^ varstr}
      | Some (entry, _) -> (
          if StrSet.mem varstr syms.uninit then
            Error {loc=ex.decor;
                   value="Variable " ^ varstr ^ " may not be initialized"}
          else
            (* Now need to do proper field checking *)
            (* first, make sure var is array type if has index expr. *)
          if Option.is_some ixopt && not (is_array_type entry.symtype) then
            Error {loc=ex.decor; value="Index expression on non-array type "
                                       ^ typetag_to_string entry.symtype}
          else 
            (* first, check index expression if any *)
            let check_indexexp ixopt =
              match ixopt with
              | None -> Ok None
              | Some ixexp -> 
                match check_expr syms tenv ixexp with
                | Error err -> Error err
                | Ok checked_ixexp ->
                  if checked_ixexp.decor <> int_ttag then
                    Error {loc=ex.decor;
                           value="Index expression must have integer type"}
                  else Ok (Some checked_ixexp) in
            match check_indexexp ixopt with 
            | Error err -> Error err
            | Ok ixopt -> (
                (* get type of expression apart from array *)
                let headtype =
                  if Option.is_some ixopt then
                    array_element_type entry.symtype
                  else entry.symtype
                in 
                (* second, recursively check fields. return fields & type *)
                let rec check_fields prevty fields =
                  match fields with
                  | [] -> Ok ([], prevty)
                  | (fname, ixopt)::rest -> (
                      (* TODO: check for opaque type here for better
                         error messages "cannot access fields of types
                         whose structure is hidden" *)
                      match get_ttag_field prevty fname with
                      | None -> 
                        Error {loc=ex.decor;
                               value="Field " ^ fname
                                     ^ " does not belong to type "
                                     ^ typetag_to_string prevty}
                      | Some finfo ->
                        if Option.is_some ixopt
                        && not (is_array_type finfo.fieldtype) then
                          Error {loc=ex.decor;
                                 value="Index expression on non-array type"
                                       ^ typetag_to_string finfo.fieldtype}
                        else
                          (* Look for a specified type if field is generic. *)
                          let fieldty = 
                            match finfo.fieldtype with
                            | Typevar tvar -> get_typearg prevty tvar
                            (* TODO: may need to recurse to fill in type
                               variables all the way down. *)
                            | Namedtype _ -> finfo.fieldtype 
                          in 
                          match check_indexexp ixopt with
                          | Error err -> Error err
                          | Ok ixopt -> (
                              (* Recurse with this type as the outer type. *)
                              match check_fields
                                      (* It's only the array type if no ix *)
                                      (if Option.is_none ixopt then fieldty
                                       else array_element_type fieldty)
                                      rest with
                              | Ok (checked_fields, finalty) ->
                                Ok ((fname, ixopt)::checked_fields, finalty)
                              | Error err -> Error err
                            ))
                in
                match check_fields headtype fields with
                | Error err -> Error err
                | Ok (checked_fields, expty) -> 
                  debug_print ("#AN: var expression type: "
                               ^ typetag_to_string expty);
                  Ok { e=ExpVar ((varstr, ixopt), checked_fields);
                       decor=expty })
        )
    )

  | ExpRecord _ -> (
      match thint with
      | None ->
        Error {
          loc=ex.decor;
          value="Type of record literal cannot be determined in this context"
        }
      | Some ttag ->
        debug_print ("#AN: checking record expression to match "
                     ^ typetag_to_string ttag);
        check_recExpr syms tenv ttag ex
    )

  | ExpSeq elist -> (
      match thint with
      | None -> Error
                  {loc=ex.decor;
                   value="Unable to determine sequence type in this context"}
      | Some seqty ->
        let eltty: typetag = array_element_type seqty in 
        let checked_elist =
          List.map (check_expr syms tenv ~thint:(Some eltty)) elist in
        (* parser ensures no empty list expressions *)
        let elist_errors = List.filter Result.is_error checked_elist in
        if elist_errors <> [] then
          (* Just throw the first error for now *)
          List.hd elist_errors
        else
          let elist = concat_ok checked_elist in
          (* let eltty = (List.hd elist).decor in *)
          let types_equal = List.for_all (fun (e: typetag expr) ->
              e.decor = eltty) elist in
          if not types_equal then
            Error {loc=ex.decor;
                   value="Inconsistent types in array expression"}
          else
            (* Note: won't work with array of arrays. *)
            Ok {e=ExpSeq elist; decor=array_type_of eltty}
    )                                                
  (* typecheck and all make sure they're the same type. *)
  (* return type is array of, or special sequence type to be more general? *) 

  | ExpVariant (_, _, _) ->
    check_variant syms tenv ex ~declvar:false thint

  | ExpBinop (e1, oper, e2) -> (
      debug_print "#AN: Checking binary operator expression";
      match check_expr syms tenv e1 with
      | Ok ({e=_; decor=ty1} as e1) -> (  (* without () e1 is the whole thing *)
          match check_expr syms tenv e2 with
          | Ok ({e=_; decor=ty2} as e2) -> (
              debug_print "#AN: checked both operands";
              (* Oh. the type comparison itself recurses *)
              if not (types_equal ty1 ty2) then 
                Error {loc=ex.decor;
                       value = ("Operator type mismatch: " ^ typetag_to_string ty1
                                ^ ", " ^ typetag_to_string ty2)}
              else (
                match oper with
                | OpEq | OpNe | OpLt | OpGt | OpLe | OpGe ->
                  (* Also not valid for generic types? *)
                  if is_generic_type ty1 then
                    Error {
                      loc=ex.decor;
                      value="Comparison operator not valid for generic types"
                    }
                  else if is_recursive_type ty1 then
                    Error {
                      loc=ex.decor;
                      value="Comparison operator not valid for recursive types"
                    }
                  else
                    Ok {e=ExpBinop (e1, oper, e2); decor=bool_ttag}
                | OpAnd | OpOr when ty1 <> bool_ttag ->
                  if ty1 <> bool_ttag then
                    Error {
                      loc=ex.decor;
                      value="Operations && and || only valid for type bool"
                    }
                  else
                    Ok {e=ExpBinop (e1, oper, e2); decor=bool_ttag}
                | _ ->
                  (* TODO: check type interfaces for operation. *)
                  Ok {e=ExpBinop (e1, oper, e2); decor=ty1}
              ))
          | Error err -> Error err
        )
      | Error err -> Error err
    )

  | ExpUnop (oper, exp) -> (
      match check_expr syms tenv exp with
      | Error err -> Error err
      | Ok ({e=_; decor=ty} as exp) -> (
          match oper with
          | OpNot ->
            if ty <> bool_ttag then
              Error {loc=ex.decor;
                     value="Operation ! only valid for type bool"}
            else
              Ok {e=ExpUnop (oper, exp); decor=ty}
          | _ ->
            (* TODO: check interfaces of ty for operation *)
            Ok {e=ExpUnop (oper, exp); decor=ty}
        ))

  | ExpCall (fname, args) -> (
      match check_call syms tenv (fname, args) with
      | Error msg -> Error { loc=ex.decor; value=msg }
      | Ok cexp -> Ok cexp
    )
  | ExpNullAssn _ ->
    Error {loc=ex.decor;
           value="Null-check assignment not allowed in this context"}

(** Helper for check_call to match a formal with actual parameter list *)
(* Should I embed this in check_call? *)
and match_params paramsyms (args: (bool * typetag expr) list) =
  let rec accloop paramsyms (args: (bool * typetag expr) list) accmap = 
    match (paramsyms, args) with
    | ([], []) -> Ok accmap
    | (_, []) | ([], _) ->
      Error ("Argument number mismatch: procedure expects "
             ^ string_of_int (List.length paramsyms) ^ " arguments, got "
             ^ string_of_int (List.length args))
    (* may not make sense to recurse on the outer function anymore *)
    | (pentry::prest, (argmut, argexp)::arest) -> (
        (* Anything need to be kept here to inform code generation? *)
        match ((*subtype_match*) unify_match argexp.decor pentry.symtype) with
        | Error (argtag, paramtag) ->
          Error ("Cannot unify argument type " ^ typetag_to_string argtag
                 ^ " with parameter type " ^ typetag_to_string paramtag)
        | Ok tvarmap -> (* probably have to surround with a fold *)
          if pentry.mut <> argmut
        then Error ("Mutability flag mismatch for parameter " ^ pentry.symname)
        else
          (* merge map with accumulated map *)
          match merge_tvarmaps tvarmap accmap with
          | Error (tag1, tag2) ->
            Error ("Inconsistent type variable usage between "
                   ^ typetag_to_string tag1 ^ " and "
                   ^ typetag_to_string tag2)
          | Ok mergedmap -> accloop prest arest mergedmap
      )
  in accloop paramsyms args StrMap.empty

(** Procedure call check, used for both exprs and stmts. *)
and check_call syms tenv (fname, args) =
  (* TODO: check fn name and argument types first, so can send the hints. *)
  match Symtable.findproc_opt fname syms with
  | None -> Error ("Unknown procedure name: " ^ fname)
  | Some (proc, _) -> (
      let argTypes = List.map (fun ent -> Some ent.symtype) proc.fparams in
      (* recursively check argument exprs and store types in list. *)
      let args_res = List.map2 
          (fun ex argty -> check_expr syms tenv ex ~thint:argty) 
          (List.map snd args) argTypes in
      (* Concatenate errors from args check and bail out if any *)
      (* check_expr doesn't return a list, so stitch into one. *)
      (* FIX: probably check_expr should return a list also, for consistency *)
      let err_strs =
        List.fold_left (
          fun es res -> match res with
            | Ok _ -> es
            | Error {loc=_; value} -> es ^ "\n" ^ value
        ) "" args_res in
      if err_strs <> "" then
        Error err_strs
      else
        (* could construct these further down... *)
        let args_typed = List.combine (List.map fst args) (concat_ok args_res) in
        debug_print ("#AN: actual parameter types for call: " ^
                     String.concat ","
                       (List.map (fun (_, (e: typetag expr)) -> typetag_to_string e.decor) args_typed));
        (* find the procedure entry (checking arg exprs first is eval order!) *)
        (* stitch the mutability tags back in for checking. *)
        match match_params proc.fparams args_typed with 
        | Error estr -> 
          Error ("Argument match failure for " ^ fname ^ ": " ^ estr)
        | Ok tvarmap -> 
          (* do the mutability check after other checks. *)
          let rec check_mutability = function
            | (mut, argexp)::argsrest -> (
                if not mut then check_mutability argsrest
                (* If mutable, make sure it's a var reference and mutable *)
                else match argexp.e with
                  | ExpVar varexpr -> 
                    (* Make sure containing var is mutable *)
                    if not (is_mutable_varexp syms varexpr) then
                      Error ("Variable expression " ^ exp_to_string argexp
                             ^ " cannot be passed mutably")
                    else
                      check_mutability argsrest
                  | _ ->
                    Error ("Non-variable expression "
                           ^ exp_to_string argexp ^ "cannot be passed mutably")
              )
            | [] -> Ok ()
          in
          match check_mutability args with
          | Error err -> Error err
          | Ok () ->
            (* replace return type with specified version if any *)
            (* But wait: how will we remember to cast it in codegen if it is
               a generic return type? Probably compare it to the proc return type *)
            let newrettype = specify_type tvarmap proc.rettype
            in
            debug_print ("#AN: specified return type: "
                         ^ typetag_to_string newrettype);
            Ok {e=ExpCall (fname, args_typed); decor=newrettype}
    )


(** Check that a record expression matches the given type. *)
and check_recExpr syms tenv (ttag: typetag) (rexp: locinfo expr) =
  match rexp.e with
  | ExpRecord flist ->
    let fields = get_struct_fields ttag in
    (* make a map from the fields to their types, removing them as
       they're matched. *)
    let fdict = List.fold_left (fun tmap (fi: fieldInfo) ->
        StrMap.add fi.fieldname
          (* Look for a specified type if field is generic. *)
          (match fi.fieldtype with
           | Typevar tvar -> get_typearg ttag tvar (* in the parent ttag *)
           | Namedtype _ -> fi.fieldtype (* TODO: may need to recurse *)
          ) tmap) (* HERE? Need resolved generic *)
        StrMap.empty
        fields in
    (* check field types, recursively removing from the map. *)
    let rec check_fields
        (flist: (string * locinfo expr) list)
        (accdict: typetag StrMap.t)
        (accfields: (string * typetag expr) list) =
      match flist with
      | [] ->
        if StrMap.is_empty accdict
        then Ok {e=ExpRecord accfields; decor=ttag}
        else Error {
            loc=rexp.decor;
            value=("Record field " ^ fst (StrMap.choose accdict)
                   ^ " must be defined in expression")}
      | (fname, fexp)::rest -> (
          match StrMap.find_opt fname accdict with
          | None ->
            Error {
              loc=fexp.decor;
              value=("Unknown record field name or double init: " ^ fname)
            }
          | Some ftype -> 
            (* recurse if it's a recExpr...could I get away with not? *)
            let res = match fexp.e with
              | ExpRecord _ -> check_recExpr syms tenv ftype fexp
              | _ -> check_expr syms tenv ~thint:(Some ftype) fexp in
            match res with 
            | Error err -> Error err
            | Ok eres -> 
              (* We don't want unification here, it's explicit data
                 specification. But variables of generic type should
                 work fine as-is. *)
              if subtype_match eres.decor ftype
              then check_fields rest
                  (StrMap.remove fname accdict) ((fname,eres)::accfields)
              else Error {
                  loc=fexp.decor;
                  value=("Field type mismatch: got "
                         ^ typetag_to_string eres.decor ^ ", needed "
                         ^ typetag_to_string ftype)}
        ) (* end check_fields *)
    in
    check_fields flist fdict []
  | _ -> failwith "BUG: check_recExpr called with non-record expr"


(** check a variant expression (used in both expressions and case matches) *)
and check_variant syms tenv ex ~declvar thint =
  match ex.e with 
  | ExpVariant (mname, vname, eopt) -> (
      match thint with
      (* Later we can add better variant type disambiguation. *)
      | None -> Error {loc=ex.decor;
                       value=("Cannot determine type of variant expression " ^
                              exp_to_string ex)}
      | Some ty -> (
          (* 1. the variant type exists *)
          let tname = get_type_classname ty in
          let cdata = PairMap.find (mname, tname) tenv in
          let variants = get_type_variants ty in
          (* 2. vname is a variant of it *)
          match List.find_opt (fun (vstr, _) -> vstr = vname) variants with
          | None ->
            Error {loc=ex.decor;
                   value=("Unknown variant " ^ vname ^ " of type "
                          ^ mname ^ "::" ^ tname)}
          | Some (_, tyopt) -> (
              match tyopt with
              | None -> 
                (* 3. check if the variant takes a value or not *)
                if Option.is_some eopt then
                  Error {loc=(Option.get eopt).decor;
                         value="Variant |" ^ vname
                               ^ " does not hold a value"}
                else
                  (* NOTE: replacing with the type's actual module name here. *)
                  (* Wait, I shouldn't really need to, since all the type info
                     is going in the decor. *)
                  (*Ok {e=ExpVariant (ty.modulename, vname, None); *)
                  Ok {e=ExpVariant (mname, vname, None);
                      (* TODO: generate typevars when we have them in the AST *)
                      decor=gen_ttag cdata []} 
              | Some vtype -> (
                  match eopt with
                  | None -> 
                    Error {loc=ex.decor;
                           value="Variant " ^ tname ^ "|" ^ vname
                                 ^ " requires a value"}
                  | Some e2 -> (
                      (* 4. typecheck value (if it's not a declaration in a case) *)
                      if not declvar then 
                        match check_expr syms tenv e2 with 
                        | Error err -> Error err
                        (* 5. Check that the value type and variant type match *)
                        | Ok echecked ->
                          if subtype_match echecked.decor vtype then
                            Ok {
                              e=ExpVariant (mname, vname,
                                            Some echecked);
                              decor=gen_ttag cdata []
                            }
                          else
                            Error {
                              loc=e2.decor;
                              value="Value type " ^ typetag_to_string echecked.decor
                                    ^ " Does not match variant type "
                                    ^ typetag_to_string vtype
                            }
                      else
                        Ok {e=ExpVariant (mname, vname, None);
                            decor=gen_ttag cdata []}

                    )))))
  | _ -> failwith "check_variant called without variant expr"

(** lvalue checking code for assignment contexts. Also removes from
    uninitialized symbols set. *)
and check_lvalue syms tenv (((varname, ixopt), flds) as varexpr) loc =
  match Symtable.findvar_opt varname syms with
  | None -> Error {loc=loc; value="Undefined variable " ^ varname}
  | Some (varsym, scope) -> (
      (* Check the lvalue (new), first setting as initted if applicable. *)
      if Option.is_none ixopt && flds = [] then
        (* This will be expanded to update the specific field's uninit status. *)
        (syms.uninit <- StrSet.remove varname syms.uninit;
         if scope < syms.scopedepth then 
           (* initialized from parent scope *)
           syms.parent_init <- StrSet.add varname syms.parent_init
        );
      match check_expr syms tenv {e=ExpVar varexpr; decor=loc} with
      | Error err -> Error err
      | Ok lvalexp -> 
        (* util function to check if an lvalue is assignable *)
        let rec is_assignable varsym prevmut prevty flds = 
          (* it can be non-var but still mutable *)
          match flds with
          (* still not sure if this is right for array fields *)
          | [] -> prevmut || (is_array_type varsym.symtype && varsym.mut)
          | (fname, _)::rest ->
            (* if symbol isn't mutable, fields can never be changed *)
            if not varsym.mut then false else
              match get_ttag_field prevty fname with
              | None -> failwith "BUG: field not found"
              | Some finfo ->
                (* array indexes keep the mutability of the var/field *)
                is_assignable varsym finfo.mut finfo.fieldtype rest
        in
        (* Arrays received as args are not vars but their elements 
           can be assigned if passed mutable. *)
        (* still not right, you can't assign to the whole array *)
        if not (is_assignable varsym varsym.var varsym.symtype flds) then
          Error {loc=loc;
                 value="Assignment to immutable l-value "
                       ^ exp_to_string lvalexp}
        else
          Ok lvalexp
    )


(** Check for a redeclaration (name exists at same scope) *)
(* I'm not using this yet...was a candidate for check_stmt *)
let is_redecl varname syms =
  match Symtable.findvar_opt varname syms with
  | None -> false
  | Some (_, scope) -> scope = syms.scopedepth


(** Conditionals can include an assignment, so handle them specially. *)
let check_condexp condsyms (tenv: typeenv) condexp : expr_result =
  match condexp.e with
  | ExpNullAssn (decl, (((_, _), _) as varexp), (* tyopt, *) ex) -> (
    match check_expr condsyms tenv ex with
    | Error err -> Error err
    | Ok ({e=_; decor=ety} as goodex) -> (
      if not (is_option_type ety) then
        Error { loc=condexp.decor;
                value="Nullable assignment '?=' requires a nullable rvalue" }
      (* Eliminated variable decl case, may be temporary *)
      (* else if decl then
        (* Indexed or field expressions not allowed. But actually they could be,
           right? ~if (things[1] ?= expr()) then~
           ...it couldn't initialize it, that's all. *)
        if Option.is_some ixopt || flds <> [] then
          Error {loc=condexp.decor;
                 value="var declaration must be a single name"}
        else 
          (* if a var, add it to the symbol table (down below). 
           * It can't be a redeclaration, it's the first thing in the scope! *)
          let tycheck = 
            match tyopt with
            | None -> Ok ()
            | Some tyexp -> ( (* could check this as a Decl *)
              match check_typeExpr condsyms tenv tyexp with
              | Error msg -> Error {loc=condexp.decor; value=msg}
              | Ok dty when not (types_equal dty (option_base_type ety)) ->
                 Error {loc=condexp.decor;
                        value="Declared type " ^ typetag_to_string dty
                              ^ " for variable " ^ varname
                              ^ " does not match nullable initializer type "
                              ^ typetag_to_string ety}
              | Ok _ -> Ok ()
            ) in
          match tycheck with
          | Error e -> Error e
          | Ok _ -> 
             (* add the variable to symbols. Caller will hold the modified 
                'condsyms' node *)
             Symtable.addvar condsyms varname
               {symname=varname; symtype=(option_base_type ety); var=true;
                mut=is_mutable_type ety; addr=None};
             (* rebuild the name-only varexp so it has the result type. *)
             (* UPD: I replaced tyopt with None, shouldn't be needed? *)
             Ok { e=ExpNullAssn (decl, ((varname, None), []), None, goodex);
                  decor=bool_ttag }
      *)
      else (
        (* Non-decl case, must now check the lvalue expression *)
        match check_lvalue condsyms tenv varexp condexp.decor with
           | Error err -> Error err
           | Ok {e=newlval; decor=lvalty} -> 
              if not (types_equal lvalty (option_base_type ety)) then
                Error { loc=condexp.decor;
                        value="Type mismatch in nullable assignment ("
                              ^ typetag_to_string lvalty ^ ", "
                              ^ typetag_to_string ety ^ ")" }
              else (
                match newlval with
                | ExpVar lval ->
                  (* type expression removed here too. *)
                  Ok { e=ExpNullAssn (decl, lval, (* None, *) goodex);
                       decor=bool_ttag }
                | _ -> failwith "Bug: lval expression not ExpVar"
              )
  )))
  | _ -> (
      (* Otherwise, it has to be bool *)
      debug_print "#AN: checking non-assignment conditional expr";
      match check_expr condsyms tenv condexp with
      | Error err -> Error err
      | Ok {e=_; decor=ety} as goodex ->
        if ety <> bool_ttag && not (is_option_type ety) then
          Error {
            loc=condexp.decor;
            value=("Conditional must have Boolean or nullable type, found: "
                   ^ typetag_to_string ety)
          }
        else
          goodex
  )


(* Statements need a pointer back to their symbol table for future
 * traversals, or else I need a way to pick the correct child.
 * Or, I could assume traversal in the same order. *)
(* Exprs never start their own new scope! *)
type 'a stmt_result = ((typetag, 'a st_node, locinfo) stmt, string located list)
                     Stdlib.result

(** factored out declaration typechecking code (used by globals also) *)
let typecheck_decl syms tenv (varname, tyopt, initopt) =
  if StrSet.mem varname reserved_names then
    Error ("Reserved word " ^ varname ^ " cannot be a variable name")
  else 
    (* Should I factor this logic into a try_add symtable method? *)
    match Symtable.findvar_opt varname syms with
    | Some (_, scope) when scope = syms.scopedepth ->
       Error ("Redeclaration of variable " ^ varname)
    | Some _ | None -> (
      (* check type expr and have result of option - is there a nicer way? *)
      let tyres = match tyopt with
        | None -> Ok None
        | Some dtyexp -> (
          match check_typeExpr syms tenv dtyexp with 
          | Error msg -> Error msg
          | Ok ttag ->
            debug_print ("#AN: constructed decl typetag: "
                         ^ typetag_to_string ttag);
            Ok (Some ttag) )
      in
      match tyres with
      | Error msg -> Error msg
      | Ok ttagopt -> (
        (* Check the initialization expression and its type if needed.
         * Value is a result with (ty, expr Option) pair *)
        match initopt with
        | None -> (
          match ttagopt with
          | None ->
             Error "Var declaration must have type or initializer"
          | Some decltype -> 
             Ok (None, decltype) )
        | Some initexp -> (
          match check_expr syms tenv ~thint:ttagopt initexp with
          | Error err -> Error err.value (* oops, lose precise position *)
          | Ok ({e=_; decor=ettag} as e2) -> (
            match ttagopt with
            | Some ttag ->
               if subtype_match ettag ttag then
                 Ok (Some e2, ttag)
               else
                 Error ("Declared type " ^ typetag_to_string ttag
                        ^ " for variable " ^ varname
                        ^ " does not match initializer type "
                        ^ typetag_to_string ettag)
            | None -> Ok (Some e2, ettag)
      ))))


let rec check_stmt syms tenv stm : 'a stmt_result =
  match stm.st with 
  (* Declaration: check for redeclaration, check the exp, make sure
   * types match if declared. *)
  | StmtDecl (v, tyopt, initopt) -> (
      match typecheck_decl syms tenv (v, tyopt, initopt) with
      | Error msg -> Error [{loc=stm.decor; value=msg}]
      | Ok (e2opt, vartype) -> 
        (* Everything is Ok, create symbol table structures. *)
        debug_print ("#AN: Adding symbol '" ^ v ^ "' of type "
                     ^ typetag_to_string vartype);
        Symtable.addvar syms v
          {symname=v; symtype=vartype; var=true;
           mut=is_mutable_type vartype; addr=None};
        if Option.is_none e2opt then
          syms.uninit <- StrSet.add v syms.uninit;
        Ok {st=StmtDecl (v, None, e2opt); decor=syms}
    )

  | StmtAssign (varexpr, e) -> (
      match check_lvalue syms tenv varexpr stm.decor with
      | Error err -> Error [err]
      | Ok ({e=newlval; decor=lvalty} as lvalexp) -> 
        (* check rhs expression, giving type hint *)
        match check_expr syms tenv ~thint:(Some lvalty) e with
        | Error err -> Error [err]
        | Ok ({e=_; decor=ettag} as te) ->
          debug_print "#AN: RHS of assignment checked OK. Types:";
          debug_print ("  " ^ typetag_to_string lvalty);
          debug_print ("  " ^ typetag_to_string ettag);
          (* value-assignee typecheck *)
          if not (subtype_match ettag lvalty) then
            Error [{loc=stm.decor;
                    value="Assignment type mismatch: l-value "
                          ^ exp_to_string lvalexp ^ " of type " 
                          ^ typetag_to_string lvalty ^ " can't store "
                          ^ typetag_to_string ettag}]
          else (
            debug_print "assignment subtype match completed OK";
            match newlval with
            | ExpVar lval ->
              Ok {st=StmtAssign (lval, te); decor=syms}
            | _ -> failwith "Bug: lval expression not ExpVar" )
    )

  | StmtNop -> Ok {st=StmtNop; decor=syms}

  | StmtReturn eopt -> (
      (* checks that type is return type of the enclosing function, 
       * so check_proc only needs to make sure all paths return. *)
      match syms.in_proc with
      | None ->
        (* 2021-06: is this obsolete? Only globalstmts are outside procs. *)
        Error [{loc=stm.decor;
                value="Return statement not allowed "
                      ^ "outside of procedure context"}]
      | Some inproc -> (
          match eopt with
          | None -> if inproc.rettype = void_ttag then
              Ok {st=StmtReturn None; decor=syms}
            else
              Error [{loc=stm.decor;
                      value="Cannot return void; function return type is "
                            ^ typetag_to_string inproc.rettype}]
          | Some e -> 
            (* have to have optional return type expression for void. *)
            match check_expr syms tenv ~thint:(Some inproc.rettype) e with
            | Error err -> Error [err]
            | Ok ({e=_; decor=ettag} as te) -> (
                if not (subtype_match ettag inproc.rettype) then
                  Error [{loc=stm.decor;
                          value="Return type mismatch: needed "
                                ^ typetag_to_string inproc.rettype
                                ^ ", found " ^ typetag_to_string ettag}]
                else Ok {st=StmtReturn (Some te); decor=syms}
              )))

  | StmtIf (condexp, thenbody, elsifs, elseopt) -> (
      let thensyms = Symtable.new_scope syms in 
      match check_condexp thensyms (* condsyms *) tenv condexp with
      | Error err -> Error [err]
      | Ok newcond -> (
          (* let thensyms = Symtable.new_scope condsyms in *)
          match check_stmt_seq thensyms tenv thenbody with
          | Error errs -> Error errs
          | Ok newthen -> (
              let elsifs_result = (* this will be a big concat. *)
                let allres =
                  List.map (fun (elsifcond, blk) ->
                      let elsifsyms = Symtable.new_scope syms (*condsyms*) in
                      match check_condexp elsifsyms tenv elsifcond with
                      | Error err -> Error [err]
                      | Ok newelsifcond -> (
                          match check_stmt_seq elsifsyms tenv blk with
                          | Error errs -> Error errs
                          (* return the elsif symbol tables for checking inits. *)
                          | Ok newblk -> Ok ((newelsifcond, newblk), elsifsyms)
                        ))
                    elsifs
                in
                if List.exists Result.is_error allres then
                  Error (concat_errors allres)
                else
                  Ok (concat_ok allres)
              in
              match elsifs_result with
              | Error errs -> Error errs
              | Ok elsifres -> (
                  let newelsifs = List.map fst elsifres in
                  let elsifsyms = List.map snd elsifres in 
                  match elseopt with 
                  | None -> Ok {st=StmtIf (newcond, newthen, newelsifs, None);
                                decor=syms (* thensyms *)}
                  | Some elsebody -> 
                    let elsesyms = Symtable.new_scope (* condsyms *) syms in
                    match check_stmt_seq elsesyms tenv elsebody with
                    | Error errs -> Error errs
                    | Ok newelse -> 
                      if not (StrSet.is_empty syms.uninit) then (
                        (* intersect all parent-initted symbols of the blocks. *)
                        let init_ifelse =
                          StrSet.inter thensyms.parent_init elsesyms.parent_init in
                        let initted_by_all =
                          List.fold_left StrSet.inter init_ifelse
                            (List.map (fun nd -> nd.parent_init) elsifsyms) in
                        (* print_string ("Initted by all blocks: "
                                      ^ StrSet.fold (fun v acc -> acc ^ ", " ^ v)
                                          initted_by_all "" ^ "\n"); *)
                        (* remove from uninitialized. *)
                        syms.uninit <-
                          (* It's a right fold. *)
                          StrSet.fold StrSet.remove initted_by_all syms.uninit
                      );
                      Ok {st=StmtIf (newcond, newthen, newelsifs, Some newelse);
                          decor=syms (* thensyms *)}
                ))))

  | StmtWhile (cond, body) -> (
      let whilesyms = Symtable.new_scope syms in 
      match check_condexp whilesyms tenv cond with
      | Error err -> Error [err]
      | Ok newcond -> (
          (* let bodysyms = Symtable.new_scope condsyms in *)
          match check_stmt_seq whilesyms tenv body with
          | Error errs -> Error errs
          | Ok newbody -> Ok {st=StmtWhile (newcond, newbody); decor=whilesyms}
        ))

  | StmtCase (matchexp, caseblocks, elseopt) -> (
      (* check the top (match) expression. *)
      match check_expr syms tenv matchexp with
      | Error err -> Error [err]
      | Ok matchexp ->
        let mtype = matchexp.decor in
        (* check all case blocks, accumulating cases for exhaustiveness *)
        let rec check_cases
            (cblocks: ('ed expr * ('ed,'sd,'tt) stmt list) list) caseacc =
          match cblocks with
          | (cexp, cbody)::rest -> (
              let errout msg = Error [{value=msg; loc=cexp.decor}] in
              (* the last piece, indepdendent of the type of match exp *)
              let check_casebody (cexp: typetag expr) caseval cbody blocksyms = 
                match check_stmt_seq blocksyms tenv cbody with
                | Error errs -> Error errs
                | Ok newcbody -> (
                    match check_cases rest (caseval::caseacc) with
                    | Ok blocks -> Ok ((cexp, newcbody)::blocks)
                    | Error errs -> Error errs
                  ) in
              (* 1. check the case expression *)
              match cexp.e with 
              (* expression-type-specific stuff starts here. *)
              | ExpVariant (modname, vntname, eopt) -> (
                  (* typecheck as an expression but skip the variable if any *)
                  match check_variant syms tenv cexp ~declvar:true (Some mtype) with
                  | Error err -> Error [err]
                  | Ok checkedcexp -> (
                      let casetype = checkedcexp.decor in 
                      if not (types_equal casetype mtype) then
                        errout ("Case type " ^ typetag_to_string casetype
                                ^ " does not match match expression type "
                                ^ typetag_to_string mtype)
                      else (
                        (* get type of this specific case's value, if it has one *)
                        let (_, vnttyopt) =
                          List.find (fun (vn, _) -> vntname = vn)
                            (get_type_variants casetype) in
                        if List.exists ((=) vntname) caseacc then 
                          errout ("Duplicate variant case " ^ "|" ^ vntname)
                        else
                          match eopt with (* result.fold? join? bind? *)
                          | None -> 
                            let newcexp =
                              {e=ExpVariant(modname, vntname, None);
                               decor=matchexp.decor} in
                            let blocksyms = Symtable.new_scope syms in
                            check_casebody newcexp vntname cbody blocksyms
                          | Some cvalexp ->
                            match cvalexp.e with
                            | ExpVar ((cvar, None), []) -> (
                                let vntty = Option.get vnttyopt in
                                let (newcexp: typetag expr) =
                                  {e=ExpVariant(
                                       modname, vntname,
                                       Some {e=ExpVar((cvar, None), []);
                                             decor=vntty});
                                   decor=matchexp.decor} in
                                let blocksyms = Symtable.new_scope syms in
                                Symtable.addvar blocksyms cvar {
                                  symname=cvar;
                                  symtype=vntty;
                                  var=false;
                                  mut=is_mutable_type vntty; (*correct?*)
                                  addr=None 
                                };
                                debug_print (st_node_to_string blocksyms);
                                check_casebody newcexp vntname cbody blocksyms
                              )
                            | _ -> errout ("Variant case value expression must "
                                           ^ "be a single variable name")
                      )))
              (* val() expression type, to match any non-null nullable *)
              | ExpVal varexpr -> (
                  if not (is_option_type mtype) then
                    errout "val() case can only be used with nullable expressions"
                  else if List.exists ((=) "val") caseacc then 
                    errout ("Duplicate val() case ")
                  else 
                    match varexpr.e with 
                    | ExpVar ((valvar, None), []) -> (
                        let valty = (option_base_type mtype) in
                        let (newcexp: typetag expr) =
                          {e=ExpVal({e=ExpVar((valvar, None), []); decor=valty});
                           decor=matchexp.decor} in
                        (* Add the variable to the symtable *)
                        let blocksyms = Symtable.new_scope syms in
                        Symtable.addvar blocksyms valvar {
                          symname=valvar;
                          symtype=valty;
                          var=false;
                          mut=is_mutable_type valty; (* might want to poke it *)
                          addr=None 
                        };
                        debug_print (st_node_to_string blocksyms);
                        check_casebody newcexp "val" cbody blocksyms
                      )
                    | _ -> errout ("val expression must contain"
                                   ^ " a single variable name")
                )
              | caseexpr -> (* any other expression type *)
                (* check that it's a constexpr *)
                let cexpstr = exp_to_string cexp in
                if not (is_const_expr caseexpr) then
                  errout "Case matches must be constant expressions"
                else if List.exists ((=) cexpstr) caseacc then 
                  errout ("Duplicate case value " ^ cexpstr)
                else (
                  (* check expr and verify same type as matchexp *)
                  match check_expr syms tenv ~thint:(Some mtype) cexp with
                  | Error err -> Error [err]
                  | Ok checkedcexp ->
                    let casetype = checkedcexp.decor in
                    if (is_option_type mtype) then
                      (* at least for now, don't allow specific values of a 
                         nullable *)
                      if casetype <> null_ttag then
                        errout ("Case of a nullable expression may only be "
                                ^ "'null' or 'val()'")
                        (* if (casetype <> {mtype with nullable=false})
                           && (casetype <> null_ttag) then *)
                        (* errout ("Case type " ^ typetag_to_string casetype
                              ^ " is not an instance of nullable match "
                              ^ "expression type " ^ typetag_to_string mtype) *)
                      else
                        let blocksyms = Symtable.new_scope syms in
                        check_casebody checkedcexp cexpstr cbody blocksyms
                    else if not (types_equal casetype mtype) then
                      errout ("Case value type " ^ typetag_to_string casetype
                              ^ " does not match match expression type "
                              ^ typetag_to_string mtype)
                    else
                      let blocksyms = Symtable.new_scope syms in
                      check_casebody checkedcexp cexpstr cbody blocksyms
                )
            )
          | [] ->
            if is_variant_type mtype then 
              (* can I just set this to 2 if it's nullable? and add the cases 
                  above for nullables *)
              let nvariants = List.length (get_type_variants mtype) in
              (* check for exhaustiveness here, for now just by comparing lengths*)
              if List.length caseacc < nvariants
              && Option.is_none elseopt then
                Error [{value="Case statement is not exhaustive";
                        loc=stm.decor}]
              else if List.length caseacc = nvariants
                   && Option.is_some elseopt then
                Error [{value="Unreachable else block; "
                              ^ "cases cover all variants";
                        loc=stm.decor}] (* get location in ese block instead? *)
              else
                Ok []
            else              
            if Option.is_none elseopt then
              Error [{value="Case statements that are not for variants or "
                            ^ "nullables need an else block";
                      loc=stm.decor}]
            else 
              Ok []
        in (* end check_cases *)
        match check_cases caseblocks [] with
        | Error errs -> Error errs
        | Ok newcblocks -> (
            match elseopt with
            | None -> 
              Ok {st=StmtCase (matchexp, newcblocks, None); decor=syms}
            | Some eblock ->
              let blocksyms = Symtable.new_scope syms in
              match check_stmt_seq blocksyms tenv eblock with
              | Error errs -> Error errs
              | Ok neweblock ->
                Ok {st=StmtCase (matchexp, newcblocks, Some neweblock);
                    decor=syms}
          ))

  | StmtCall ex -> (
      match ex.e with
      | ExpCall (fname, args) -> (
          match check_call syms tenv (fname, args) with
          | Error msg -> Error [{loc=stm.decor; value=msg}]
          | Ok newcallexp -> (
              (* non-void call can't be a standalone statement. *)
              match Symtable.findproc_opt fname syms with
              | None -> failwith "BUG: proc name was previously found OK."
              | Some (entry, _) when entry.rettype <> Types.void_ttag ->
                Error [{loc=stm.decor;
                        value="Non-void return type must be assigned."}]
              | _ -> Ok {st=StmtCall newcallexp; decor=syms}
            ))
      | _ -> failwith "BUG: Call statement with non-call expression"
    )

(*  | StmtBlock stlist ->
    let blockscope = Symtable.new_scope syms in
    match check_stmt_seq blockscope tenv stlist with
    | Error errs -> Error errs
    | Ok newstmts -> Ok {st=StmtBlock newstmts; decor=blockscope}
*)

(** Check a list of statements. Adds test for unreachable code. *)
and check_stmt_seq syms tenv sseq =
  let rec check' acc stmts = match stmts with
    | [] -> List.rev acc
    | stmt::rest -> (
        let res = check_stmt syms tenv stmt in
        debug_print "#AN: statement check completed";
        match stmt.st with
        | StmtReturn _ when rest <> [] ->
          let unreach = Error [{loc=stmt.decor;
                                value="Unreachable code after return"}] in
          check' (unreach::res::acc) rest
        | _ -> check' (res::acc) rest
      )
  in
  let results = check' [] sseq in
  (* let results = List.map (check_stmt syms tenv) sseq in  *)
  if List.exists Result.is_error results then
    (* Make one error list out of all. Matches stmt_result. *)
    Error (concat_errors results)
  else
    (* Make one Ok out of the list of results. NOT a stmt_result. *)
    Ok (concat_ok results)


(** Determine if a block of statements returns on every path.
  * Return types and unreachable code are checked elsewhere. *)
let rec block_returns stlist =
  (* If I add a break statement, this also has to make sure it doesn't happen
   * before a return. *)
  match stlist with
  | [] -> false 
  | stmt::rest -> (
    match stmt.st with
    | StmtReturn _ -> true
    | StmtDecl _ | StmtAssign _ | StmtNop | StmtCall _ -> block_returns rest
    (* | StmtBlock slist -> block_returns slist || block_returns rest *)
    | StmtIf (_, thenblk, elsifs, elsblock) -> (
      (* If all paths return, then OK, else must return after. *)
      match elsblock with
      | None -> block_returns rest
      | Some elsblock -> (
        if block_returns thenblk
           && List.for_all (fun (_, elsif) -> block_returns elsif) elsifs
           && block_returns elsblock then true
        else block_returns rest ))
    | StmtWhile (_, _) ->
       (* While body may never be entered, so can't guarantee *)
       block_returns rest
    | StmtCase (_, caseblocks, elseopt) -> (
      (* case statements will be exhaustiveness-checked, so the function
       * returns if all present cases return *)
      let rets =
        List.for_all (fun (_, blk) -> block_returns blk) caseblocks
        && (match elseopt with
            | None -> true
            | Some eblk -> block_returns eblk)
      in rets || block_returns rest
    )
  )


(** Check a procedure declaration and add it to the given symbol node. *)
let check_procdecl syms tenv modname (pdecl: ('loc, 'loc) procdecl)
  : ((('a st_node, 'loc) procdecl * 'a st_procentry), 'er) result =
  (* Helper function to construct error result *)
  let errout msg = Error [{loc=pdecl.decor; value=msg}] in
  (* 0. Initial correctness checks *)
  if StrSet.mem pdecl.name reserved_procnames then
    errout ("Reserved name " ^ pdecl.name ^ " cannot be a procedure name")
  else if modname = "" && pdecl.visibility = Export then
    errout ("\"export\" qualifier is redundant for top-level module")
  else
    (* 1. check procedure name for redeclaration. Is scope check needed? *)
    match Symtable.findproc_opt pdecl.name syms with
    | Some (_, scope) when syms.scopedepth = scope ->
       errout ("Redeclaration of procedure " ^ pdecl.name)
    | _ -> (
      (* 2. Check generic type parameter declarations. *)
      (* loop through typeparams and add to symtables, error for repeats. *)
      let tparams_result =
        List.fold_left (fun resacc tv ->
            (* Hmm, we're just using the fold to propagate the error here. *)
            match resacc with
            | Error e -> Error e
            | Ok _ -> (
                match Symtable.findtvar_opt tv syms with
                | Some _ -> errout ("Redeclaration of type parameter " ^ tv)
                | None ->
                  Symtable.addtvar syms tv [];
                  Ok ()
              )) (Ok ()) pdecl.typeparams in
      match tparams_result with
      | Error e -> Error e (* have to do this to reconstruct result obj *)
      | Ok () -> 
        (* 3. Typecheck arguments *)
        let argchecks = List.map (fun (_, _, texp) ->
            check_typeExpr syms tenv texp)
                        pdecl.params in
        if List.exists Result.is_error argchecks then
        (* can't exactly use concat_errors here because typeExpr check
         * errors are strings, not list. But should still simplify this. *)
          let errs =
            concat_map (
              fun r -> match r with
                       | Ok _ -> []
                       | Error msg -> [{loc=pdecl.decor; value=msg}]
            ) argchecks
        in Error errs
        else
          let argtypes = concat_ok argchecks in
          (* We no longer put the typetags in the params *)
          (* let checkedparams = List.map2
              (fun (m, nm, _) argty -> (m, nm, argty))
              pdecl.params argtypes in *)
          (* check that any mutability markers on parameters are allowable. *)
          let rec check_mutparams (argtypes: typetag list) params =
            match (argtypes, params) with
            | (argtype::argsrest, (mut, _, _)::paramsrest) ->
              (* arrays are mutable. Should I make a helper function for this? *)
              if mut && not (is_mutable_type argtype)
              then Error {loc=pdecl.decor;
                          value="Type " ^ typetag_to_string argtype
                                ^ " is immutable and cannot be passed mutable" }
              else check_mutparams argsrest paramsrest
            | ([], []) -> Ok ()
            | _ -> failwith "BUG: param types and param list length mismatch"
          in
        match check_mutparams argtypes pdecl.params with
        | Error err -> Error [err]
        | Ok _ -> 
          (* Build symbol table entries for params *)
          let paramentries =
            List.map2 (
              fun (mut, paramname, _ (* typeExp, not needed*)) argtype ->
                {symname = paramname; symtype=argtype;
                 var=false; mut=mut; addr=None}
            ) pdecl.params argtypes
          in
           (* Code to build symbol table entries for fields of all params
              used to be here *)
           (* Typecheck return type *)
           match check_typeExpr syms tenv pdecl.rettype with
           | Error msg -> Error [{loc=pdecl.decor; value=msg}]
           | Ok rttag -> (
               (* Create procedure symtable entry.
                  * is this where I do private, by just not making it?
              * Don't add it to module symtable node here; caller does it. *)
               let procentry =
                 (* may get rid of export later. For now, handy for testing *)
                 {procname=(if modname = "" || pdecl.visibility = Export
                            then pdecl.name
                            else modname ^ "::" ^ pdecl.name);
                  rettype=rttag; fparams=paramentries} in
             (* create new inner scope under the procedure, and add args *)
             (* Woops, it creates a "dangling" scope if proc isn't defined *)
               let procscope = Symtable.new_proc_scope syms procentry in
               (* Should I add the proc to its own symbol table? Don't see why. *)
               (* Did I do this so codegen for recursive calls "just works"? *)
             Symtable.addproc procscope pdecl.name procentry;
             List.iter (fun param ->
                 (* print_endline ("Adding param symbol " ^ param.symname); *)
                 Symtable.addvar procscope param.symname param) paramentries;
             Ok ({pdecl with decor=procscope},
             (* Yay, simpler! We no longer put the typetag in decls. *)
             (*Ok ({name=pdecl.name; typeparams=pdecl.typeparams;
                  params=checkedparams; rettype=pdecl.rettype; export=pdecl.export;
                  decor=procscope}, *)
                 procentry)
           ))


(** Check the body of a procedure whose header has already been checked 
  * (and had its parameters added to the symbol table) *)
let check_proc tenv (pdecl: ('addr st_node, 'l) procdecl) proc =
  debug_print ("#AN: About to check procedure " ^ pdecl.name);
  let procscope = pdecl.decor in
  match check_stmt_seq procscope tenv proc.body with
  | Error errs -> Error errs
  | Ok newslist ->
    debug_print "checked procedure with no errors";
    let rettype = (Symtable.getproc pdecl.name procscope).rettype in
    if rettype <> void_ttag && not (block_returns proc.body) then 
      Error [{loc=proc.decor;
              value="Non-void procedure " ^ pdecl.name
                    ^ " does not return a value on every execution path"}]
    else
      (* procedure's decoration is its inner symbol table *)
      Ok {decl=pdecl; body=newslist; decor=procscope}


(** Check a global declaration statement (needs const initializer) and
    generate symtable entry. *)
let check_globdecl syms tenv modname gstmt
  : (('ed, 'sd, locinfo) globalstmt, _) result =
  match gstmt.init with
  (* could do this syntactically...but error messages are better here. *)
  | None -> Error [{loc=gstmt.decor;
                    value="Globals must be initialized when declared"}]
  | Some initexp when not (is_const_expr initexp.e) ->
     Error [{loc=initexp.decor;
             value="Global initializer must be constant expression"}]
  | Some _ -> (
    match typecheck_decl syms tenv
            (gstmt.varname, gstmt.typeexp, gstmt.init) with
    | Error msg -> Error [{loc=gstmt.decor; value=msg}]
    | Ok (e2opt, vartype) ->
       (* add to symtable *)
       let varname = modname ^ "::" ^ gstmt.varname in
       Symtable.addvar syms gstmt.varname {
           symname=varname;
           symtype=vartype;
           var=true;
           mut=is_mutable_type vartype;
           addr=None
         };
       Ok {varname=gstmt.varname; typeexp=None; (* removed gstmt.typeexp; *)
           init=e2opt; decor=syms}
  )


(** Check a type definition, generating classData for the tenv. *)
let check_typedef syms tenv modname (tdef: (locinfo, _) typedef)
  : (classData, _) result = 
  (* check for typename redeclaration *)
  match PairMap.find_opt ("", tdef.typename) tenv with
  | Some _ ->
     Error [{ loc=tdef.decor;
              value="Type redeclaration: " ^ tdef.typename }]
  | None -> (
    (* Add type variables to symtable, catching repeats *)
    let tvarres =
      tdef.typeparams
      |> List.fold_left (fun res tv ->
             match res with
             | Error err -> Error err
             | Ok _ -> (
               match Symtable.findtvar_opt tv syms with
               | Some _ ->
                  Error [{loc=tdef.decor;
                          value=("Redeclared type variable " ^ tv)}]
               | None ->
                  Symtable.addtvar syms tv [];
                  Ok ()))
           (Ok ())
    in
    match tvarres with
    | Error err -> Error err
    | Ok _ -> (
        (* Match what kind of type it is and do detailed checking. *)
      match tdef.kindinfo with
      | Fields fields ->
        (* Check fields of a struct type declaration. Check for
           nonexistent types, field redeclaration.
           Not-found types get a placeholder class if they're recursive. *)
        let rec check_fields flist acc = match flist with
          | [] -> Ok (List.rev acc)
          | fdecl :: rest ->
            if List.exists (fun (fi : fieldInfo) ->
                fi.fieldname = fdecl.fieldname) acc then
              Error [{ loc=fdecl.decor;
                       value="Field redeclaration " ^ fdecl.fieldname }]
            else
              (* see if class exists ourselves, add dummy to tenv? *)
              match check_typeExpr syms tenv fdecl.fieldtype with
              | Error e ->
                if not tdef.rectype then
                  Error [{loc=fdecl.decor; value="Field type error: " ^ e}]
                else (
                  (* construct typetag and finfo for forward-defined field. *)
                  debug_print ("#AN: Creating placeholder for recursive field "
                               ^ "'" ^ fdecl.fieldname ^ "'");
                  let dummyClass = {
                    classname = get_texp_classname fdecl.fieldtype; 
                    in_module = modname;
                    opaque=false; muttype=false; rectype=true;
                    tparams=[]; kindData=Hidden
                  } in
                  (* gen_ttag insufficient, may be nullable *)
                  let ttag = gen_ttag dummyClass [] (*
                    { (* should have a ttag_of_texpr function?
                          that's what check_texpr should do *)
                      modulename = modname;
                      typename = fdecl.fieldtype.classname;
                      tclass = dummyClass;
                      array = fdecl.fieldtype.array;
                      paramtypes = [];
                      nullable = fdecl.fieldtype.nullable;} *)
                  in
                  let finfo = {
                    fieldname=fdecl.fieldname; priv=fdecl.priv;
                    mut=fdecl.mut;
                    fieldtype = ttag
                  } in
                  check_fields rest (finfo::acc))
              | Ok (Namedtype tinfo) -> 
                let finfo = {
                  fieldname=fdecl.fieldname; priv=fdecl.priv;
                  mut=fdecl.mut;
                  fieldtype = Namedtype tinfo
                  } in check_fields rest (finfo::acc)
              | Ok (Typevar tv) -> (
                match Symtable.findtvar_opt tv syms with
                | None ->
                   Error [{loc=fdecl.decor;
                           value=("Undeclared type variable " ^ tv)}]
                | Some _ ->
                   let finfo = {
                       fieldname=fdecl.fieldname; priv=fdecl.priv;
                       mut=fdecl.mut; (* Generic fields can be reassigned, right? *)
                       fieldtype = Typevar tv
                     } in check_fields rest (finfo::acc))
       in 
       (match check_fields fields [] with
        | Error e -> Error e
        | Ok flist -> 
           Ok {
               (* construct the classData for the entire struct type. *)
               classname = tdef.typename;
               in_module = modname;
               opaque = tdef.opaque;
               muttype = List.exists (fun (finfo: fieldInfo) ->
                   (* If either the field itself is mutable or its type is. *)
                   finfo.mut || is_mutable_type finfo.fieldtype) flist;
               rectype = tdef.rectype;
               tparams = tdef.typeparams;
               (* for generics: generate field info with same type
                  variables as outer *)
               kindData = Struct flist;
             }
       )
    | Variants variants -> (
       let rec check_variants vdecllist accres =
         match vdecllist with
         | [] -> Ok accres
         | vdecl :: rest ->
            (* check for name reuse, then check the expression itself *)
            if List.exists
                 (fun vd -> vd.variantName = vdecl.variantName) rest then
              Error [{ loc=tdef.decor;
                       value="Name " ^ vdecl.variantName
                             ^ " reused in variant" }]
            else
              match vdecl.variantType with
              | Some vtexp -> (
                  match check_typeExpr syms tenv vtexp with
                  | Error e ->
                    if not tdef.rectype then
                      Error [{loc=tdef.decor;
                              value="Variant subtype error: " ^ e}]
                    else
                      (* construct placeholder for forward-defined class. *)
                      let dummyClass = {
                        classname = get_texp_classname vtexp;
                        in_module = modname;
                        opaque=false; muttype=false; rectype=true;
                        tparams=[]; kindData=Hidden
                      } in 
                      let ttag = gen_ttag dummyClass []
                        (* {
                        modulename = modname;
                        typename = vtexp.classname;
                        tclass = dummyClass;
                        array = vtexp.array;
                        paramtypes = [];
                        nullable = vtexp.nullable;
                           } *)
                      in
                      check_variants rest ((vdecl.variantName, Some ttag)::accres)
                  | Ok ttag ->
                    check_variants rest ((vdecl.variantName, Some ttag)::accres)
                )
              | None -> (* bare-name variant *)
                check_variants rest ((vdecl.variantName, None)::accres)
       in
       match check_variants variants [] with
       | Error elist -> Error elist
       | Ok variants ->
          (* Value constructors are NOT currently function symbols. 
             They are a separate type of expression. *)
          (* Similarly, nullary constructors aren't added to the variable table. 
             But they can be constexprs. *)
          Ok {
              classname = tdef.typename;
              in_module = modname;
              opaque = tdef.opaque;
              (* Should variant types be immutable always? Need to think. *)
              muttype = List.exists
                  (fun st -> Option.is_some (snd st)
                             && is_mutable_type (Option.get (snd st))
                  ) variants;
              rectype = tdef.rectype;
              tparams = [];
              kindData = Variant variants
            }
     )
    | Newtype tyex -> (
        match tyex.texpkind with
        | Generic _ -> Error [{value="Cannot create newtype of generic type";
                             loc=tdef.decor}]
        | Concrete ctex -> 
          match PairMap.find_opt (ctex.modname, ctex.classname) tenv with
        | None ->
          Error [{value="Unknown type name " ^ typeExpr_to_string tyex;
                  loc=tdef.decor}]
        (* Create a whole new type with the same properties as the root type *)
        (* Hmmm.. may even want to have a reference to the type it is,
           for assigning values. Then update type matching! *)
        (* For Generics: Make sure type params match up.
           example: newtype StrDict(t) is Dict(String, t); *)
        | Some cdata -> 
          Ok {
            classname = tdef.typename;
            in_module = modname; (* defined in this module now *)
            muttype = cdata.muttype;
            rectype = cdata.rectype;
            opaque = cdata.opaque;
            tparams = cdata.tparams;
            (* construct a tag for the underlying type *)
            kindData = Newtype (
                Namedtype {
                  modulename = modname;
                  tclass = {cdata with classname = tdef.typename;
                                       in_module = modname};
                  typeargs = [] (* TOFIX *)
              })
          })
    | Hidden ->
      Ok {
        classname = tdef.typename;
        in_module = modname;
        opaque = true;
        muttype = true; (* Can't assume it's not mutable,
                           it's based on what's called *)
        rectype = false; (* doesn't matter, it's a pointer anyway?? *)
        tparams = [];
        kindData = Hidden
      }
  ))


(** From imported module specs, add types and global var/proc symbols. *)
let add_imports syms tenv specs istmts = 
  (* Even if you open a module, you should remember which module the 
   * function came from, for error messages *)
  (* Maybe var symbols can have a 'parent_struct' that could either be a 
     proc or a type or a module. Namespace? *)
  (* helper function to append to errors (list of string located) *)
  let add_import_notice errlist =
    List.map (fun sloc ->               
        {sloc with value=(sloc.value ^ " (in included modspec)")})
      errlist
  in 
  (* Construct the right names to use from the statements. *)
  (* check type definitions and add to tenv. *)
  let rec check_importtypes modname modalias tdefs tenv_acc =
    match tdefs with
    | [] -> Ok tenv_acc
    | td::rest ->
       match check_typedef syms tenv_acc modname td with
       | Ok cdata ->
          let newtenv =
            (* need to add unqualified type name for modspecs *)
            PairMap.add (modalias, cdata.classname) cdata tenv_acc
            |> PairMap.add (modname, cdata.classname) cdata in
          check_importtypes modname modalias rest newtenv
       | Error es -> Error (add_import_notice es)
                         
  in
  (* global variables and procs done together, both create symbols *)
  let check_importdecls modname prefix tenv the_spec = 
    (* Iterate over global variable declarations and add to symtable *)
    List.map (
        fun (gdecl: ('et,'st) globaldecl) ->
        let refname = prefix ^ gdecl.varname in
        (* only codegen should make it a dot name? *)
        let fullname = modname ^ "::" ^ gdecl.varname in
        match check_typeExpr syms tenv gdecl.typeexp with
        | Error msg ->
           Error [{value=msg ^ " (in imported modspec)"; loc=gdecl.decor}] 
        | Ok ttag -> (
          match Symtable.findvar_opt refname syms with
          | Some (_, _) ->
             Error [{value=("Extern variable name clash:" ^ refname);
                     loc=gdecl.decor}]
          | None ->
             Symtable.addvar syms refname {
                 (* Keep the original module name internally. *)
                 symname = fullname; symtype = ttag; 
                 var = true; mut=is_mutable_type ttag; addr = None
               };
             (* Add field initializers too. Not anymuer! *)
             (* List.iter (add_field_sym syms refname true) ttag.tclass.fields; *)
             (* Don't think we want to add both names in this context. *)
             (* if refname <> fullname then
                Symtable.addvar syms fullname entry; *)
             Ok syms (* doesn't get used *)
      )) the_spec.globals
    (* iterate over procedure declarations and add those. *)
    @ (List.map ( (* need to fold-map now to keep new pdecls? *)
             fun (pdecl: ('ed, 'sd) procdecl) ->
             let refname = prefix ^ pdecl.name in
             let fullname = modname ^ "::" ^ pdecl.name in
             (* check_procdecl now gets module name prefix from AST. *)
             match check_procdecl syms tenv modname pdecl 
             (* { pdecl with name=(prefix ^ pdecl.name) } *) with
             | Ok (_, entry) ->
                Symtable.addproc syms refname entry;
                if refname <> fullname then 
                  Symtable.addproc syms fullname entry;
                Ok syms
             | Error errs -> Error (add_import_notice errs)
           ) the_spec.procdecls
      ) (* end check_importdecls *)
    in
    let rec mainloop stmts tenv_acc modnames =
      match stmts with
      | [] -> Ok (syms, tenv_acc) (* return value of outer function *)
      | istmt::rest -> (
        (* get the module names to be used in the symtable and tenv. *)
        let (modname, modalias) = match istmt.value with
          | Import (modname, aliasopt) -> (
            match aliasopt with
            | Some alias -> (modname, alias)
            | None -> (modname, modname) )
          | Open modname -> (modname, "") in
        if List.mem modname modnames then
          Error [{value="Duplicate module import " ^ modname;
                  loc=istmt.loc}]
        else 
          let prefix = if modalias = "" then "" else modalias ^ "::" in
          (* Get the modspec from the preloaded list. *)
          let the_spec = StrMap.find modname specs in
          (* Call the function to check and add imported types *)
          match
            check_importtypes modname modalias the_spec.typedefs tenv_acc with
          | Error errs -> Error errs
          | Ok newtenv -> (
            (* Check and add import declarations (vars and procs) *)
            match concat_errors
                    (check_importdecls modname prefix newtenv the_spec) with
            | [] -> mainloop rest newtenv (modname::modnames)
            | errs -> Error errs
      )) (* end mainloop *)
    in mainloop istmts tenv []


(** Check one entire module, rewriting each AST component. *)
let check_module syms (tenv: typeenv) ispecs
    (dmod: (locinfo, 'sd, locinfo) dillmodule)
  : ((typetag, 'a st_node, locinfo) dillmodule * 'tenv, 'er) result =
  (* Check import statements and load modspecs into symtable
     (they've been loaded from .dms files by the top level) *)
  match add_imports syms tenv ispecs dmod.imports with
  | Error errs -> Error errs 
  | Ok (syms, tenv) -> (  (* It's the same symtable node that's passed in... *)
      (* print_typekeys tenv; *)
      (* Create a new scope to add all locally-defined things below imports. *)
      let syms = Symtable.new_scope syms in
      (* create tenv entries (classdata) for type definitions *)
      let typesres =
        List.fold_left (fun acc td ->
            match acc with
            (* have to check twice to bubble the error up. *)
            | Error e -> Error e
            | Ok (tenv, classes) -> (
                match check_typedef syms tenv dmod.name td with
                (* Though we add classdatas to the tenv, we keep handles
                   to them also, for the fixup to recursive types *)
                | Ok cdata ->
                Ok (PairMap.add ("", cdata.classname) cdata tenv,
                    cdata :: classes)
                | Error e -> Error e
              ))
          (Ok (tenv, [])) dmod.typedefs
      in
      match typesres with
      | Error e -> Error e
      | Ok (tenv, newclasses) ->
        debug_print ("#AN: checking " ^ string_of_int (List.length newclasses)
                     ^ " typeclasses for recursive updates");
        (* update recursive type fields with completed classData *)
        List.iter (
          fun (cdata: classData) -> if cdata.rectype then
            match cdata.kindData with
            | Struct finfos -> 
              finfos |> List.iter (fun (finfo: fieldInfo) ->
                  if is_recursive_type finfo.fieldtype then (
                    let finishedClass = PairMap.find
                        ("", get_type_classname finfo.fieldtype) tenv in
                    debug_print ("#AN-check_module: Updating classData for field "
                                 ^ finfo.fieldname ^ " of " ^ cdata.classname);
                    set_type_class finfo.fieldtype finishedClass
                  ))
            | Variant vlist -> 
              vlist |> List.iter (fun (vname, vtopt) -> (
                    match vtopt with
                    | Some vttag ->
                      if is_recursive_type vttag then (
                        debug_print ("-searching for completed classname "
                                     ^ get_type_classname vttag);
                        let finishedClass = PairMap.find
                            ("", get_type_classname vttag) tenv in
                        debug_print ("#AN-check_module: Updating classData "
                                     ^ "for variant "
                                     ^ vname ^ " of " ^ cdata.classname);
                        set_type_class vttag finishedClass 
                      )
                    | None -> ()
                  ))
            | _ -> ()
        ) newclasses;
        debug_print ("-- module types in tenv: " ^ string_of_tenv tenv);
        (* spam syms into the decor of the AST typedefs to update the decor type.
           Could there be a better way? check_typedef should return a new
           typedef itself. I think that's all there is to it. *)
        let newtypedefs: ('a st_node, 'l) typedef list =
         List.map (fun tdef -> {tdef with decor=syms}) dmod.typedefs in
      (*match tdef.kindinfo with
            (* using fake null_ttag *)
            | Fields fields ->
                let newfields =
                  List.map (fun (fd: locinfo fieldDecl) ->
                      {fd with decor=null_ttag})
                    fields in
                {tdef with kindinfo=(Fields newfields); decor=syms}
            | Variants variants ->
                let newvariants =
                  List.map (fun (vd: locinfo variantDecl) ->
                      {vd with decor=null_ttag}) variants in
                {tdef with kindinfo=Variants newvariants; decor=syms}
            | Newtype texpr -> 
              let newtexpr: typetag expr = {
                texpkind = match texpr.texpkind with
                  | Generic s -> Generic s
                  | Concrete cte

                in 
               (* Need to replace the texpr with the typetag *)
              {tdef with kindinfo=Newtype newtexpr; decor=syms}
            | Hidden ->
               {tdef with kindinfo=Hidden; decor=syms}
          ) dmod.typedefs in
                        debug_print "#AN: Finished remapping decor of typedefs"; *)
       (* Check global declarations *)
        let globalsrlist = List.map (check_globdecl syms tenv dmod.name)
            dmod.globals in
        if List.exists Result.is_error globalsrlist then
          Error (concat_errors globalsrlist)
        else
          let newglobals = concat_ok globalsrlist in
          (* Check procedure decls first, to add to symbol table *)
          let pdeclsrlist = List.map (fun proc ->
              check_procdecl syms tenv dmod.name proc.decl)
              dmod.procs in
          if List.exists Result.is_error pdeclsrlist then
            Error (concat_errors pdeclsrlist)
          else
            let newpdecls = 
              List.map (fun ((pd: ('a st_node, locinfo) procdecl), pentry) ->
                  Symtable.addproc syms pd.name pentry;
                  (* need to update the type *)
                  pd) 
                (concat_ok pdeclsrlist) in
            (* Check procedure bodies *)
            let procsrlist = List.map2 (check_proc tenv) newpdecls dmod.procs in
            if List.exists Result.is_error procsrlist then
              Error (concat_errors procsrlist)
            else
              let newprocs = concat_ok procsrlist in
              (* Made it this far, assemble the newly-decorated module. *)
              debug_print "procedure bodies checked";
              Ok ({name=dmod.name; imports=dmod.imports;
                   typedefs=newtypedefs;
                   globals=newglobals; procs=newprocs
                  },
                  tenv)
    )

(** Generate the interface object for a checked module, to be serialized. *)
let create_module_spec (the_mod: (typetag, 'a st_node, locinfo) dillmodule)
  : (typetag, 'a st_node, locinfo) module_spec =
  (* "unparser" to reconstruct syntactic type expressions *)
  let rec texpr_of_ttag ty =
    match ty with
    | Typevar tv -> {
        texpkind = Generic tv;
        nullable = false;
        array = false;
        loc = (Lexing.dummy_pos, Lexing.dummy_pos)
      }
    | Namedtype tinfo -> {
        texpkind = Concrete {
            modname = tinfo.modulename;
            classname = tinfo.tclass.classname;
            typeargs = List.map (fun ta -> texpr_of_ttag ta) tinfo.typeargs
          };
        nullable = is_option_type ty;
        array = is_array_type ty;
        loc = (Lexing.dummy_pos, Lexing.dummy_pos) }
  in
  {
    name = the_mod.name;
    imports = 
      List.map (fun (istmt: importStmt located) -> {
            value = (match istmt.value with
                | Import (mn, alias) -> Import (mn, alias)
                | Open mn -> Import (mn, None)); (* wait, why not Open? *)
            loc=istmt.loc
          }) the_mod.imports;
    (* TODO: Make sure all names fully qualified in the spec file.
       (Hopefully it will just work since modname is in the classTypeExpr) *)
    (* change opaque to hidden typedefs. *)
    typedefs =
       List.map (fun tdef ->
           if tdef.opaque then
             { tdef with kindinfo = Hidden }
           else tdef
         ) the_mod.typedefs;
    globals =
      List.map (fun gdecl ->
          { decor = gdecl.decor;
            varname = gdecl.varname;
            typeexp = 
              (* The original global initializer statement may not have had a
                 typeExpr, so we reconstruct one from the symbol table. *)
              let vtype = 
                (fst (Symtable.findvar gdecl.varname gdecl.decor)).symtype in
              texpr_of_ttag vtype
          }
        ) the_mod.globals;
    procdecls = List.map (fun proc -> proc.decl) the_mod.procs
}
