(** Abstract syntax tree structure *)

(* open Types *) (* shouldn't need this *)
open Common

type consttype =
  | FloatVal of float
  | IntVal of Int64.t
  | ByteVal of char
  | BoolVal of bool
  | StringVal of string
  | NullVal

type unary_op =
  | OpNeg
  | OpBitNot
  | OpNot

type binary_op =
  | OpTimes
  | OpDiv
  | OpMod  (* Want to make it the "proper" mod *)
  | OpPlus
  | OpMinus
  | OpBitAnd
  | OpBitOr
  | OpBitXor
  | OpEq
  | OpNe
  | OpLt
  | OpGt
  | OpLe
  | OpGe
  | OpAnd
  | OpOr

type 'l classTypeExpr = {
  modname: string;
  classname: string;
  typeargs: 'l typeExpr list
}

and 'l texpKind =
  | Generic of string  (* type variable *)
  | Concrete of 'l classTypeExpr

(** Syntactic type expression. Decorated with location for error
    checking, and then removed from AST afterwards. *)
and 'l typeExpr = {
  texpkind: 'l texpKind;
  (* semantically, option and array get folded into the type as classes. *)
  nullable: bool;
  array: bool;
  loc: 'l
}

let get_texp_classname te = match te.texpkind with
  | Generic _ -> failwith "Error: get_texp_classname called on generic type"
  | Concrete cte -> cte.classname


type 'ed raw_expr = (* should really probably change to inline records *)
  | ExpConst of consttype
  | ExpVal of 'ed expr (* builtin val(v) to match non-null nullable *)
  | ExpVar of 'ed var_expr
  | ExpRecord of (string * 'ed expr) list (* assignment to each field *)
  | ExpSeq of 'ed expr list
  (* module name, (no more) type name, variant name, initializer *)
  | ExpVariant of string * string * 'ed expr option
  | ExpBinop of 'ed expr * binary_op * 'ed expr
  | ExpUnop of unary_op * 'ed expr
  | ExpCall of string * (bool * 'ed expr) list (* proc name, mut * value list *)
  (* the bool is true if declaring a new var *)
  (* the typeExpr here was a smell, that should only be for a decl. *)
  (* Declaring variables in a null assignment may not be worth it, unless
     I find somewhere else to put the construct. *)
  | ExpNullAssn of bool * 'ed var_expr (* * 'l typeExpr option *) * 'ed expr

(** Type for an lvalue. Module name is currently concatted on
    (I guess because local symtables store them that way).  *)
(* The first element is special because it's the symbol table lookup. *)
(* The optional expression is indexing [] *)
and 'ed var_expr = (string * 'ed expr option) * (string * 'ed expr option) list

(** Decorated expression type *)
and 'ed expr = { e: 'ed raw_expr; decor: 'ed }

let get_varexpr_var (ve: 'ed var_expr) = fst (fst ve)

type ('ed, 'sd, 'l) raw_stmt = 
  | StmtDecl of string * 'l typeExpr option * 'ed expr option
  | StmtAssign of 'ed var_expr * 'ed expr
  | StmtNop
  | StmtReturn of 'ed expr option
  (* Hmm, may want to make this a record, it's a little unwieldy. *)
  | StmtIf of 'ed expr (* cond *)
              * ('ed,'sd,'l) stmt list (* then block *)
              * ('ed expr * ('ed,'sd,'l) stmt list) list (* elsif blocks *)
              * ('ed,'sd,'l) stmt list option (* else block *)
  | StmtWhile of 'ed expr (* cond *)
                 * ('ed,'sd,'l) stmt list (* body *)
  | StmtCase of 'ed expr (* object to match *)
                * ('ed expr * ('ed,'sd,'l) stmt list) list (* case blocks *)
                * ('ed,'sd,'l) stmt list option (* else block *)
  | StmtCall of 'ed expr  (* call used as statement, must return void *)
(*  | StmtBlock of ('ed,'sd,'l) stmt list *)

(** Decorated statement type *)
and ('ed, 'sd, 'l) stmt = { st: ('ed,'sd,'l) raw_stmt; decor: 'sd }


(** Global variable declaration without initializer; only used in
    modspecs. *)
type ('sd, 'l) globaldecl = {
    varname: string;
    (* in_module: string; *)
    typeexp: 'l typeExpr;
    decor: 'sd
  }

(** Global variable declaration with required initializer. *)
type ('ed, 'sd, 'l) globalstmt = {
    varname: string;
    typeexp: 'l typeExpr option;
    init: 'ed expr option; (* required by semantics, check in analyzer *)
    decor: 'sd
  }

(* I thought about removing the symtable decoration from the decl, but
   it can stand on its own in an interface file, so I guess it needs
   it. *)
type ('sd, 'l) procdecl = {
  name: string;
  typeparams: typevar list; (* need to change? *)
  (* One could imagine removing the typeExprs after analysis. *)
  (* The bool is the mutable indicator *)
  params: (bool * string * 'l typeExpr) list; 
  (* TODO: Also need "private" signifier. *)
  export: bool;
  rettype: 'l typeExpr;  (* make optional to get rid of void? *) 
  decor: 'sd
}

(** AST procedure record. *)
type ('ed,'sd,'l) proc = {
    decl: ('sd, 'l) procdecl;
    body: ('ed,'sd,'l) stmt list;
    decor: 'sd
  }

(* Type definition syntax begins here *)

(** Single field declaration of a struct type. *)
type 'l fieldDecl = {
    fieldname: string;
    priv: bool;
    mut: bool;
    (* Create 'typevar' field matching the struct later *)
    fieldtype: 'l typeExpr;
    decor: 'l 
  }

(** A single named option for a variant type. *)
type 'l variantDecl = {
    variantName: string;
    variantType: 'l typeExpr option; (* may be a constant symbol *)
    decor: 'l
  }

(** Type decl info that's different for structs/unions/enums. *)
type 'l kindInfo =
  | Fields of 'l fieldDecl list
  | Variants of 'l variantDecl list
  | Newtype of 'l typeExpr
  | Hidden (* for externally-defined opaque types *)

(** struct for definition of any type. *)
type ('sd, 'l) typedef = {
  (* module name is stored in the tenv. *)
  typename: string;
  rectype: bool;
  typeparams: string list;
  kindinfo: 'l kindInfo;
  opaque: bool;
  decor: 'sd
}


(* import and full module syntax begins here *)

(** Import statements occur separately, so no need to include in 
 * the stmt type. Only decoration is location, so just do it directly *)
type importStmt =
  | Import of string * string option
  | Open of string

type ('ed, 'sd, 'l) dillmodule = {
    name: string;
    imports: (importStmt located) list;
    typedefs: ('sd, 'l) typedef list;
    globals: ('ed, 'sd, 'l) globalstmt list;
    procs: ('ed, 'sd, 'l) proc list;
    (* initblock: ('ed,'sd) stmt list *)
  }

type ('ed, 'sd, 'l) module_spec = {
    name: string;
    imports: (importStmt located) list;
    typedefs: ('sd, 'l) typedef list;
    globals: ('sd, 'l) globaldecl list;
    procdecls: ('sd, 'l) procdecl list
  }


(* printing functions start here *)


let rec typeExpr_to_string te =
  (match te.texpkind with
   | Generic tv -> tv
   | Concrete cte ->
     (if cte.modname <> "" then cte.modname ^ "::" else "")
     ^ (if cte.typeargs = [] then ""
        else "(" ^
             String.concat ", " (List.map typeExpr_to_string cte.typeargs)
             ^ ")")
     ^ cte.classname)
  ^ (if te.nullable then "?" else "")
  ^ (if te.array then "[]" else "") 

and fieldDecl_to_string fd =
  (if fd.priv then "private " else "")
  ^ (if fd.mut then "mut " else "")
  ^ fd.fieldname ^ ": "
  ^ typeExpr_to_string fd.fieldtype

and typedef_to_string tdef = 
  "type " ^ tdef.typename
  ^ if List.length tdef.typeparams > 0 then
      "(" ^ String.concat "," tdef.typeparams ^ ")" else ""
  ^ (match tdef.kindinfo with
      | Fields fields ->
        " is" ^ (if tdef.rectype then " rec" else "") ^ " record\n   "
        ^ String.concat ",\n   " (List.map fieldDecl_to_string fields)
      | Variants variants ->
        " is" ^ (if tdef.rectype then " rec" else "") ^ " variant\n   "
        ^ String.concat ",\n   "
            (List.map (fun vdec ->
                 vdec.variantName
                 ^ (match vdec.variantType with 
                    | Some vt -> ": " ^ typeExpr_to_string vt
                    | None -> "")                          
               )         
                 variants)
     | Newtype tyex -> " is " ^ typeExpr_to_string tyex
     | Hidden -> ""
    )
  ^ ";\n"




(** Doesn't print out the full source yet. Not used in modspecs? *)
let rec exp_to_string (e: 'a expr) =
  match e.e with
  | ExpConst (FloatVal f) -> Float.to_string f
  | ExpConst (IntVal i) -> Int64.to_string i
  | ExpConst (ByteVal c) -> String.make 1 c
  | ExpConst (BoolVal b) -> if b then "true" else "false"
  | ExpConst (StringVal s) -> "\"" ^ String.escaped s ^ "\""
  | ExpConst NullVal -> "null"
  | ExpVal (e) -> "val(" ^ exp_to_string e ^ ")"
  | ExpVar vexpr -> varExpr_to_string vexpr
  | ExpRecord fl ->
      "{" ^ String.concat ", "
              (List.map (fun (fname, ex) ->
                   fname ^ "=" ^ exp_to_string ex) fl)
      ^ "}"
  | ExpSeq vl ->
     "{" ^ String.concat ", " (List.map exp_to_string vl) ^ "}"
  | ExpVariant (mn, vn, eopt) ->
     (if mn <> "" then mn ^ "::" else "")
     ^ (*tn ^ "|" ^*) vn
     ^ (match eopt with
        | Some e -> "(" ^ exp_to_string e ^ ")"
        | None -> "")
  | ExpBinop (e1, _, e2) -> exp_to_string e1 ^ " BINOP " ^ exp_to_string e2
  | ExpUnop (_, e) -> "UNOP " ^ exp_to_string e
  | ExpCall (procname, args) ->
     procname ^ "("
     ^ String.concat ", "
         (List.map (fun (mut, ex) ->
              (if mut then "#" else "") ^ exp_to_string ex) args)
     ^ ")"
  | ExpNullAssn (decl, vexp, (* tyopt, *) e) ->
     (if decl then "var " else "")
     ^ varExpr_to_string vexp
     (* ^ Option.fold ~none:""
         ~some:(fun ty -> ": " ^ typeExpr_to_string ty) tyopt *)
     ^ " ?= " ^ exp_to_string e

and varExpr_to_string (vi, fl) = 
  let indexed_to_string (vn, eopt) =
    vn ^ (match eopt with
          | Some e -> "[" ^ exp_to_string e ^ "]"
          | None -> "")
  in
  String.concat "." (List.map indexed_to_string (vi::fl))


let rec stmt_to_string st = 
      match st.st with
      | StmtDecl (v, t, eopt) ->
         "var " ^ v 
         ^ (match t with
            | Some te -> ": " ^ typeExpr_to_string te 
            | None -> "" )
         ^ (match eopt with
            | Some e -> " = " ^ exp_to_string e
            | None -> "")
         ^ ";\n"
      | StmtAssign (vexpr, e) ->
         varExpr_to_string vexpr ^ " = "
         ^ exp_to_string e ^ ";\n"
      | StmtNop -> "nop;\n"
      | StmtReturn (Some e) -> "return " ^ exp_to_string e ^ ";\n"
      | StmtReturn None -> "return;\n"
      | StmtCall e -> exp_to_string e ^ ";\n"
      | StmtIf (e, tb, eifs, eb) -> if_to_string (e, tb, eifs, eb)
      | StmtCase (e, blks, elseopt) -> case_to_string (e, blks, elseopt)
      | StmtWhile (cond, body) ->
         "while (" ^ exp_to_string cond ^ ") loop\n"
         ^ block_to_string body
         ^ "/while\n"
(*| StmtBlock sl -> "begin\n" ^ block_to_string sl ^ "end\n" *)

and block_to_string sl = 
  List.fold_left (fun prev st -> prev ^ stmt_to_string st) "" sl

and elsif_to_string (e, sl) =
  "elsif (" ^ exp_to_string e ^ ") then\n"
  ^ block_to_string sl

(* maybe interpret sub-functions will return a label *)
and if_to_string (e, tb, eifs, els) =
  "if " ^ exp_to_string e ^ " then \n"
  ^ block_to_string tb
  ^ List.fold_left (fun s eif -> s ^ elsif_to_string eif) "" eifs
  ^ (match els with
     | Some sb -> "else \n" ^ block_to_string sb
     | None -> "")
  ^ "/if\n"

and case_to_string (matchexp, caseblocks, elseopt) =
  "case " ^ exp_to_string matchexp ^ "\n"
  ^ String.concat "\n"
      (List.map (fun (caseexp, block) ->
           "  of " ^ exp_to_string caseexp ^ " then \n"
           ^ block_to_string block) caseblocks)
  ^ (match elseopt with
     | Some eblock -> "  else \n" ^ block_to_string eblock
     | None -> "")
  ^ "\n /case\n"

(* let interpret_params plist =  *)

let procdecl_to_string (pdecl: ('sd, 'tt) procdecl) =
  (if pdecl.export then "export " else "") ^ "proc "
  ^ (if (List.length pdecl.typeparams) > 0
     then "(" ^ String.concat "," pdecl.typeparams ^ ") " else "")
  ^ pdecl.name ^ "("
  ^ String.concat "," (
        List.map (fun (mut, varname, vartype) ->
            (if mut then "#" else "")
            ^ varname ^ ": " ^ typeExpr_to_string vartype) pdecl.params)
  ^ ") => " ^ typeExpr_to_string pdecl.rettype

let proc_to_string (proc: ('ed, 'sd, 'tt) proc) =
  (* a little ugly, but maybe I will use the pdecl later. *)
  procdecl_to_string proc.decl ^ " is \n"
  ^ block_to_string proc.body
  ^ "/proc\n" (* "\nend " ^ proc.decl.name ^ "\n" *)

let import_to_string istmt =
  match istmt.value with
  | Import (mname, Some alias) ->
    "import " ^ mname ^ " as " ^ alias ^ ";\n"
  | Import (mname, None) ->
    "import " ^ mname ^ ";\n"
  | Open mname ->
    "open " ^ mname ^ ";\n"
          
let module_to_string (dmod: ('ed, 'sd, 'tt) dillmodule) =
  "module " ^ dmod.name ^ " is \n"
  ^ String.concat "" (List.map import_to_string dmod.imports)
  ^ String.concat "\n" (List.map typedef_to_string dmod.typedefs)
  ^ List.fold_left (
        fun s gstmt ->
        s ^ "var " ^ gstmt.varname
        ^ Option.fold ~none:"" ~some:(fun te -> ": " ^ typeExpr_to_string te)
            gstmt.typeexp
        ^ Option.fold ~none:"" ~some:(fun e -> " = " ^ exp_to_string e)
            gstmt.init
        ^ "\n"
      ) "" dmod.globals
  ^ List.fold_left (fun s p -> s ^ proc_to_string p) "" dmod.procs
  (* ^ block_to_string dmod.initblock *)
  ^ "/module\n" (* "end " ^ dmod.name ^ "\n" *)

(** This is creating the actual interfaces...so it's important! *)
let modspec_to_string (mspec: ('ed, 'sd, 'l) module_spec) =
  "modspec " ^ mspec.name ^ " is \n"
  ^ String.concat "\n\n" (List.map typedef_to_string mspec.typedefs)
  ^ List.fold_left (
        fun s (gdecl: ('sd, 'l) globaldecl) ->
        s ^ "var " ^ gdecl.varname ^ ": "
        ^ typeExpr_to_string gdecl.typeexp ^ ";\n")
      "" mspec.globals
  ^ List.fold_left
      (fun s pd -> s ^ procdecl_to_string pd ^ ";\n") "" mspec.procdecls
  ^ "/modspec\n" (*"end " ^ mspec.name ^ "\n"*) 
  
