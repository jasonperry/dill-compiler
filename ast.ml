(** Abstract syntax tree structure *)

(* open Types *) (* yay, now generic over what it's decorated with! *)

type consttype =
  | FloatVal of float
  | IntVal of int  (* TODO: make int32 to avoid OCaml 31-bit ints *)
  | BoolVal of bool

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

(** position info to decorate the AST with. TODO: don't put it here. *)
type locinfo = Lexing.position * Lexing.position

(** This is still used for error messages. *)
type 'a located =
  { loc: Lexing.position * Lexing.position; value: 'a }

(** Syntactic type expression. Needs to be expanded *)
type typeExpr =
  | TypeName of string  (* module, params, array, null *)

type 'ed raw_expr = (* should really probably change to inline records *)
  | ExpConst of consttype
  | ExpVar of string * string list (* field specifiers *)
  | ExpRecord of (string * 'ed expr) list
  | ExpBinop of 'ed expr * binary_op * 'ed expr
  | ExpUnop of unary_op * 'ed expr
  | ExpCall of string * 'ed expr list
  (* the bool is true if declaring a new var *)
  | ExpNullAssn of bool * string * typeExpr option * 'ed expr

(** Decorated expression type *)
and 'ed expr = { e: 'ed raw_expr; decor: 'ed }

type ('ed,'sd) raw_stmt = 
  | StmtDecl of string * typeExpr option * 'ed expr option
  | StmtAssign of string * 'ed expr  (* need to make var expr on left? *)
  | StmtNop
  | StmtReturn of 'ed expr option
  (* Hmm, may want to make this a record, it's a little unwieldy. *)
  | StmtIf of 'ed expr (* cond *)
              * ('ed,'sd) stmt list (* then block *)
              * ('ed expr * ('ed,'sd) stmt list) list (* elsif blocks *)
              * ('ed,'sd) stmt list option (* else block *)
  | StmtWhile of 'ed expr (* cond *)
                 * ('ed, 'sd) stmt list (* body *)
  | StmtCall of 'ed expr  (* have to check the function returns void *)
  | StmtBlock of ('ed,'sd) stmt list

(** Decorated statement type ('a is for the decor of embedded exprs) *)
and ('ed,'sd) stmt = { st: ('ed,'sd) raw_stmt; decor: 'sd }


(** Global variable declaration only; only used in modspecs. *)
type 'sd globaldecl = {
    varname: string;
    (* in_module: string; *)
    typeexp: typeExpr;
    decor: 'sd
  }

(** Global var declaration with required initializer. *)
type ('ed, 'sd) globalstmt = {
    varname: string;
    typeexp: typeExpr option;
    init: 'ed expr option; (* required by semantics, check in analyzer *)
    decor: 'sd
  }

(* I thought about removing the decoration from the decl, but it can
 * stand on its own in an interface file, so I guess it needs it. *)
type 'sd procdecl = {
    name: string;
    (* One could imagine removing the typeExprs after analysis. *)
    params: (string * typeExpr) list;
    (* Also need "private" signifier. *)
    export: bool;
    rettype: typeExpr;
    decor: 'sd
  }

(** AST procedure record. *)
type ('ed,'sd) proc = {
    decl: 'sd procdecl;
    body: ('ed,'sd) stmt list;
    decor: 'sd
  }

(** Single field declaration of a struct type. *)
type fieldDecl = {
    fieldname: string;
    priv: bool;
    mut: bool;
    (* Create 'typevar' field matching the struct later *)
    fieldtype: typeExpr;
  }

(** A struct type definition. *)
type structTypedef = {
    typename: string;
    (* actually need a fieldDecl for this *)
    fields: fieldDecl list (* should also be decorated with loc *)
  }

(* It needs the symbol table decoration for the methods, I think. *)
type typedef =
  | Struct of structTypedef


(** Import statements occur separately, so it seems no need to include in 
 * the stmt type. Also, no decoration needed?
 * Any possible errors are in the imported header itself, so it seems not. *)
type importStmt =
  | Using of string * string option
  | Open of string

type ('ed,'sd) dillmodule = {
    name: string;
    imports: importStmt list;
    typedefs: typedef list;
    globals: ('ed, 'sd) globalstmt list;
    procs: ('ed,'sd) proc list;
    (* initblock: ('ed,'sd) stmt list *)
  }

(* No expressions in a module spec. *)
type 'sd module_spec = {
    name: string;
    imports: importStmt list;
    typedefs: typedef list;
    globals: 'sd globaldecl list;
    procdecls: 'sd procdecl list
  }


(* printing functions start here *)


let typeExpr_to_string te =
  match te with
  | TypeName s -> s

(** Doesn't print out the full source yet. Not used in modspecs? *)
let rec exp_to_string (e: 'a expr) =
  match e.e with
  | ExpConst _ -> "CONSTEXP "
  | ExpVar (v, _) -> "(VAREXP " ^ v ^ "POSSIBLE DOT FIELDS) "
  | ExpRecord fl ->
      "{" ^ String.concat ", "
              (List.map (fun (fname, ex) ->
                   fname ^ "=" ^ exp_to_string ex) fl)
      ^ "}"
  | ExpBinop (e1, _, e2) -> exp_to_string e1 ^ "BINOP " ^ exp_to_string e2
  | ExpUnop (_, e) -> "UNOP " ^ exp_to_string e
  | ExpCall (pn, _) -> pn ^ "(yadda, yadda)"
  | ExpNullAssn (decl, v, tyopt, e) ->
     (if decl then "var " else "")
     ^ v ^ Option.fold ~none:"" ~some:typeExpr_to_string tyopt
     ^ " ?= " ^ exp_to_string e

let rec stmt_to_string st = 
      match st.st with
      | StmtDecl (v, t, eopt) ->
         "var " ^ v 
         ^ (match t with
            | Some (TypeName tn) -> " : " ^ tn
            | None -> "" )
         ^ (match eopt with
            | Some e -> " = " ^ exp_to_string e
            | None -> "")
         ^ ";\n"
      | StmtAssign (v, e) -> v ^ " = " ^ exp_to_string e ^ ";\n"
      | StmtNop -> "nop;\n"
      | StmtReturn (Some e) -> "return " ^ exp_to_string e ^ ";\n"
      | StmtReturn None -> "return;\n"
      | StmtCall e -> exp_to_string e ^ ";\n"
      | StmtIf (e, tb, eifs, eb) -> if_to_string (e, tb, eifs, eb)
      | StmtWhile (cond, body) ->
         "while (" ^ exp_to_string cond ^ ") loop\n"
         ^ block_to_string body
         ^ "endloop\n"
      | StmtBlock sl -> "begin\n" ^ block_to_string sl ^ "end\n"

and block_to_string sl = 
  List.fold_left (fun prev st -> prev ^ stmt_to_string st) "" sl

and elsif_to_string (e, sl) =
  "elsif (" ^ exp_to_string e ^ ") then\n"
  ^ block_to_string sl

(* maybe interpret sub-functions will return a label *)
and if_to_string (e, tb, eifs, els) =
  "if (" ^ exp_to_string e ^ ") then\n"
  ^ block_to_string tb
  ^ List.fold_left (fun s eif -> s ^ elsif_to_string eif) "" eifs
  ^ (match els with
     | Some sb -> "else " ^ block_to_string sb
     | None -> "")
  ^ "endif\n"

(* let interpret_params plist =  *)

let procdecl_to_string (pdecl: 'sd procdecl) =
  if pdecl.export then "export " else ""
  ^ "proc " ^ pdecl.name ^ "("
  ^ String.concat "," (
        List.map (fun (varname, vartype) ->
            varname ^ ": " ^ typeExpr_to_string vartype) pdecl.params)
  ^ ") : " ^ typeExpr_to_string pdecl.rettype

let proc_to_string (proc: ('ed, 'sd) proc) =
  (* a little ugly, but maybe I will use the pdecl later. *)
  procdecl_to_string proc.decl ^ "= \n"
  ^ block_to_string proc.body
  ^ "\nend " ^ proc.decl.name ^ "\n"

let module_to_string (dmod: ('ed, 'sd) dillmodule) =
  "module " ^ dmod.name ^ " = \n"
  ^ List.fold_left (
        fun s -> function
              | Struct tdef -> 
                 s ^ "type " ^ tdef.typename ^ " = struct\n"
                 ^ "(some fields)\n end " ^ tdef.typename ^ "\n"
      ) "" dmod.typedefs
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
  ^ "end " ^ dmod.name ^ "\n"

let modspec_to_string (mspec: 'sd module_spec) =
  "modspec " ^ mspec.name ^ " = \n"
  ^ List.fold_left (
        fun s (gdecl: 'sd globaldecl) ->
        s ^ "var " ^ gdecl.varname ^ ": "
        ^ typeExpr_to_string gdecl.typeexp ^ ";\n")
      "" mspec.globals
  ^ List.fold_left
      (fun s pd -> s ^ procdecl_to_string pd ^ ";\n") "" mspec.procdecls
  ^ "end " ^ mspec.name ^ "\n"
  
