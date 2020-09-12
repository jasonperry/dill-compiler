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

(** position info to decorate the AST with *)
type locinfo = Lexing.position * Lexing.position

(** This is still used for error messages. *)
type 'a located =
  { loc: Lexing.position * Lexing.position; value: 'a }

(** Type info to decorate the second verion of the AST *)
(* type typeinfo = { ty: typetag } *) (* just use typetag directly. *)

(** Syntactic type expression. Needs to be expanded *)
type typeExpr =
  | TypeName of string  (* module, params, array, null *)

type 'ed raw_expr = (* should really probably change to inline records *)
  | ExpConst of consttype
  | ExpVar of string  (* later a type for pieces of an object expr *)
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

(* I thought about removing the decoration from the decl, but it can
 * stand on its own in an interface file, so I guess it needs it. *)
type 'sd procdecl = {
    name: string;
    (* One could imagine removing the typeExprs after analysis. *)
    params: (string * typeExpr) list;
    rettype: typeExpr;
    decor: 'sd;
  }

type ('ed,'sd) proc = {
    decl: 'sd procdecl;
    body: ('ed,'sd) stmt list;
    decor: 'sd
  }

type ('ed,'sd) dillmodule = {
    name: string;
    (* No, AST should not have a symbol table in it! 
     * I can keep the top level symbol table with the control function. *)
    globals: ('ed, 'sd) stmt list;
    procs: ('ed,'sd) proc list;
    initblock: ('ed,'sd) stmt list
  }

type ('ed, 'sd) module_interface = {
    name: string;
    globals: ('ed, 'sd) stmt list; (* but remove initializers *)
    procdecls: 'sd procdecl list
  }

(* printing functions start here *)

let typeExpr_to_string te =
  match te with
  | TypeName s -> s

let rec exp_to_string (e: 'a expr) =
  match e.e with
  | ExpConst _ -> "CONSTEXP "
  | ExpVar v -> "(VAREXP " ^ v ^ ") "
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
  "proc " ^ pdecl.name ^ "("
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
  ^ block_to_string dmod.globals
  ^ List.fold_left (fun s p -> s ^ proc_to_string p) "" dmod.procs
  ^ block_to_string dmod.initblock
  ^ "end " ^ dmod.name ^ "\n"

let interface_to_string (modi: ('ed, 'sd) module_interface) =
  "modspec " ^ modi.name ^ " = \n"
  ^ block_to_string modi.globals
  ^ List.fold_left
      (fun s pd -> s ^ procdecl_to_string pd ^ ";\n") "" modi.procdecls
  ^ "end " ^ modi.name ^ "\n"
  
