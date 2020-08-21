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

type 'a raw_expr = (* should really probably change to inline records *)
  | ExpConst of consttype
  | ExpVar of string  (* later a type for pieces of an object expr *)
  | ExpBinop of 'a expr * binary_op * 'a expr
  | ExpUnop of unary_op * 'a expr
  | ExpCall of string * 'a expr list
  (* the bool is true if declaring a new var *)
  | ExpNullAssn of bool * string * typeExpr option * 'a expr

(** Decorated expression type *)
and 'a expr = { e: 'a raw_expr; decor: 'a }


type ('a,'b) raw_stmt = 
  | StmtDecl of string * typeExpr option * 'a expr option
  | StmtAssign of string * 'a expr  (* need to make var expr on left? *)
  | StmtReturn of 'a expr option
  (* Hmm, may want to make this a record, it's a little unwieldy. *)
  | StmtIf of 'a expr (* cond *)
              * ('a,'b) stmt list (* then block *)
              * ('a expr * ('a,'b) stmt list) list (* elsif blocks *)
              * ('a,'b) stmt list option (* else block *)
  | StmtWhile of 'a expr (* cond *) * ('a, 'b) stmt list (* body *)
  | StmtCall of 'a expr  (* have to check the function returns void *)
  | StmtBlock of ('a,'b) stmt list

(** Decorated statement type *)
and ('a,'b) stmt = { st: ('a,'b) raw_stmt; decor: 'b }

(* Note that this doesn't need a decoration type param, it's not recursive. *)
type raw_procdecl = {
    name: string;
    (* One could imagine removing the typeExprs after analysis. *)
    params: (string * typeExpr) list;
    rettype: typeExpr
  }
(* I thought about removing the decoration from the decl, but it can
 * stand on its own in an interface file, so I guess it needs it. *)
and 'a procdecl = { pdecl: raw_procdecl; decor: 'a;  }

type ('a,'b) raw_proc = {
    decl: 'b procdecl;
    body: ('a,'b) stmt list
  }

type ('a,'b) proc = { proc: ('a,'b) raw_proc; decor: 'b }



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
         ^ " = " ^ (match eopt with
                    | Some e -> exp_to_string e
                    | None -> "")
         ^ ";\n"
      | StmtAssign (v, e) -> v ^ " = " ^ exp_to_string e ^ ";\n"
      | StmtReturn (Some e) -> "return " ^ exp_to_string e ^ ";\n"
      | StmtReturn None -> "return;\n"
      | StmtCall e -> exp_to_string e ^ ";\n"
      | StmtIf (e, tb, eifs, eb) -> if_to_string (e, tb, eifs, eb)
      | StmtWhile (cond, body) ->
         "while (" ^ exp_to_string cond ^ ") loop\n"
         ^ block_to_string body
         ^ "endloop"
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
  ^ "end\n"

(* let interpret_params plist =  *)

let proc_to_string pr =
  (* a little ugly, but maybe I will use the pdecl later. *)
  let pdecl = pr.proc.decl.pdecl in
  "proc " ^ pdecl.name ^ "(" ^ "yadda, yadda" ^ ") : yadda = \n"
  ^ block_to_string pr.proc.body
  ^ "\nendproc\n"

let program_to_string (procs, block) =
  List.fold_left (fun s p -> s ^ proc_to_string p) "" procs
  ^ block_to_string block
