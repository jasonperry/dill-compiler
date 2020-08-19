
(* "Lexing" is the runtime for ocamllex-generated lexers. *)
open Ast

(* eventually move these printing functions elsewhere. *)

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

let rec block_to_string sl = 
  List.fold_left (fun prev st -> prev ^ 
      match st.st with
      | StmtDecl (v, t, eopt) ->
         "VAR " ^ v 
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
    ) "" sl

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

(** Format two Lexing.location objects as a string showing the range. *)
let format_loc (spos: Lexing.position) (epos: Lexing.position) =
  if spos.pos_lnum = epos.pos_lnum then
    Format.sprintf "%d:%d-%d"
      spos.pos_lnum
      (spos.pos_cnum - spos.pos_bol)
      (epos.pos_cnum - epos.pos_bol)
  else 
    Format.sprintf "%d:%d-%d:%d"
      spos.pos_lnum
      (spos.pos_cnum - spos.pos_bol)
      epos.pos_lnum
      (epos.pos_cnum - epos.pos_bol)

(** Generate string buffer showing a sequence of errors. *)
let format_errors elist =
  let format1 {loc; value} =
    (* TODO: distinguish between error and warning. *)
    "Error: " ^ format_loc (fst loc) (snd loc) ^ ":\n    " ^ value
  in
  (* errors append at beginning, so need to reverse the list. *)
  let errstrs = List.rev_map format1 elist in
  String.concat "\n" errstrs ^ "\n"

(** Run as many phases as we have on one module. *)
let process_module channel =
  let buf = Lexing.from_channel channel in
  let modtree = try
      Parser.main Lexer.token buf
    with
    | Lexer.Error msg ->
       let spos, epos = (Lexing.lexeme_start_p buf, Lexing.lexeme_end_p buf) in
       print_string
         ("At line " ^ format_loc spos epos ^ ": lexical error:\n    "
          ^ msg ^ "\n");
       failwith "Compilation terminated at lexing."
    | Parser.Error ->
       let spos, epos = (Lexing.lexeme_start_p buf, Lexing.lexeme_end_p buf) in
       print_string
         ("At line " ^ format_loc spos epos ^ ": syntax error.\n");
       failwith "Compilation terminated at parsing." 
  in
  let open Symtable1 in 
  let analyzedmod = Analyzer.check_module Symtable.empty base_tenv
                      modtree in
  match analyzedmod with
  | Ok _ -> print_string "Success!\n"
  | Error errs -> print_string (format_errors errs)

(* let () =
  repeat (Lexing.from_channel stdin) *)

let () =
  let infile =
    if Array.length Sys.argv > 1 then
      open_in Sys.argv.(1)
    else stdin
  in
  process_module infile
  
