
(* "Lexing" is the runtime for ocamllex-generated lexers. *)
open Ast

let rec exp_to_string (e: 'a expr) =
  match e.e with
  | ExpConst _ -> "CONSTEXP "
  | ExpVar v -> "(VAREXP " ^ v ^ ") "
  | ExpBinop (e1, _, e2) -> exp_to_string e1 ^ "BINOP " ^ exp_to_string e2
  | ExpUnop (_, e) -> "UNOP " ^ exp_to_string e
  | ExpCall (pn, _) -> pn ^ "(yadda, yadda)"
  | ExpNullAssn (decl, v, e) ->
     (if decl then "var " else "")
     ^ v ^ " ?= " ^ exp_to_string e

let rec block_to_string sl = 
  List.fold_left (fun prev st -> prev ^ 
      match st.st with
      | StmtDecl (v, t, e) ->
         "VAR " ^ v 
         ^ (match t with
            | Some (TypeName tn) -> " : " ^ tn
            | None -> "" )
         ^ " = " ^ exp_to_string e ^ ";\n"
      | StmtAssign (v, e) -> v ^ " = " ^ exp_to_string e ^ ";\n"
      | StmtReturn (Some e) -> "return " ^ exp_to_string e ^ ";\n"
      | StmtReturn None -> "return;\n"
      | StmtCall e -> exp_to_string e ^ ";\n"
      | StmtIf (e, tb, eifs, eb) -> if_to_string (e, tb, eifs, eb)
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

(* let process (line : string) =
  let linebuf = Lexing.from_string line in
  try
    (* Run the parser on this line of input. *)
    Printf.printf "%s\n%!" (interpret_block (Parser.main Lexer.token linebuf))
  with
  | Lexer.Error msg ->
      Printf.fprintf stderr "%s%!" msg
  | Parser.Error ->
      Printf.fprintf stderr "At offset %d: syntax error.\n%!" (Lexing.lexeme_start linebuf) 

let process (optional_line : string option) =
  match optional_line with
  | None ->
      ()
  | Some line ->
      process line

let rec repeat buf =
  (* Attempt to read one line. *)
  let optional_line, continue = Lexer.line buf in
  process optional_line;
  if continue then
    repeat buf
 *)

(* take the whole buffer, letting newlines be treated as whitespace. *)
let process_whole channel =
  let buf = Lexing.from_channel channel in
  try
    (* Run the parser on this line of input. *)
    Printf.printf "%s\n%!" (program_to_string (Parser.main Lexer.token buf))
  with
  | Lexer.Error msg ->
      Printf.fprintf stderr "%s%!" msg
  | Parser.Error ->
     let spos, epos = (Lexing.lexeme_start_p buf, Lexing.lexeme_end_p buf) in
     Printf.fprintf stderr
       "At line %d:%d-%d: syntax error.\n%!"
       spos.pos_lnum
       (spos.pos_cnum - spos.pos_bol)
       (epos.pos_cnum - epos.pos_bol)

(* let () =
  repeat (Lexing.from_channel stdin) *)

let () =
  let infile =
    if Array.length Sys.argv > 1 then
      open_in Sys.argv.(1)
    else stdin
  in
  process_whole infile
  
