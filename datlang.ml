
(* "Lexing" is the runtime for ocamllex-generated lexers. *)
open Ast

let rec interpret_exp (e: expr) =
  match e with
  | ExpConst _ -> "CONSTEXP "
  | ExpVar v -> "(VAREXP " ^ v ^ ") "
  | ExpBinop (e1, _, e2) -> interpret_exp e1 ^ "BINOP " ^ interpret_exp e2
  | ExpUnop (_, e) -> "UNOP " ^ interpret_exp e

let rec interpret_block sl = 
  List.fold_left (fun prev st -> prev ^ 
      match st with
      | StmtDecl (v, t, e) ->
         "VAR " ^ v 
         ^ (match t with
            | Some (TypeName tn) -> " : " ^ tn
            | None -> "" )
         ^ " = " ^ interpret_exp e ^ ";\n"
      | StmtAssign (v, e) -> v ^ " = " ^ interpret_exp e ^ ";\n"
      | StmtIf (e, tb, eifs, eb) -> interpret_if (e, tb, eifs, eb)
    ) "" sl

and interpret_elsif (e, sl) =
  "elsif (" ^ interpret_exp e ^ ") then\n"
  ^ interpret_block sl

(* maybe interpret sub-functions will return a label *)
and interpret_if (e, tb, eifs, els) =
  "if (" ^ interpret_exp e ^ ") then\n"
  ^ interpret_block tb
  ^ List.fold_left (fun s eif -> s ^ interpret_elsif eif) "" eifs
  ^ (match els with
     | Some sb -> "else " ^ interpret_block sb
     | None -> "")
  ^ "end\n"

let process (line : string) =
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

(* take the whole buffer, letting newlines be treated as whitespace. *)
let process_whole channel =
  let buf = Lexing.from_channel channel in
  try
    (* Run the parser on this line of input. *)
    Printf.printf "%s\n%!" (interpret_block (Parser.main Lexer.token buf))
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

let () = process_whole stdin
