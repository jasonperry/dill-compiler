(** Recursive descent parser for dill *)

open Common
open Slexer

(** Type for simple token buffering/lookahead implementation. *)
type tbuf = {
  lbuf: token array;
  lexbuf: Sedlexing.lexbuf;
  lpos: int ref;
  lookahead: int
}

(** Refill token buffer's lookahead in-place from lexer. *)
let _refill_tbuf tbuf =
  let rec tloop i =
    if i == tbuf.lookahead then ()
    else
      let nexttok = Slexer.token tbuf.lexbuf in
      Array.set tbuf.lbuf i nexttok;
      if nexttok.ttype = EOF then () (* leave old tokens *)
      else tloop (i+1)
  in 
  if !(tbuf.lpos) < tbuf.lookahead
  then failwith "All tokens must be consumed to call _refill_buf "
  else
    tloop 0; tbuf.lpos := 0

(** Initialize token buffer with specified lookahead size. *)
let init_tbuf lexbuf lookahead =
  let tbuf = {
    lbuf = Array.init lookahead (fun _ ->
        {ttype = EOF; loc=Sedlexing.lexing_positions lexbuf});
    lexbuf = lexbuf;
    lpos = ref lookahead; (* marks as empty so it can refill *)
    lookahead = lookahead
  } in
  _refill_tbuf tbuf;
  tbuf

(** Attempt to eat one token of given type from token buffer. *)
let consume tbuf ttype =
  if !(tbuf.lpos) = tbuf.lookahead then _refill_tbuf tbuf;
  let i = !(tbuf.lpos) in
  if tbuf.lbuf.(i).ttype = ttype then (
    tbuf.lpos := i+1;
    Some (tbuf.lbuf.(i)))
  else
    None

(** Return current token in buffer without moving the pointer. *)
let peek tbuf =
  (* Note that this can only do a single lookahead, regardless
     of buffer size, unless it "stretches" the buffer. *)
  if !(tbuf.lpos) = tbuf.lookahead then _refill_tbuf tbuf;
  tbuf.lbuf.(!(tbuf.lpos))


(** Consume the next token of any type. Should be only for testing? *)
let consume_any tbuf =
  let tok = peek tbuf in
  tbuf.lpos := !(tbuf.lpos) + 1;
  tok

(* -------------------- Parser Proper ------------------ *)

let modsource buf =
  match (token buf).ttype with
  | ICONST i -> print_string ("ICONST " ^ Int64.to_string i ^ "\n")
  | _ -> print_string "something else"

(* for testing the lexer. Any sequence of valid tokens. *)
let rec any_tokens buf =
  match (consume_any buf).ttype with 
  | ICONST i -> print_string ("(ICONST " ^ Int64.to_string i ^ ") ");
    any_tokens buf
  | FCONST x -> print_string ("(FCONST " ^ string_of_float x ^ ") ");
    any_tokens buf
  | BYTECONST c -> print_string ("(BYTECONST '" ^ Char.escaped c ^ "') ");
    any_tokens buf
  | STRCONST s -> print_string ("(STRCONST \"" ^ String.escaped s ^ "\") ");
    any_tokens buf
  | IDENT_LC s -> print_string ("(IDENT_LC " ^ s ^ ") "); any_tokens buf
  | IDENT_UC s -> print_string ("(IDENT_UC " ^ s ^ ") "); any_tokens buf
  | EOF -> print_string "EOF\n "; (* don't recurse *)
  | _ -> print_string "token "; any_tokens buf

(* temporary top-level code *)
let _ =
  (* Could go in dillc.ml *)
  Printexc.register_printer (
    function 
    | SyntaxError e -> Some ("Syntax Error: " ^
        (fst e.loc).pos_fname ^ ":" ^ format_loc (fst e.loc) (snd e.loc)
        ^ ":" ^ e.msg
      )
    | _ -> None);
  (* to figure out: why no double-backslash on the \x *)
  let lexbuf = Sedlexing.Utf8.from_channel stdin in
  (* from_string "42 '\\n' 'w' 'เ' (* เมืองจึงวิปริตเป็นนัก *) '\x41' 44 f" in *)
  let tbuf = init_tbuf lexbuf 20 in
  any_tokens tbuf
