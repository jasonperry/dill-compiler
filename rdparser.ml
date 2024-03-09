(** Recursive descent parser for dill *)

open Common
open Slexer

let modsource buf =
  match (token buf).ttype with
  | ICONST i -> print_string ("ICONST " ^ Int64.to_string i ^ "\n")
  | _ -> print_string "something else"

(* for testing the lexer. Any sequence of valid tokens. *)
let rec any_tokens buf =
  match (token buf).ttype with 
  | ICONST i -> print_string ("(ICONST " ^ Int64.to_string i ^ ") ");
    any_tokens buf
  | BYTECONST c -> print_string "'"; print_char c; print_string "' ";
    any_tokens buf
  | EOF -> print_string "EOF "
  | _ -> print_string "token ";
    any_tokens buf

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
  let lexbuf = Sedlexing.Utf8.from_string "42 '\\n' 'w' 'เ' (* เมืองจึงวิปริตเป็นนัก *) '\x41' 44 f" in
  any_tokens lexbuf
