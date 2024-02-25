(** sedlex lexer for dill *)

open Sedlexing  (* new_line, loc stuff that parser will use *)
exception Error of string (* TODO: look for error type in Sedlexing *)

(* Regular expressions *)
let newline = [%sedlex.regexp? Opt '\r', '\n']
let whitespace = [%sedlex.regexp? (' ' | '\t')]
let digit = [%sedlex.regexp? '0'..'9']
let iconst = [%sedlex.regexp? Plus digit] 
let expon = [%sedlex.regexp? Opt ('e' | 'E'), Opt ('-' | '+'), Plus digit] 
let fconst = [%sedlex.regexp? Plus digit, '.', Star digit, Opt expon]
let ident_lc =
  [%sedlex.regexp? ('a'..'z' | '_'), Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]
let ident_uc =
  [%sedlex.regexp? ('A'..'Z'), Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]

let symbol = [%sedlex.regexp? '#', ident_lc]
(* TODO: hex constants *)

let rec token buf =
  match%sedlex buf with
  | whitespace ->
    token buf
  | newline ->
    new_line buf; token buf
  | _ (* as c *) ->   (* sedlex doesn't know this syntax, boo *)
    raise (Error (Printf.sprintf "Unexpected character %c"
                    buf.buf.[lexeme_start buf]))
