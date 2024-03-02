(** sedlex lexer for dill *)

open Sedlexing  (* new_line, loc stuff that parser will use *)
exception Error of string (* TODO: unified lex/parse SyntaxError type *)
(* Lexing.position has the filename too *)
(* Not in common.ml for now, Other modules might have different error
   types. Or, should I make a unified error type? *)
exception SyntaxError of {
    msg: string;
    loc: Lexing.position * Lexing.position
  }
(* Idea: parameterize the module by encoding *)
module Enc = Sedlexing.Utf8

(* Regular expressions *)
let newline = [%sedlex.regexp? Opt '\r', '\n']
let whitespace = [%sedlex.regexp? (' ' | '\t')]
let digit = [%sedlex.regexp? '0'..'9']
let iconst = [%sedlex.regexp? Plus digit] 
let expon = [%sedlex.regexp? Opt ('e' | 'E'), Opt ('-' | '+'), Plus digit] 
let fconst = [%sedlex.regexp? Plus digit, '.', Star digit, Opt expon]
let ident_lc =
  [%sedlex.regexp? ('a'..'z' | '_'),
                 Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]
let ident_uc =
  [%sedlex.regexp? ('A'..'Z'), Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]
let symbol = [%sedlex.regexp? '#', ident_lc]
(* TODO: hex constants *)

(* final type should have loc in it. *)
type ttype =
  | ICONST of Int64.t
  | FCONST of float
  | STRCONST of string
  | BYTECONST of char
  | IDENT_LC of string
  | IDENT_UC of string
  | LPAREN | RPAREN | LBRACE | RBRACE | LSQRB | RSQRB
  | PLUS | MINUS | TIMES | DIV | MOD
  | UMINUS (* not lexed *)
  | AMP | PIPE | CARAT | TILDE (* bitwise operators *)
  | EQ | NE | LT | GT | LE | GE
  | AND | OR | BANG
  | TRUE | FALSE | NULL (* | VAL *)
  | COLON | DCOLON | SEMI | DOT | COMMA | HASH | QMARK | ARROW | DARROW
  | ASSIGN | NULLASSIGN
  | VAR | REF (* | LET ? *)
  | IS
  | IF | THEN | ELSIF | ELSE | ENDIF
  | WHILE | LOOP | ENDWHILE
  | CASE | OF | ENDCASE
  | PROC | ENDPROC | RETURN | NOP
  | MODULE | ENDMODULE | MODSPEC | ENDMODSPEC
  | IMPORT | AS | OPEN
  | TYPE | OPAQUE | REC | STRUCT | VARIANT | MUT (* | ENUM *)
  | EOF
  
type token = {
  ttype: ttype;
  loc: Lexing.position * Lexing.position
}

(* do I have to write my own to_string for the buf? *)
let string_of_ucarray arr =
  String.of_seq (Array.to_seq (Array.map Uchar.to_char arr))

let string_of_lexeme buf =
  string_of_ucarray (lexeme buf)

let rec tparse (buf: Sedlexing.lexbuf) =
  match%sedlex buf with
    | whitespace ->
      tparse buf
    | newline ->
      new_line buf; tparse buf
    | "(*" ->
      comment 0 buf
    | iconst -> ICONST (Int64.of_string (string_of_ucarray (lexeme buf)))
    (* | any (* as c *) ->  (* sedlex doesn't know this syntax, boo *) *)
    | _ -> raise (SyntaxError {
        msg=("Unexpected character: " ^ Enc.lexeme buf);
        loc=lexing_positions buf
      })
       (* (Printf.sprintf "Unexpected character: %c"
                           (Uchar.to_char (lexeme_char buf 0)))) *)

and comment depth buf =
  match%sedlex buf with
  | "(*" -> comment (depth+1) buf
  | "*)" ->
    if depth = 0 then tparse buf else comment (depth-1) buf
  | newline -> new_line buf; comment depth buf
  | eof -> raise (Error "Unterminated comment at EOF")
  | _ -> comment depth buf

(* Wait...will buf be different after? *)
let token buf = 
  { ttype=tparse buf; loc=lexing_positions buf }
