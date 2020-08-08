{
   open Parser (* for token defs *)
   open Lexing (* new_line *)
   exception Error of string (* should be LexError? *)
}

(* Regular expressions *)
let digit = ['0'-'9']
let iconst = digit+
let exp = ['e' 'E'] ['-' '+']? digit+
let fconst = digit+ '.' digit* exp?
let ident_lc = ['a'-'z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let ident_uc = ['A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

(* Temporary, because it's in the calc example.
 * Maybe turn it into "file"?  *)
rule line = parse
| ([^'\n']* '\n') as line
    (* Normal case: one line, no eof. *)
    { Some line, true }
| eof
    (* Normal case: no data, eof. *)
    { None, false }
| ([^'\n']+ as line) eof
    (* Special case: some data but missing '\n', then eof.
       Consider this as the last line, and add the missing '\n'. *)
    { Some (line ^ "\n"), false }

and token = parse  (* funny that it's called parse *)
  | [ ' ' '\t' ]
    { token lexbuf }
  | '\r'? '\n'
    { new_line lexbuf; token lexbuf }
  | fconst as f
    { FCONST (float_of_string f) }
  | iconst as i
    { ICONST (int_of_string i) }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '*'     { TIMES }
  | '/'     { DIV }
  | '('     { LPAREN }
  | ')'     { RPAREN }
  | '='	    { ASSIGN }
  | ','	    { COMMA }
  | ';'	    { SEMI }
  | ':'	    { COLON }
  | "?="    { NULLASSIGN }
  | "var"   { VAR }
  | "if"    { IF }
  | "then"  { THEN }
  | "elsif" { ELSIF }
  | "else"  { ELSE }
  | "endif" { ENDIF }
  | "begin" { BEGIN }
  | "end"   { END }
  | "proc"  { PROC }
  | "return" { RETURN }
  | ident_lc as v	{ IDENT_LC v }
  | ident_uc as v	{ IDENT_UC v }
  | eof     { EOF }
  | _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }

