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

(* Unused, from the calc example *)
(* rule line = parse
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
 *)

rule token = parse  (* funny that it's called parse *)
  | [ ' ' '\t' ]
    { token lexbuf }
  | '\r'? '\n'
    { new_line lexbuf; token lexbuf }
  | "(*"
    { comment 0 lexbuf }
  | "\""
    { string (Buffer.create 80) lexbuf }  
  | iconst as i
    (* TODO: checking for 32-bit fit. Maybe bigints later! *)
    { ICONST (int_of_string i) }
  | fconst as f
    { FCONST (float_of_string f) }
  | '('     { LPAREN }
  | ')'     { RPAREN }
  | '{'     { LBRACE }
  | '}'     { RBRACE }
  | '*'     { TIMES }
  | '/'     { DIV }
  | '%'     { MOD }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '&'     { AMP }
  | '|'     { PIPE }
  | '^'     { CARAT }
  | '~'     { TILDE }
  (* | "++"   { CONCAT } *)
  | "=="    { EQ }
  | "!="    { NE }
  | "<"     { LT }
  | ">"     { GT }
  | "<="    { LE }
  | ">="    { GE }
  | "&&"    { AND }
  | "||"    { OR }
  | '!'     { NOT }
  | '#'     { HASH }
  | '?'     { QMARK }
  | '='	    { ASSIGN }
  | "?="    { NULLASSIGN }
  | "->"    { ARROW }
  | "=>"    { DARROW }
  | ','	    { COMMA }
  | ';'	    { SEMI }
  | "::"    { DCOLON }
  | ':'	    { COLON }
  | "var"   { VAR }
  | "if"    { IF }
  | "then"  { THEN }
  | "elsif" { ELSIF }
  | "else"  { ELSE }
  | "endif" { ENDIF }
  | "is"    { IS }
  | "begin" { BEGIN }
  | "end"   { END }
  | "while" { WHILE }
  | "loop"  { LOOP }
  | "endloop" { ENDLOOP }
  | "case"    { CASE }
  | "of"      { OF }
  | "endcase" { ENDCASE }
  | "proc"    { PROC }
  | "return"  { RETURN }
  | "nop"     { NOP }
  | "module"  { MODULE }
  | "modspec" { MODSPEC }
  | "import"  { IMPORT }
  | "as"      { AS }
  | "open"    { OPEN }
  | "export"  { EXPORT }
  | "private" { PRIVATE }
  | '.'       { DOT }
  | "type"    { TYPE }
  | "struct"  { STRUCT }
  | "variant" { VARIANT }
  | "mut"     { MUT }
  | "True"    { TRUE }    (* Is this the place to put built-in names? *)
  | "False"   { FALSE }   (* Even if not, bools might be special. *)
  | "Null"    { NULL }
  | ident_lc as v	{ IDENT_LC v }
  | ident_uc as v	{ IDENT_UC v }
  | eof     { EOF }
  | _ as c 
    { raise (Error (Printf.sprintf "Unexpected character %c" c)) }
     (* (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) } *)

and comment depth = parse
  | "(*" { comment (depth+1) lexbuf }
  | "*)" { if depth = 0 then token lexbuf else comment (depth-1) lexbuf }
  | eof { raise (Error "Unterminated comment at end of file") }
  | _ { comment depth lexbuf }
  
and string acc = parse
               | '"' { STRCONST (Buffer.contents acc) }
  | '\\' '\"' { Buffer.add_char acc '\"'; string acc lexbuf }
  | "\\n" { Buffer.add_char acc '\n'; string acc lexbuf }
  | "\\t" { Buffer.add_char acc '\t'; string acc lexbuf }
  (* TODO: \x, maybe \f and \b also (whatever they mean) *)
  | "\\\\" { Buffer.add_char acc '\\'; string acc lexbuf }
  | [^ '"' '\\']+ { Buffer.add_string acc (Lexing.lexeme lexbuf);
                    string acc lexbuf }
  (* it seems to not be catching this *)
  | '\n' { raise (Error "String not terminated at newline") }
  | eof { raise (Error "Unterminated string constant at end of file") }
  | _ { raise (Error ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
