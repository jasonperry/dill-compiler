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
let ident_body = ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let ident_lc = ['a'-'z' '_'] ident_body
let ident_uc = ['A'-'Z'] ident_body
let ident_variant = '#' ident_body
let typevar = '\'' ident_body [^ '\'']
                    
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
  | "**"
    { linecomment lexbuf }
  | '\''
    { byte [] lexbuf }
  | "\""
    { string (Buffer.create 80) lexbuf }
  | iconst as i
   (* OCaml seems to use 63-bit ints now. *)
    { I_LIT (Int64.of_string i) }
  | fconst as f
    { F_LIT (float_of_string f) }
  | '('     { LPAREN }
  | ')'     { RPAREN }
  | '{'     { LBRACE }
  | '}'     { RBRACE }
  | '['     { LSQRB }
  | ']'     { RSQRB }
  | '*'     { TIMES }
  | '/'     { DIV }
  | '%'     { MOD }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '&'     { AMP }
  | '|'     { PIPE }
  | '^'     { CARAT }
  | '~'     { TILDE }
  | "<<"    { SHL }
  | ">>"    { SHR }
  (* | "++"   { CONCAT } *)
  | "=="    { EQ }
  | "!="    { NE }
  | "<"     { LT }
  | ">"     { GT }
  | "<="    { LE }
  | ">="    { GE }
  | "&&"    { AND }
  | "||"    { OR }
  | '!'     { BANG }
  | '#'     { HASH }
  | '$'     { DOLLAR }
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
  | "ref"   { REF }
  | "if"    { IF }
  | "then"  { THEN }
  | "elsif" { ELSIF }
  | "else"  { ELSE }
  | "/if" { ENDIF }
  | "is"    { IS }
  | "do"    { DO }
  (* | "begin" { BEGIN } *)
  (*  | "end"   { END } *)
  | "while" { WHILE }
  (* | "loop"  { LOOP } *)
  | "/while" { ENDWHILE }
  | "case"    { CASE }
  | "of"      { OF }
  | "/case" { ENDCASE }
  | "proc"    { PROC }
  | "/proc"   { ENDPROC }
  | "return"  { RETURN }
  | "nop"     { NOP }
  | "module"  { MODULE }
  | "/module" { ENDMODULE }
  | "import"  { IMPORT }
  | "as"      { AS }
  | "open"    { OPEN }
  | "private" { PRIVATE }
  | "modspec" { MODSPEC }
  | "/modspec" { ENDMODSPEC }
  (* | "export"  { EXPORT } *)
  | "require" { REQUIRE }
  | '.'       { DOT }
  | "type"    { TYPE }
  | "/type"   { ENDTYPE }
  | "rec"     { REC }
  | "opaque"  { OPAQUE }
  | "record"  { STRUCT }
  | "variant" { VARIANT }
  | "mut"     { MUT }
  | "#true"    { TRUE }    (* these also represent values *)
  | "#false"   { FALSE }
  | "#null"    { NULL }
  | "#val"     { VAL }
  | ident_lc as s	{ LC_IDENT s }
  | ident_uc as s	{ UC_IDENT s }
  | ident_variant as v  { VLABEL v }
  | eof     { EOF }
  | _ as c 
    { raise (Error (Printf.sprintf "Unexpected character %c" c)) }
     (* (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) } *)

and comment depth = parse
  | "(*" { comment (depth+1) lexbuf }
  | "*)" { if depth = 0 then token lexbuf else comment (depth-1) lexbuf }
  (* Oh, I still have to count newlines! *)
  | '\n' { new_line lexbuf; comment depth lexbuf }
  | eof { raise (Error "Unterminated comment at end of file") }
  | _ { comment depth lexbuf }

and linecomment = parse
  | '\n' { new_line lexbuf; token lexbuf }
  | _ { linecomment lexbuf }

and string acc = parse
  | '"' { S_LIT (Buffer.contents acc) }
  | '\\' '\"' { Buffer.add_char acc '\"'; string acc lexbuf }
  | "\\n" { Buffer.add_char acc '\n'; string acc lexbuf }
  | "\\r" { Buffer.add_char acc '\r'; string acc lexbuf }
  | "\\t" { Buffer.add_char acc '\t'; string acc lexbuf }
  (* TODO: \x, maybe \f and \b also (whatever they mean) *)
  | "\\\\" { Buffer.add_char acc '\\'; string acc lexbuf }
  (* The ^ means "not", so this is the one that matches a regular char letter *)
  | [^ '"' '\\']+ { Buffer.add_string acc (Lexing.lexeme lexbuf);
                    string acc lexbuf }
  (* it seems to not be catching this *)
  | '\n' { raise (Error "String not terminated at newline") }
  | eof { raise (Error "Unterminated string constant at end of file") }
  | _ { raise (Error ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }

and byte acc = parse
  | '\'' {
      if List.length acc == 0 then 
        raise (Error "Byte constant cannot be empty") 
      else if List.length acc > 1 then
        raise (Error ("Byte constant too long: " ^ Lexing.lexeme lexbuf)) 
      else
        B_LIT (List.hd acc)
    }
  | "\\n" { byte ('\n'::acc) lexbuf } (* doesn't matter if it reverses. *)
  | "\\t" { byte ('\t'::acc) lexbuf }
  | "\\r" { byte ('\r'::acc) lexbuf }
  (* TODO: hex \x## *) (* oh wait, it could be multiple types *)
  | "\\\\" { byte ('\\'::acc) lexbuf }
  | [^ '"' '\\'] { byte ((Lexing.lexeme_char lexbuf 0)::acc) lexbuf }
  | '\n' { raise (Error "Byte constant not terminated at newline") }
  | eof { raise (Error "Unterminated byte constant at end of file") }
  | _ { raise (Error ("Illegal byte constant: " ^ Lexing.lexeme lexbuf)) }

                 
