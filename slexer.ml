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
let hexdigit = [%sedlex.regexp? ('0'..'9' | 'a'..'f' | 'A'..'F')]
let iconst = [%sedlex.regexp? Opt '-', Plus digit]
let hexconst = [%sedlex.regexp? "0x", Plus hexdigit]
let expon = [%sedlex.regexp? Opt ('e' | 'E'), Opt ('-' | '+'), Plus digit] 
let fconst = [%sedlex.regexp? Opt '-', Plus digit, '.', Star digit, Opt expon]
let ident_lc =
  [%sedlex.regexp? ('a'..'z' | '_'),
                 Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]
let ident_uc =
  [%sedlex.regexp? ('A'..'Z'), Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]
let ident_sym = [%sedlex.regexp? '#', ident_lc]
let symbol = [%sedlex.regexp? '#', ident_lc]
let hexbyte = [%sedlex.regexp? "\\x", Rep (hexdigit, 2)]
(* ASCII printable except ' and \ (for char literals) *)
(* leaving out double quote (34), '"' works in ocaml. *)
let char_noesc = [%sedlex.regexp? (20 .. 38 | 40 .. 91 | 93 .. 126)]
(* Any unicode except ' and \ for string literals. May not be needed. *)
let str_noesc = [%sedlex.regexp? Sub (any, Chars "\"\\")]

type ttype =
  | ICONST of Int64.t
  | FCONST of float
  | STRCONST of string
  | BYTECONST of char
  | IDENT_LC of string
  | IDENT_UC of string
  | LPAREN | RPAREN | LBRACE | RBRACE | LSQRB | RSQRB
  | PLUS | MINUS | TIMES | DIV | MOD
  (* | UMINUS (* not lexed *) *)
  | AMP | PIPE | CARAT | TILDE (* bitwise operators *)
  | EQ | NE | LT | GT | LE | GE
  | AND | OR | NOT (* Which ones overloadable? Maybe not these. *)
  | TRUE | FALSE | NULL (* | VAL *)
  | COLON | DCOLON | SEMI | DOT | COMMA (* | HASH | QMARK *) | ARROW | DARROW
  | ASSIGN | NULLASSIGN
  | VAR | REF | IMMREF
  | NOP
  | IF | THEN | ELSIF | ELSE | ENDIF 
  | WHILE | LOOP | ENDWHILE
  | CASE | OF | ENDCASE
  | IS
  | PROC | ENDPROC | RETURN
  | MODULE | ENDMODULE | MODSPEC | ENDMODSPEC
  | IMPORT | AS | OPEN | EXPORT | PRIVATE
  | TYPE | OPAQUE | REC | RECORD | VARIANT | MUT (* | ENUM *)
  | EOF
  
type token = {
  ttype: ttype;
  loc: Lexing.position * Lexing.position
}

(* do I have to write my own to_string for the buf? *)
let string_of_ucarray arr =
  String.of_seq (Array.to_seq (Array.map Uchar.to_char arr))

let syntax_error msg buf =
  SyntaxError { msg=msg;
                loc=lexing_positions buf }

let rec tparse (buf: Sedlexing.lexbuf) =
  match%sedlex buf with
    | whitespace ->
      tparse buf
    | newline ->
      new_line buf; tparse buf
    | "(*" ->
      comment 0 buf
    | '\'' ->
      byte [] buf
    | "\"" ->
       string (Buffer.create 80) buf
    | iconst -> ICONST (Int64.of_string (Enc.lexeme buf))
    | hexconst -> ICONST (Int64.of_string (Enc.lexeme buf))
    | fconst -> FCONST (Float.of_string (Enc.lexeme buf))
    | '(' -> LPAREN
    | ')' -> RPAREN
    | '{' -> LBRACE
    | '}' -> RBRACE
    | '[' -> LSQRB
    | ']' -> RSQRB
    | '+' -> PLUS
    | '-' -> MINUS
    | '*' -> TIMES
    | '/' -> DIV
    | '%' -> MOD
    | '^' -> CARAT (* overloadable, maybe *)
    | '|' -> PIPE
    | '&' -> AMP
    | '~' -> TILDE (* bitwise not *)
    | "==" -> EQ
    | "!=" -> NE
    | '<' -> LT
    | "<=" -> LE
    | ">=" -> GT
    | "&&" -> AND
    | "||" -> OR
    | '!' -> NOT
    (* | '#' -> HASH
       | '?' -> QMARK *) (* Must be attached to something else. *)
    | '=' -> ASSIGN
    | "?=" -> NULLASSIGN
    | "->" -> ARROW
    | "=>" -> DARROW
    | ',' -> COMMA
    | '.' -> DOT
    | ';' -> SEMI
    | "::" -> DCOLON (* actually this should be attached too. *)
    | ':' -> COLON
    | "var" -> VAR
    | "ref^" -> IMMREF
    | "ref" -> REF
    | "nop" -> NOP
    | "if" -> IF
    | "then" -> THEN
    | "elsif" -> ELSIF
    | "else" -> ELSE
    | "/if" -> ENDIF
    | "while" -> WHILE
    | "loop" -> LOOP
    | "/while" -> ENDWHILE
    | "case" -> CASE
    | "of" -> OF
    | "/case" -> ENDCASE
    | "is" -> IS
    | "module" -> MODULE
    | "/module" -> ENDMODULE
    | "modspec" -> MODSPEC
    | "/modspec" -> ENDMODSPEC (* Should put these in separate parser? *)
    | "import" -> IMPORT
    | "as" -> AS
    | "open" -> OPEN
    | "export" -> EXPORT
    | "private" -> PRIVATE
    | "type" -> TYPE
    | "rec" -> REC
    | "opaque" -> OPAQUE
    | "mut" -> MUT
    | "record" -> RECORD
    | "variant" -> VARIANT
    | ident_lc -> IDENT_LC (Enc.lexeme buf)
    | ident_uc -> IDENT_UC (Enc.lexeme buf)
    | eof -> EOF
    (* Lexeme will be empty unless we match an actual regex. *)
    | any ->
      raise (syntax_error ("Unexpected character: "
                           ^ Enc.lexeme buf) buf) 
    | _ -> failwith "Unreachable: slexer.tparse"

and comment depth buf =
  match%sedlex buf with
  | "(*" -> comment (depth+1) buf
  | "*)" ->
    if depth = 0 then tparse buf else comment (depth-1) buf
  | newline -> new_line buf; comment depth buf
  | eof -> raise (syntax_error "Unterminated comment at EOF" buf)
  | any -> comment depth buf (* unicode in comments too, yay! *)
  | _ -> failwith "Unreachable: slexer.comment"

and string acc buf = 
  match%sedlex buf with
  | '"' -> STRCONST (Buffer.contents acc)
  | "\\\"" -> Buffer.add_char acc '\"'; string acc buf
  | "\\n" -> Buffer.add_char acc '\n'; string acc buf 
  | "\\r" -> Buffer.add_char acc '\r'; string acc buf 
  | "\\t" -> Buffer.add_char acc '\t'; string acc buf 
  | "\\b" -> Buffer.add_char acc '\b'; string acc buf
  | "\\\\" -> Buffer.add_char acc '\\'; string acc buf
  | hexbyte ->
    let bytechar =
      char_of_int (int_of_string ("0x" ^ String.sub (Enc.lexeme buf) 2 2)) in
    Buffer.add_char acc bytechar; string acc buf      
  | "\\", any ->
    raise (syntax_error ("Illegal backslash escape in string: "
                         ^ Enc.lexeme buf) buf)
  | '\n' -> raise (syntax_error "Unterminated string constant at newline" buf)
  | eof -> raise (syntax_error "Unterminated string constant at EOF" buf)
  | str_noesc -> Buffer.add_string acc (Enc.lexeme buf);
    string acc buf
  (* Probably this cannot be reached either. *)
  | any -> raise (syntax_error ("Illegal character in string: "
                                ^ Enc.lexeme buf) buf)
  | _ -> failwith "Unreachable: slexer.string"

and byte (acc: char list) buf =
  match%sedlex buf with
  | '\'' ->
    if List.length acc == 0 then
      raise (syntax_error "Byte constant cannot be empty" buf)
    else if List.length acc > 1 then
      (* could match just the single-char expressions,
         but this is more informative? *)
      raise (syntax_error "Too many characters in byte constant" buf)
    else
      BYTECONST (List.hd acc)
  | "\\n" -> byte ('\n'::acc) buf
  | "\\t" -> byte ('\t'::acc) buf
  | "\\r" -> byte ('\r'::acc) buf
  | "\\b" -> byte ('\b'::acc) buf  (* backspace *)
  | "\\\\" -> byte ('\\'::acc) buf
  | hexbyte ->
    let bytechar =
      char_of_int (int_of_string ("0x" ^ String.sub (Enc.lexeme buf) 2 2)) in
    byte (bytechar::acc) buf
  | "\\", any ->
    raise (syntax_error ("Illegal backslash escape in byte: "
                         ^ Enc.lexeme buf) buf)
  | char_noesc -> byte ((Enc.lexeme buf).[0]::acc) buf
  | any ->
    raise (syntax_error ("Illegal byte constant: " ^ Enc.lexeme buf) buf)
  | _ -> failwith "Unreachable: slexer.byte"
    
(* Wait...will buf be different after? what if I get pos first? *)
let token buf = 
  { ttype=tparse buf; loc=lexing_positions buf }
