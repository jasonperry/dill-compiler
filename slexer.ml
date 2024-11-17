(** sedlex lexer for dill *)

open Sedlexing  (* new_line, loc stuff that parser will use *)
open Syntax     (* my SyntaxError exception type *)
open Parser     (* token types from there *)
(* Not in common.ml for now, Other modules might have different error
   types. Or, should I make a unified error type? *)
(* Idea: parameterize the module by encoding *)
module Enc = Sedlexing.Utf8

(* Regular expressions *)
let newline = [%sedlex.regexp? Opt '\r', '\n']
let whitespace = [%sedlex.regexp? (' ' | '\t')]
let digit = [%sedlex.regexp? '0'..'9']
let hexdigit = [%sedlex.regexp? ('0'..'9' | 'a'..'f' | 'A'..'F')]
let iconst = [%sedlex.regexp? Plus digit]
let hexconst = [%sedlex.regexp? "0x", Plus hexdigit]
let expon = [%sedlex.regexp? Opt ('e' | 'E'), Opt ('-' | '+'), Plus digit] 
let fconst = [%sedlex.regexp? Plus digit, '.', Star digit, Opt expon]
let ident_lc =
  [%sedlex.regexp? ('a'..'z' | '_'),
                 Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]
let qident_lc = [%sedlex.regexp? Opt (ident_lc, "::"), ident_lc]
let ident_uc =
  [%sedlex.regexp? ('A'..'Z'), Star ('a'..'z' | 'A'..'Z' | '0'..'9' | '_')]
(* Currently parsing :: as a separate token. *)
(* let qident_uc = [%sedlex.regexp? Opt (ident_lc, "::"), ident_uc] *)
let vlabel = [%sedlex.regexp? '#', ident_lc]
let hexbyte = [%sedlex.regexp? "\\x", Rep (hexdigit, 2)]
(* ASCII printable except ' and \ (for char literals) *)
(* leaving out double quote (34), '"' works in ocaml. *)
let char_noesc = [%sedlex.regexp? (20 .. 38 | 40 .. 91 | 93 .. 126)]
(* Any unicode except ' and \ for string literals. May not be needed. *)
let str_noesc = [%sedlex.regexp? Sub (any, Chars "\"\\")]
(*
type ttype =
  | I_LIT of Int64.t
  | F_LIT of float
  | S_LIT of string
  | B_LIT of char
  | LC_IDENT of string
  | UC_IDENT of string
  | VLABEL of string
  | LPAREN | RPAREN | LBRACE | RBRACE | LSQRB | RSQRB
  | PLUS | MINUS | TIMES | DIV | MOD
  (* | UMINUS (* not lexed *) *)
  | AMP | PIPE | CARAT | TILDE (* bitwise operators *)
  | SHL | SHR  (* logical shift *)
  | EQ | NE | LT | GT | LE | GE
  | AND | OR | NOT (* Which ones overloadable? Maybe not these. *)
  | TRUE | FALSE | NULL (* | VAL *)
  | COLON | DCOLON | SEMI | DOT | COMMA
  | HASH | DOLLAR | QMARK | ARROW | DARROW
  | ASSIGN | NULLASSIGN
  | VAR | REF | IMMREF
  | NOP
  | IF | THEN | ELSIF | ELSE | ENDIF 
  | WHILE (* | LOOP *) | ENDWHILE
  | CASE | OF | ENDCASE
  | IS | DO
  | PRIVATE | PROC | ENDPROC | RETURN
  | MODULE (* | BEGIN *) | ENDMODULE | MODSPEC | ENDMODSPEC
  | IMPORT | AS | OPEN (* | EXPORT *) | REQUIRE
  | TYPE | ENDTYPE | OPAQUE | REC | RECORD | VARIANT | MUT 
  | EOF

type token = {
  ttype: ttype;
  loc: Lexing.position * Lexing.position
}
*)
(* Map and function for unparsing and error messages. *)
module Ttype =
  struct
    type t = token
    let compare = Stdlib.compare
  end

(* Used by the parser to generate error messages also. *)
module TokenMap = Map.Make(Ttype)
let ttype_strings = List.fold_left  (* of_list in ocaml 5.1 *)
    (fun m (k,v) -> TokenMap.add k v m) TokenMap.empty [
    (LPAREN, "("); (RPAREN, ")"); (LBRACE, "{"); (RBRACE, "}");
    (LSQRB, "["); (RSQRB, "]"); (PLUS, "+"); (MINUS, "-");
    (TIMES, "*"); (DIV, "/"); (MOD, "%"); (CARAT, "^"); (TILDE, "~");
    (BANG, "!"); (AMP, "&"); (SHL, "<<"); (SHR, ">>"); (EQ, "==");
    (NE, "!="); (LT, "<"); (LE, "<="); (GT, ">"); (GE, ">=");
    (AND, "&&"); (OR, "||"); (HASH, "#"); (QMARK, "?"); (DOLLAR, "$");
    (ASSIGN, "="); (NULLASSIGN, "?="); (ARROW, "->"); (DARROW, "=>");
    (DOT, "."); (SEMI, ";"); (DCOLON, "::"); (COMMA, ","); (COLON, ":");
    (MODULE, "module"); (* (BEGIN, "begin"); *) (ENDMODULE, "/module");
    (IMPORT, "import"); (OPEN, "open"); (AS, "as"); (PRIVATE, "private");
    (MODSPEC, "modspec"); (ENDMODSPEC, "/modspec"); (REQUIRE, "require");
    (IS, "is"); (DO, "do");
    (PROC, "proc"); (ENDPROC, "/proc"); (RETURN, "return");
    (VAR, "var"); (REF, "ref"); (NOP, "nop"); (IF, "if"); (THEN, "then");
    (ELSIF, "elsif"); (ELSE, "else"); (ENDIF, "/if");
    (WHILE, "while"); (* (LOOP, "loop"); *) (ENDWHILE, "/while");
    (CASE, "case"); (OF, "of"); (ENDCASE, "/case");
    (OPAQUE, "opaque"); (TYPE, "type"); (MUT, "mut"); (REC, "rec");
    (STRUCT, "struct"); (VARIANT, "variant");
    (TRUE, "#true"); (FALSE, "#false"); (NULL, "#null")
  ]

(** For converting tokens back to strings. Use this in Ast also *)
let string_of_ttype = function
  | I_LIT n -> Int64.to_string n
  | F_LIT x -> string_of_float x
  | S_LIT s -> "\"" ^ String.escaped s ^ "\""
  | B_LIT c -> "'" ^ Char.escaped c ^ "'"
  | UC_IDENT s -> s
  | LC_IDENT s -> s
  | VLABEL s -> s
  | t -> TokenMap.find t ttype_strings

(* Useful in parser for error messages. But does the lexer also store this? *)
let string_of_token token = string_of_ttype token

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
    | newline ->  (* sedlex doesn't need you to manually bump newlines *)
      (* new_line buf; *) tparse buf
    | "(*" ->
      comment 0 buf
    | '\'' ->
      byte [] buf
    | "\"" ->
       string (Buffer.create 80) buf
    | iconst -> I_LIT (Int64.of_string (Enc.lexeme buf))
    | hexconst -> I_LIT (Int64.of_string (Enc.lexeme buf))
    | fconst -> F_LIT (Float.of_string (Enc.lexeme buf))
    | "#true" -> TRUE
    | "#false" -> FALSE
    | "#null" -> NULL
    | vlabel -> VLABEL (Enc.lexeme buf)
    (* | '#' -> HASH *)
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
    | "<<" -> SHL
    | ">>" -> SHR
    | "==" -> EQ
    | "!=" -> NE
    | '<' -> LT
    | "<=" -> LE
    | ">" -> GT
    | ">=" -> GE
    | "&&" -> AND
    | "||" -> OR
    | '!' -> BANG
    | '?' -> QMARK  (* Maybe later: attached to something else. *)
    | '$' -> DOLLAR
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
    (* | "ref^" -> IMMREF *)
    | "ref" -> REF
    | "nop" -> NOP
    | "if" -> IF
    | "then" -> THEN
    | "elsif" -> ELSIF
    | "else" -> ELSE
    | "/if" -> ENDIF
    | "while" -> WHILE
    (* | "loop" -> LOOP *)
    | "/while" -> ENDWHILE
    | "case" -> CASE
    | "of" -> OF
    | "/case" -> ENDCASE
    | "proc" -> PROC
    | "/proc" -> ENDPROC
    | "return" -> RETURN
    | "is" -> IS
    | "do" -> DO
    | "module" -> MODULE
    (* | "begin" -> BEGIN *)
    | "/module" -> ENDMODULE
    | "modspec" -> MODSPEC
    | "/modspec" -> ENDMODSPEC (* Should put these in separate parser? *)
    | "import" -> IMPORT
    | "as" -> AS
    | "open" -> OPEN
    (* | "export" -> EXPORT *)
    | "private" -> PRIVATE
    | "type" -> TYPE
    | "/type" -> ENDTYPE
    | "rec" -> REC
    | "opaque" -> OPAQUE
    | "mut" -> MUT
    | "record" -> STRUCT
    | "variant" -> VARIANT
    | ident_lc -> LC_IDENT (Enc.lexeme buf)
    | ident_uc -> UC_IDENT (Enc.lexeme buf)
    | eof -> EOF
    (* Lexeme will be empty unless we match an actual regex. *)
    | any ->
      raise (syntax_error ("Unexpected character: "
                           ^ Enc.lexeme buf) buf) 
    | _ -> failwith "Unreachable: slexer.tparse"

(* lexing rule for ident chained together with restricted whitespace *)
(* but it has to return multiple tokens; do I have to do some sort of push/pop? *)
(* or generalize so multiple tokens can be returned? *)
(* nevermind *)

and comment depth buf =
  match%sedlex buf with
  | "(*" -> comment (depth+1) buf
  | "*)" ->
    if depth = 0 then tparse buf else comment (depth-1) buf
  | newline -> (* new_line buf; *) comment depth buf
  | eof -> raise (syntax_error "Unterminated comment at EOF" buf)
  | any -> comment depth buf (* unicode in comments too, yay! *)
  | _ -> failwith "Unreachable: slexer.comment"

and string acc buf = 
  match%sedlex buf with
  | '"' -> S_LIT (Buffer.contents acc)
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
      B_LIT (List.hd acc)
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
let token buf = tparse buf
  (* { ttype=tparse buf; loc=lexing_positions buf } *)
