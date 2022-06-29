(* Syntax error type and exception for use by the parser and top level *)

type syntax_error = (Lexing.position * Lexing.position) * string

exception SyntaxError of syntax_error
