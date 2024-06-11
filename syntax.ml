(** Syntax error exception type for use by the parser and top level *)
exception SyntaxError of {
    msg: string;
    loc: Lexing.position * Lexing.position
}
