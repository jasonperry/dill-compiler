(** Recursive descent parser for dill *)

open Common
open Slexer
open Ast

(* Maybe put this stuff in its own module, or even in the lexer *)
(** Type for simple token buffering/lookahead implementation. *)
type tbuf = {
  buf: token array;
  sbuf: string array; (* Store lexemes of tokens in parallel array *)
  lexbuf: Sedlexing.lexbuf;
  mutable bpos: int;
  lookahead: int;
  (* Info about last lexeme looked at (even if not consumed) *)
  mutable last_lexeme: string;
  mutable last_loc: (Lexing.position * Lexing.position)
}

(** Refill token buffer's lookahead in-place from lexer. *)
let _refill_tbuf tbuf =
  let rec tloop i =
    if i == tbuf.lookahead then ()
    else if tbuf.bpos < tbuf.lookahead then (
      (* If not at end, copy from back of buffer. *)
      Array.set tbuf.buf i tbuf.buf.(tbuf.bpos);
      Array.set tbuf.sbuf i tbuf.sbuf.(tbuf.bpos);
      tbuf.bpos <- tbuf.bpos + 1;
      tloop (i+1))
    else
      (* Otherwise pull from the lexer. *)
      let nexttok = Slexer.token tbuf.lexbuf in
      Array.set tbuf.buf i nexttok;
      Array.set tbuf.sbuf i (Enc.lexeme tbuf.lexbuf);
      if nexttok.ttype = EOF then () (* leave old tokens *)
      else tloop (i+1)
  in
  if tbuf.bpos = 0 then ()  (* no-op case *)
  else tloop 0; tbuf.bpos <- 0

(** Initialize token buffer with specified lookahead size. *)
let init_tbuf lexbuf lookahead =
  let startloc = Sedlexing.lexing_positions lexbuf in
  let tbuf = {
    buf = Array.init lookahead (fun _ ->
        {ttype = EOF; loc=startloc});
    sbuf = Array.init lookahead (fun _ -> "");
    lexbuf = lexbuf;
    bpos = lookahead; (* marks as empty so it can refill *)
    lookahead = lookahead;
    last_lexeme = "";
    last_loc = startloc
  } in
  _refill_tbuf tbuf;
  tbuf

(** Return current token in buffer without moving the pointer. *)
let peek tbuf =
  (* For lookahead 1, this is all we have to check. *)
  if tbuf.bpos = tbuf.lookahead then _refill_tbuf tbuf;
  let i = tbuf.bpos in
  tbuf.last_lexeme <- tbuf.sbuf.(i);
  tbuf.last_loc <- tbuf.buf.(i).loc;
  tbuf.buf.(i)

(** Attempt to eat one token of given type from token buffer. *)
let consume tbuf ttype =
  let tok = peek tbuf in
  let samettype = match (ttype, tok.ttype) with
    (* Could save typing with Obj.tag but I'd feel dirty :) *)
    | ICONST _, ICONST _ -> true
    | FCONST _, FCONST _ -> true
    | STRCONST _, STRCONST _ -> true
    | BYTECONST _, BYTECONST _ -> true
    | IDENT_LC _, IDENT_LC _ -> true
    | IDENT_UC _, IDENT_UC _ -> true
    | _, _ -> ttype = tok.ttype
  in
  if samettype then (
    tbuf.bpos <- tbuf.bpos + 1;
    Some tok)
  else
    (* Oh wait, have to set prev_pos here too. It's really last_pos *)
    None

(** Consume the next token of any type. Should be only for testing? *)
let consume_any tbuf =
  let tok = peek tbuf in
  tbuf.bpos <- tbuf.bpos + 1;
  tok

let last_lexeme tbuf = tbuf.last_lexeme
let last_loc tbuf = tbuf.last_loc


(* -------------------- Parser Proper ------------------ *)

(* helpers to extract token values. *)
let tok_ival tok = match tok.ttype with
  | ICONST i -> i
  | _ -> failwith "can't get integer from non-int token "
let tok_fval tok = match tok.ttype with
  | FCONST x -> x
  | _ -> failwith "can't get float from non-float token "
let tok_cval tok = match tok.ttype with
  | BYTECONST c -> c
  | _ -> failwith "can't get char from non-char token "
let tok_sval tok = match tok.ttype with
  | STRCONST s | IDENT_LC s | IDENT_UC s -> s
  | _ -> failwith "can't get string from non-string token "

(** Helper for general parse error messages. *)
let parse_error msg tbuf =
  SyntaxError {
    msg = msg;
    loc = last_loc tbuf
  }

(** Helper for "expected this, got that" error messages. *)
let expect_error estr tbuf =
  SyntaxError {
    msg = "Expected " ^ estr ^ ", found \"" ^ last_lexeme tbuf ^ "\"";
    loc = last_loc tbuf
  }

(** Helper for "unexpected token" messages *)
let unexpect_error tbuf =
  SyntaxError {
    msg = "Unexpected token \"" ^ last_lexeme tbuf ^ "\"";
    loc = last_loc tbuf
  }

(** Helper to add location to an AST object. *)
let make_located node (stok: token) (etok: token) = {
  value = node;
  loc = (fst stok.loc, snd etok.loc)
}

let semicolon tbuf =
  match (consume tbuf SEMI) with
  | None -> raise (expect_error "';'" tbuf)
  | Some tok -> tok (* needed for location *)

(** Parse a given token type *)
let parse_tok ttype tbuf =
  match (consume tbuf ttype) with
  | None -> raise (expect_error (string_of_ttype ttype) tbuf)
  | Some tok -> tok

(** Parse unqualified name *)
let uname descrip tbuf =
  match (consume tbuf (IDENT_LC "")) with
     | None -> raise (expect_error descrip tbuf)
     | Some tok -> tok

let proc tbuf =
  (* let qualifiers = EXPORT, PRIVATE *)
  let ptok = Option.get (consume tbuf PROC) in
  let _ (* spos *) = fst ptok.loc in
  (* generic params *)
  match (consume tbuf (IDENT_LC "")) with
  | None -> raise (expect_error "procedure name" tbuf)
  | Some pname -> print_string ("found proc " ^ tok_sval pname)

(** Parse an arbitrary number of a given object. *)
let list_of pf tbuf =
  (* need a list of matching tokens? FIRST set? *)
  (* or the thing just returns none? *)
  let rec loop acc =
    match pf tbuf with
    | Some thing -> loop (thing::acc)
    | None -> List.rev acc
  in loop []

(** Parse a single import statement or nothing. *)
let import tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  | IMPORT ->
    (* maybe a "pop" function would be nice *)
    let _ = Option.get (consume tbuf IMPORT) in
    let mntok = uname "module name" tbuf in
    let alias = match (peek tbuf).ttype with
      | AS ->
        let _ = Option.get (consume tbuf AS) in
        let matok = uname "module alias" tbuf in
        Some (tok_sval matok)
      | _ -> None
    in
    let etok = semicolon tbuf in
    Some (make_located (Import (tok_sval mntok, alias)) stok etok)
  | OPEN ->
    let _ = Option.get (consume tbuf OPEN) in
    let mntok = uname "module name" tbuf in 
    let etok = semicolon tbuf in 
    Some (make_located (Open (tok_sval mntok)) stok etok)
  | _ -> None
             
let module_body mname tbuf =
  { name = mname;
    imports = list_of import tbuf;
    typedefs = [];
    globals = [];
    procs = [];
  }
              
   (* loop to accumulate both types and global vars?
           or strictly types first?  *)
  (* let tok = peek tbuf in
  match tok.ttype with
  (* I can make imports come first, yay. *)
  | IMPORT -> print_string "Imports with no module"
  (* need lookahead 2 for these? *)
  | EXPORT -> print_string "Exporting a proc prolly, aight"
  | PRIVATE -> print_string "Keepin secrets eh"
  | PROC -> proc tbuf
  | ICONST i -> print_string ("ICONST " ^ Int64.to_string i ^ "\n")
  | VAR -> print_string ("Global variable ya")
     | _ -> raise (unexpect_error tbuf) *)

let dillsource tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  | MODULE ->
    let _ (* spos *) = fst (stok.loc) in 
    let _ = Option.get (consume tbuf MODULE) in
    let mntok = uname "module name" tbuf in
    let _ = parse_tok IS tbuf in 
    let the_module = module_body (tok_sval mntok) tbuf in
       (match (consume tbuf ENDMODULE) with
        | Some _ ->
          let _ (* epos *) = snd (last_loc tbuf) in
          [the_module]
        | None -> raise (expect_error "\"/module\"" tbuf)
       )
  | _ -> [module_body "" tbuf] (* get location from returned body. *)

(* for testing the lexer and token buffer. Any sequence of valid tokens. *)
let rec any_tokens buf =
  match (consume_any buf).ttype with 
  | ICONST i -> print_string ("(ICONST " ^ Int64.to_string i ^ ") ");
    any_tokens buf
  | FCONST x -> print_string ("(FCONST " ^ string_of_float x ^ ") ");
    any_tokens buf
  | BYTECONST c -> print_string ("(BYTECONST '" ^ Char.escaped c ^ "') ");
    any_tokens buf
  | STRCONST s -> print_string ("(STRCONST \"" ^ String.escaped s ^ "\") ");
    any_tokens buf
  | IDENT_LC s -> print_string ("(IDENT_LC " ^ s ^ ") "); any_tokens buf
  | IDENT_UC s -> print_string ("(IDENT_UC " ^ s ^ ") "); any_tokens buf
  | EOF -> print_string "EOF\n "; (* don't recurse *)
  | _ -> print_string "token "; any_tokens buf

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
  let lexbuf = Sedlexing.Utf8.from_channel stdin in
  (* from_string "42 '\\n' 'w' 'เ' (* เมืองจึงวิปริตเป็นนัก *) '\x41' 44 f" in *)
  let tbuf = init_tbuf lexbuf 10 in
  (* any_tokens tbuf *)
  let modules = dillsource tbuf in
  String.concat "\n" (List.map module_to_string modules)
