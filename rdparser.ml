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

(** LL(2) lookahead *)
let peek2 tbuf =
  if tbuf.bpos >= tbuf.lookahead - 1 then _refill_tbuf tbuf;
  let i = tbuf.bpos + 1 in
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


(* -------------------- Parser Helper Functions ------------------ *)

(* helpers to extract token values. Maybe not needed now. *)
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

(** Make location out of a start and end position. *)
let make_location (t1spos, _) (_, t2epos) =
  (t1spos, t2epos)

(** Helper to add location to an AST object. *)
let make_located node (t1spos, _) (_, t2epos) = {
  value = node;
  loc = (t1spos, t2epos)
}

(** Parse an arbitrary number of a given object. *)
let list_of pf tbuf =
  (* need a list of matching tokens? FIRST set? *)
  (* or the thing just returns none? *)
  let rec loop acc =
    match pf tbuf with
    | Some thing -> loop (thing::acc)
    | None -> List.rev acc
  in loop []

(*
(** Maybe parse a given object, but OK if not (catch exception) *)
let option rule tbuf =
  try (rule tbuf) with
  | SyntaxError _ -> None (* no it hides errors *)
  | res -> Some res
*)

(* ----------------- rule functions begin ---------------- *)

(*
let semicolon tbuf =
  match (consume tbuf SEMI) with
  | None -> raise (expect_error "';'" tbuf)
  | Some tok -> tok.loc 
   *)

(* "Token parsers" seem to have special status. They are the only ones
   that call "consume" directly and use the coercion functions. *)

(** Consume token of given type, with error message if not *)
let get_tok ttype descrip tbuf =
  match (consume tbuf ttype) with
  | None -> raise (expect_error descrip tbuf)
  | Some tok -> tok

(** Parse a given token type without data, returning only location *)
let parse_tok ttype tbuf =
  (get_tok ttype (string_of_ttype ttype) tbuf).loc

let iconst tbuf =
  let tok = get_tok (ICONST Int64.zero) "integer constant" tbuf in
  (tok_ival tok, tok.loc)
                
let fconst tbuf =
  let tok = get_tok (FCONST 0.0) "float constant" tbuf
  in (tok_fval tok, tok.loc)

let bconst tbuf =
  let tok = get_tok (BYTECONST '@') "byte constant" tbuf
  in (tok_cval tok, tok.loc)

let sconst tbuf =
  let tok = get_tok (STRCONST "") "string constant" tbuf
  in (tok_sval tok, tok.loc)

(** Parse unqualified lowercase name. Takes a description string from context
    so errors can say what the value is for. *)
let uqname descrip tbuf =
  let tok = get_tok (IDENT_LC "") descrip tbuf in
  (tok_sval tok, tok.loc)

(* possibly qualified? *)
let typename tbuf =
  let tok = get_tok (IDENT_UC "") "class name" tbuf in
  (tok_sval tok, tok.loc)

(* ---- end of single-token parsers ---- *)

let rec expr tbuf =
  (* Get a single expression, then look for operators, and finally
     compute precedence *)
  match (peek tbuf).ttype with
  | LPAREN ->
    let sloc = parse_tok LPAREN tbuf in
    let e = expr tbuf in (* exprs already have location *)
    let eloc = parse_tok RPAREN tbuf in
    { e=e.e; decor=make_location sloc eloc }
  | ICONST _ ->
    let (n, tloc) = iconst tbuf in
    { e=ExpConst (IntVal n); decor=make_location tloc tloc }
  | FCONST _ ->
    let (x, tloc) = fconst tbuf in
    { e=ExpConst (FloatVal x); decor=make_location tloc tloc }
  | BYTECONST _ ->
    let (c, tloc) = bconst tbuf in
    { e=ExpConst (ByteVal c); decor=make_location tloc tloc }
  | STRCONST _ ->
    let (s, tloc) = sconst tbuf in
    { e=ExpConst (StringVal s); decor=make_location tloc tloc }
  | _ -> raise (expect_error "Unknown expression token" tbuf)

(* and operTail tbuf = (\* look for operators following *\) *)

  (* want to try multiple things in a natural way... *)
  (* Maybe I should raise errors always and catch them... *)
  (* Where do I put the logic of when I'm "committed" to parsing that type
     of thing? *)
  (* step 1: constExp vs OpExp *)
(* exp's recursive "buddies" can be different from other things *)

(** typeExpr doesn't return separate location, it's in the struct. *)
let typeExpr tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  (* Can't just do "qtypename" because an lc_ident could be a type
     variable also. *)
  | IDENT_LC _ ->
    (* maybe move this out to qualTypename or just typename? *)
    let (n1, _) = uqname "module name or type variable" tbuf in
    (match (peek tbuf).ttype with
     | DCOLON ->
       ignore (parse_tok DCOLON tbuf);
       let (cn, el1) = typename tbuf in
       (* TODO: parse type args/nullable/array markers *)
       { texpkind=(
            Concrete {
              modname=n1; classname=cn;
              typeargs=[];
            });
           (* nullable should be 'option' *)
           nullable=false; array=false;
           loc=make_location stok.loc el1
       }
     | _ -> failwith "todo: type var parsing"
    )
  | IDENT_UC _ -> 
    let (cn, el1) = typename tbuf in
    (* TODO: parse type args/nullable/array markers *)
    { texpkind=(
         Concrete {
           modname=""; classname=cn;
           typeargs=[];
         });
        (* nullable should be 'option' *)
        nullable=false; array=false;
        loc=make_location stok.loc el1
      }
  | _ -> raise (expect_error "type expression" tbuf)
           
(* if initializer is required, the caller will check, right? *)
(* Yes, I think that's better than trying to divide syntactically. *)
let declStatement tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  | VAR -> 
    let sloc = parse_tok VAR tbuf in
    let (vname, _) = uqname "lvalue" tbuf in
    let tyopt = 
      (match (peek tbuf).ttype with
       | COLON ->  (* has type expression *)
         ignore (parse_tok COLON tbuf);
         Some (typeExpr tbuf)
       | _ -> None
      ) in
    let initopt = None in
    let eloc = parse_tok SEMI tbuf in
    Some ((vname, tyopt, initopt), (sloc, eloc))
  | _ -> None
    
(** Parse a single import statement or nothing. *)
let import tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  | IMPORT ->
    let sloc = parse_tok IMPORT tbuf in
    let (mname, _) = uqname "module name" tbuf in
    let alias = match (peek tbuf).ttype with
      | AS ->
        let _ = parse_tok AS tbuf in
        let (malias, _) = uqname "module alias" tbuf in
        Some malias
      | _ -> None
    in
    let eloc = parse_tok SEMI tbuf in
    (make_located (Import (mname, alias)) sloc eloc)
  | OPEN ->
    let sloc = parse_tok OPEN tbuf in
    let (mname, _) = uqname "module name" tbuf in 
    let eloc = parse_tok SEMI tbuf in 
    (make_located (Open mname) sloc eloc)
  | _ -> failwith "BUG: import called with non-import token"

let visibility tbuf =
  let stok = peek tbuf in
  let vis = match stok.ttype with
    | EXPORT -> let _ = parse_tok EXPORT tbuf in Export
    | PRIVATE -> let _ = parse_tok PRIVATE tbuf in Private 
    | _ -> Default
  in 
  (vis, stok.loc)

let param_info tbuf =
  let sloc = (peek tbuf).loc in
  let mutmark = match (peek tbuf).ttype with
    | DOLLAR ->
      ignore (parse_tok DOLLAR tbuf); true
    | _ -> false
  in
  let (varname, _) = uqname "parameter name" tbuf in
  let _ = parse_tok COLON tbuf in
  let texp = typeExpr tbuf in
  ((mutmark, varname, texp), make_location sloc texp.loc)
  
(* want list-of but have to have something that might return none *)
let param_list tbuf =
  let sloc = (peek tbuf).loc in
  let rec loop eloc =
    match (peek tbuf).ttype with
    | RPAREN -> ([], eloc)
    | _ -> let (pinfo, ploc) = param_info tbuf in
      (match (peek tbuf).ttype with
       | COMMA ->
         let (rest, eloc) = loop ploc in
         (pinfo::rest, eloc)
       | _ -> ([], eloc))
  in
  let (plist, eloc) = loop sloc in
  (List.rev plist, make_location sloc eloc)

(** Void typeExpr for when it's implicit. *)
let voidTypeExpr loc =
  { texpkind = (Concrete {
        modname = "";
        classname = "Void";
        typeargs = [] });
    nullable = false;
    array = false;
    loc = loc
  }
          
let proc_header tbuf = 
  let vis, sloc = visibility tbuf in 
  let _ = parse_tok PROC tbuf in
  let (pname, _) = uqname "procedure name" tbuf in
  (* TODO: generic params *)
  let _ = parse_tok LPAREN tbuf in
  let (params, _) = param_list tbuf in 
  let eloc = parse_tok RPAREN tbuf in
  let rettype = match (peek tbuf).ttype with
    | COLON ->
      let _ = parse_tok COLON tbuf in
      typeExpr tbuf
    | _ -> voidTypeExpr eloc
  in 
  { name=pname;
    typeparams = [];
    params = params;
    visibility = vis;
    rettype = rettype;
    decor = make_location sloc rettype.loc
  }

let proc tbuf =
    proc_header tbuf
      
let module_body mname tbuf =
  (* I can make imports come first, yay. *)
  let imports =
    let rec imploop () =
      match (peek tbuf).ttype with
      | IMPORT | OPEN -> (import tbuf)::(imploop ())
      | _ -> []
    in List.rev (imploop ())
  in
  let _ (* procs *) = 
    let rec procloop () =
      if (peek tbuf).ttype = PROC || (peek2 tbuf).ttype = PROC then
        (proc tbuf)::(procloop ())
      else []
    in List.rev (procloop ())
  (* "export" can be on type, global var, or proc *)
   (* loop to accumulate both types and global vars?
           or strictly types first?  *)
  (* need lookahead 2 for these? *)
  (* | EXPORT -> print_string "Exporting a proc prolly, aight"
  | PRIVATE -> print_string "Keepin secrets eh"
  | PROC -> proc tbuf
  | _ -> raise (unexpect_error tbuf) *)
  in
  { name = mname;
    imports = imports;
    typedefs = [];
    globals = [];
    procs = []; (* procs *)
  }


let dillsource tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  | MODULE ->
    let _ (* spos *) = parse_tok MODULE tbuf in
    let (mname, _) = uqname "module name" tbuf in
    let _ = parse_tok IS tbuf in 
    let the_module = module_body mname tbuf in
    let _ (* epos *) = parse_tok ENDMODULE tbuf in
    [the_module]
  (* Thought: allowing top-level code makes it unclear if signatures are
     to be placed "outside"? No it doesn't! *)
  (* need to get location from returned body. *)
  | _ -> [module_body "" tbuf] 

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
  print_string ("Parsed " ^ string_of_int (List.length modules)
                ^ " module(s).\n");
  print_string (String.concat "\n" (List.map module_to_string modules))
