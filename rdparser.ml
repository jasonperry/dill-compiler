(** Recursive descent parser for dill *)

open Common
open Slexer
open Syntax
open Ast

(* for now we get these from the Menhir parser, so it's compatible with the
   lexer. *)
(* type token =
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
*)
    
type tlocated = {
  ttype: Parser.token;
  loc: Lexing.position * Lexing.position
}

(* Maybe put this stuff in its own module, or even in the lexer *)
(** Type for simple token buffering/lookahead implementation. *)
type tbuf = {
  buf: tlocated array;
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
      Array.set tbuf.buf i {ttype=nexttok; loc=Sedlexing.lexing_positions tbuf.lexbuf};
      Array.set tbuf.sbuf i (Enc.lexeme tbuf.lexbuf);
      if nexttok = EOF then () (* leave old tokens *)
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
let consume tbuf (ttype: Parser.token) =
  let tok = peek tbuf in
  let samettype = match (ttype, tok.ttype) with
    (* Could save typing with Obj.tag but I'd feel dirty :) *)
    | I_LIT _, I_LIT _ -> true
    | F_LIT _, F_LIT _ -> true
    | S_LIT _, S_LIT _ -> true
    | B_LIT _, B_LIT _ -> true
    | LC_IDENT _, LC_IDENT _ -> true
    | UC_IDENT _, UC_IDENT _ -> true
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
  | I_LIT i -> i
  | _ -> failwith "can't get integer from non-int token "
let tok_fval tok = match tok.ttype with
  | F_LIT x -> x
  | _ -> failwith "can't get float from non-float token "
let tok_cval tok = match tok.ttype with
  | B_LIT c -> c
  | _ -> failwith "can't get char from non-char token "
let tok_sval tok = match tok.ttype with
  | S_LIT s | LC_IDENT s | UC_IDENT s -> s
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
    msg = "Expected \"" ^ estr ^ "\", found \"" ^ last_lexeme tbuf ^ "\"";
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

(** Parse a token-separated list on an object given by rule. *)
let separated_list_of rule sep follow tbuf =
  let sloc = (peek tbuf).loc in
  let rec loop eloc =
    if (peek tbuf).ttype = follow then
      ([], eloc)
    else
      let (parsed, ploc) = rule tbuf in
      if (peek tbuf).ttype = sep then
         let (rest, eloc) = loop ploc in
         (parsed::rest, eloc)
      else
        ([], eloc)
  in
  let (plist, eloc) = loop sloc in
  (List.rev plist, make_location sloc eloc)
  
(*
(** Maybe parse a given object, but OK if not (catch exception) *)
let option rule tbuf =
  try (rule tbuf) with
  | SyntaxError _ -> None (* no it hides errors *)
  | res -> Some res
*)

(* ----------------- rule functions begin ---------------- *)

(* "Token parsers" seem to have special status. They are the only ones
   that call "consume" directly and use the coercion functions. *)

(** Consume token of given type, emitting error message with given description if not *)
let tok_val (ttype: Parser.token) descrip tbuf =
  match (consume tbuf ttype) with
  | None -> raise (expect_error descrip tbuf)
  | Some tok -> tok

(** Parse a given token type without data, returning only location *)
let tok_only ttype tbuf =
  (tok_val ttype (string_of_ttype ttype) tbuf).loc

(** Parse unqualified lowercase name. Takes a description string from context
    so errors can say what the value is for. *)
let uqname descrip tbuf =
  let tok = tok_val (LC_IDENT "") descrip tbuf in
  (tok_sval tok, tok.loc)

let qname descrip tbuf =
  let name1 = tok_val (LC_IDENT "") ("module name or " ^ descrip) tbuf in
  match (peek tbuf).ttype with
  | DCOLON ->
    let _ = tok_only DCOLON tbuf in
    let name2 = tok_val (LC_IDENT "") descrip tbuf in
    (tok_sval name1, tok_sval name2, make_location name1.loc name2.loc)
  | _ ->
    ("", tok_sval name1, name1.loc)

let typename tbuf =
  let tok = tok_val (UC_IDENT "") "class name" tbuf in
  (tok_sval tok, tok.loc)

(* finish me! or is it already done in typeexps. Anyway need generics *)
(* let qtypename tbuf = *)
(*   match (peek tbuf).ttype with *)
(*   | LC_IDENT _ -> (\* actually could be typevar *\)  *)
(*     let mname = tok_val (LC_IDENT "") ("module name ") tbuf in *)
(*     let _ = tok_only DCOLON tbuf in *)
(*     let tname = tok_val (UC_IDENT "") ("type name ") tbuf in *)

let iconst tbuf =
  let tok = tok_val (I_LIT Int64.zero) "integer constant" tbuf in
  (tok_ival tok, tok.loc)
                
let fconst tbuf =
  let tok = tok_val (F_LIT 0.0) "float constant" tbuf
  in (tok_fval tok, tok.loc)

let bconst tbuf =
  let tok = tok_val (B_LIT '@') "byte constant" tbuf
  in (tok_cval tok, tok.loc)

let sconst tbuf =
  let tok = tok_val (S_LIT "") "string constant" tbuf
  in (tok_sval tok, tok.loc)

(** Convert a token to its operator type *)
let binop_tok: (Parser.token -> binary_op) = function
  | PLUS -> OpPlus
  | MINUS -> OpMinus
  | TIMES -> OpTimes
  | DIV -> OpDiv
  | MOD -> OpMod
  | AMP -> OpBitAnd
  | PIPE -> OpBitOr
  | CARAT -> OpBitXor
  | SHL -> OpShl
  | SHR -> OpShr
  | AND -> OpAnd
  | OR -> OpOr
  | EQ -> OpEq
  | NE -> OpNe
  | LT -> OpLt
  | LE -> OpLe
  | GT -> OpGt
  | GE -> OpGe
  | _ -> failwith "BUG: Token does not correspond do a binary operator"
  
let binop_prec = function
  | OpTimes | OpDiv | OpMod -> 1
  | OpPlus | OpMinus -> 2
  | OpShl | OpShr -> 3
  | OpBitAnd -> 4   (* Break with C, put these higher than comparison *)
  | OpBitXor -> 5
  | OpBitOr -> 6
  | OpLt | OpLe | OpGt | OpGe -> 7
  | OpEq | OpNe -> 8
  | OpAnd -> 9
  | OpOr -> 10


(* ---- end of single-token parsers ---- *)

(** typeExpr doesn't return separate location, it's in the struct. *)
let typeExpr tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  (* Can't just do "qtypename" because an lc_ident could be a type
     variable also. *)
  | LC_IDENT _ ->
    (* maybe move this out to qualTypename or just typename? *)
    let (n1, _) = uqname "module name or type variable" tbuf in
    (match (peek tbuf).ttype with
     | DCOLON ->
       ignore (tok_only DCOLON tbuf);
       let (cn, el1) = typename tbuf in
       (* TODO: parse type args/nullable/array markers *)
       { texpkind=(
            Concrete {
              modname=n1; classname=cn;
              typeargs=[];
            });
           (* nullable becomes 'option' class in analysis? *)
           nullable=false; array=false;
           loc=make_location stok.loc el1
       }
     | _ -> failwith "todo: type var parsing"
    )
  | UC_IDENT _ -> 
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

(** Void typeExpr for when it's implicit.
    Still want to think about removing this from AST too. *)
let voidTypeExpr loc =
  { texpkind = (Concrete {
        modname = "";
        classname = "Void";
        typeargs = [] });
    nullable = false;
    array = false;
    loc = loc
  }


(** Parse a token for a literal and extract its value for an ExpLiteral. *)
let literal_val tbuf =
  match (peek tbuf).ttype with
  | I_LIT _ -> 
    let (n, tloc) = iconst tbuf in (IntVal n, tloc)
  | F_LIT _ ->
    let (x, tloc) = fconst tbuf in (FloatVal x, tloc)
  | B_LIT _ ->
    let (c, tloc) = bconst tbuf in (ByteVal c, tloc)
  | S_LIT _ ->
    let (s, tloc) = sconst tbuf in (StringVal s, tloc)
  | TRUE ->
    let tloc = tok_only TRUE tbuf in (BoolVal true, tloc)
  | FALSE ->
    let tloc = tok_only FALSE tbuf in (BoolVal false, tloc)
  | NULL ->
    let tloc = tok_only NULL tbuf in (NullVal, tloc)
  | _ -> failwith "BUG: literal_val called with wrong token type"

let unop_val tbuf =
  match (peek tbuf).ttype with
  | MINUS ->
    let tloc = tok_only MINUS tbuf in (OpNeg, tloc)
  | BANG ->
    let tloc = tok_only BANG tbuf in (OpNot, tloc)
  | TILDE ->
    let tloc = tok_only TILDE tbuf in (OpBitNot, tloc)
  | _ -> failwith "BUG: unop_val called with wrong token type"


let rec expr tbuf =
  (* oh wait! record exps don't work with operators. Do I need to
     catch that here? Nah. *)
  (* Get a single expression, then look for operators, and finally
     compute precedence *)
  let rec base_expr () = 
    match (peek tbuf).ttype with
    | LPAREN ->
      let sloc = tok_only LPAREN tbuf in
      let e = expr tbuf in (* exprs already have location *)
      let eloc = tok_only RPAREN tbuf in
      { e=e.e; decor=make_location sloc eloc }
    | I_LIT _ | F_LIT _ | B_LIT _ | S_LIT _ | TRUE | FALSE | NULL ->
      let (v, tloc) = literal_val tbuf in
      { e=ExpLiteral v; decor=make_location tloc tloc }
    | MINUS | BANG | TILDE ->
      let oper, sloc = unop_val tbuf in 
      let e = base_expr () in
      { e=ExpUnop (oper, e); decor=make_location sloc e.decor }
    | LSQRB ->
      let sloc = tok_only LSQRB tbuf in
      let rec seq_loop () =
        (* Revisit: should an empty sequence be allowed? *)
        let e = expr tbuf in
        match (peek tbuf).ttype with
        | COMMA ->
          let _ = tok_only COMMA tbuf in e :: (seq_loop ())
        | _ -> [e]
      in
      let seq = seq_loop () in
      let eloc = tok_only RSQRB tbuf in
      { e=ExpSeq seq; decor=make_location sloc eloc }
    | LBRACE ->
      let sloc = tok_only LBRACE tbuf in
      let rec record_loop () =
        let fname, _ = uqname "field name" tbuf in
        let _ = tok_only ASSIGN tbuf in
        let fexp = expr tbuf in
        match (peek tbuf).ttype with
        | COMMA ->
          let _ = tok_only COMMA tbuf in (fname, fexp) :: (record_loop ())
        | _ -> [(fname, fexp)]
      in
      let fields = record_loop() in
      let eloc = tok_only RBRACE tbuf in
      { e=ExpRecord fields; decor=make_location sloc eloc }
    | VLABEL _ -> variant_exp tbuf
    | _ -> var_or_call_expr tbuf
  in
  let e1 = base_expr () in
  let rec oper_tail () = 
    match (peek tbuf).ttype with
    | PLUS | MINUS | TIMES | DIV | MOD | AND | OR | AMP | PIPE | CARAT
    | SHL | SHR | EQ | NE | LT | LE | GT | GE ->
      let optok = consume_any tbuf in
      let oper = binop_tok optok.ttype in
      let e = base_expr () in
      (oper, e) :: (oper_tail ())
    | _ -> []
  in
  let tail = oper_tail () in
  if tail = [] then e1
  else
    let opers, exprs = List.split tail in
    expr_tree (e1 :: exprs) opers

and variant_exp tbuf =
  let lbltok = tok_val (VLABEL "") "variant label" tbuf in
  match (peek tbuf).ttype with
  | LPAREN ->
    let _ = tok_only LPAREN tbuf in
    let rec varvals_loop () =
      let e = expr tbuf in
      match (peek tbuf).ttype with
      | COMMA -> e :: (varvals_loop ())
      | _ -> [e]
    in
    let varvals = varvals_loop() in
    let eloc = tok_only RPAREN tbuf in 
    { e=ExpVariant(tok_sval lbltok, varvals);
      decor=make_location lbltok.loc eloc }
  | _ ->
    { e=ExpVariant(tok_sval lbltok, []); decor=lbltok.loc }

(** Generate an expression tree from lists, based on precedence *)
and expr_tree elist oplist =
  let rec max_prec maxi max li ri =
    if li = ri then maxi
    else
      let prec = binop_prec (List.nth oplist li) in
      if prec >= max   (* greater or equal to find rightmost max *)
      then max_prec li prec (li+1) ri
      else max_prec maxi max (li+1) ri
  in
  let rec build li ri =
    if li = ri then List.nth elist li
    (* if li = ri-1 then
      let e1, e2 = List.nth elist li, List.nth elist ri in
      { e=ExpBinop(e1, List.nth oplist li, e2);
        decor=make_location e1.decor e2.decor } *)
    else
      let maxi = max_prec 0 0 li ri in
      let e1, e2 = build li maxi, build (maxi+1) ri in
      { e=ExpBinop(e1, List.nth oplist maxi, e2);
        decor=make_location e1.decor e2.decor }
  in
  build 0 (List.length oplist)
        
             
(* and operTail tbuf = (\* look for operators following *\) *)
(** Parse a string with idents and see if it's a varexpr or callexpr later *)
(* something with a call in it can still be a varexpr but not lvalue. *)
and var_or_call_expr tbuf =
  let mname, id, sloc = qname "identifier" tbuf in
  let qident = if mname = "" then id else mname ^ "::" ^ id in
  match (peek tbuf).ttype with
  | LPAREN -> (* CallExpr *)
    let _ = tok_only LPAREN tbuf in
    let args = arg_list tbuf in
    let eloc = tok_only RPAREN tbuf in
    { e=ExpCall (qident, args);
      decor=make_location sloc eloc}
  | _ -> (* loop for varexpr tail (starting with possible indexes) *)
    let ix1, eloc =
      if (peek tbuf).ttype = LSQRB then
        index_exprs tbuf
      else ([], sloc)
    in
    let rec ve_tail eloc =
      match (peek tbuf).ttype with
      | DOT ->
        let ident, eloc = uqname "field identifier" tbuf in
        let ixs, eloc =
          if (peek tbuf).ttype = LSQRB then
            index_exprs tbuf
          else ([], eloc)
        in
        let rest, eloc = ve_tail eloc in 
        ((ident, ixs)::rest, eloc)
      | _ -> ([], eloc)
    in
    let fields, eloc = ve_tail eloc in
    { e=ExpVar ((qident, ix1), fields);
      decor=make_location sloc eloc }

(** Sequence of square-bracketed index expressions *)
and index_exprs tbuf =
  let sloc = tok_only LSQRB tbuf in
  let rec loop () = 
    let iexpr = expr tbuf in
    let eloc = tok_only RSQRB tbuf in
    match (peek tbuf).ttype with
    | LSQRB ->
      let _ = tok_only LSQRB tbuf in
      let tail, eloc = loop () in
      (iexpr::tail, make_location sloc eloc)
    | _ -> ([iexpr], make_location sloc eloc)
  in loop ()
  
(** List of arguments to a function call. *)
and arg_list tbuf =
  (* Don't need overall location, each expr has its own *)
  let rec loop () =
    if (peek tbuf).ttype = RPAREN then []
    else
      let mutmark = match (peek tbuf).ttype with
        | DOLLAR -> (ignore (tok_only DOLLAR tbuf); true)
        | _ -> false
      in          
      let e = expr tbuf in
      if (peek tbuf).ttype = COMMA then
         let rest = loop () in
         ((mutmark, e)::rest)
      else
        [(mutmark, e)]
  in
  loop ()

(* ------------------- Statement parsers ------------------- *)

(* if initializer is required, the caller will check; this rule is used
   for both globals and locals that may not require initializers. *)
let rec decl_stmt tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  | VAR -> 
    let sloc = tok_only VAR tbuf in
    let (vname, _) = uqname "lvalue" tbuf in
    let tyopt = 
      (match (peek tbuf).ttype with
       | COLON ->  (* has type expression *)
         ignore (tok_only COLON tbuf);
         Some (typeExpr tbuf)
       | _ -> None
      ) in
    let initopt =
      match (peek tbuf).ttype with
      | ASSIGN ->
        let _ = tok_only ASSIGN tbuf in
        Some (expr tbuf)
      | _ -> None
    in
    let eloc = tok_only SEMI tbuf in
    { st=StmtDecl (vname, tyopt, initopt);
      decor=make_location sloc eloc }
  | _ -> failwith "decl_stmt invalid state"

and if_stmt tbuf =
  let sloc = tok_only IF tbuf in
  let cond = expr tbuf in
  let _ = tok_only THEN tbuf in
  let then_block = stmt_seq tbuf in
  let elsif_blocks = match (peek tbuf).ttype with
    | ELSIF ->
      let rec elsif_loop () =
        (* have to do (optional) else in here too? *)
        let _ = tok_only ELSIF tbuf in
        let cond = expr tbuf in
        let _ = tok_only THEN tbuf in
        let block = stmt_seq tbuf in
        match (peek tbuf).ttype with
        | ELSIF -> (cond, block) :: (elsif_loop ())
        | _ -> [(cond, block)]
      in elsif_loop ()
    | _ -> []
  in
  let elseopt = match (peek tbuf).ttype with
    | ELSE ->
      let _ = tok_only ELSE tbuf in
      let else_block = stmt_seq tbuf in
      Some else_block
    | _ -> None
  in
  let eloc = tok_only ENDIF tbuf in
  { st=StmtIf (cond, then_block, elsif_blocks, elseopt);
    decor=make_location sloc eloc }

and while_stmt tbuf =
  let sloc = tok_only WHILE tbuf in
  let cond = expr tbuf in
  let _ = tok_only DO tbuf in
  let body = stmt_seq tbuf in
  let eloc = tok_only ENDWHILE tbuf in
  { st=StmtWhile (cond, body); decor=make_location sloc eloc }

and case_stmt tbuf =
  let sloc = tok_only CASE tbuf in
  let matchexp = expr tbuf in
  let caseblocks =
    let rec case_loop () =
      let _ = tok_only OF tbuf in
      let patexp = expr tbuf in
      let _ = tok_only THEN tbuf in
      let body = stmt_seq tbuf in
      match (peek tbuf).ttype with
      | OF -> (patexp, body) :: (case_loop ())
      | _ -> [(patexp, body)]
    in case_loop()
  in
  let elseopt = match (peek tbuf).ttype with
    | ELSE ->
      let _ = tok_only ELSE tbuf in
      Some (stmt_seq tbuf)
    | _ -> None
  in 
  let eloc = tok_only ENDCASE tbuf in
  { st=StmtCase (matchexp, caseblocks, elseopt);
    decor=make_location sloc eloc }

and nop_stmt tbuf =
  let sloc = tok_only NOP tbuf in
  let eloc = tok_only SEMI tbuf in
  { st=StmtNop; decor=make_location sloc eloc }

and call_stmt tbuf =
  let e = expr tbuf in
  match e.e with
  | ExpCall _ ->
    let eloc = tok_only SEMI tbuf in
    { st=StmtCall e; decor=(make_location e.decor eloc) }
  | _ ->
    raise (parse_error "Expression cannot serve as a statement" tbuf)

(** Both call and assign statement start with an expression *)
and call_or_assign_stmt tbuf =
  let e = expr tbuf in
  match (peek tbuf).ttype with
  | ASSIGN ->
    (match e.e with
     (* Lvalues are somewhat defined syntactically by the AST: only var_expr. *)
     | ExpVar vexp -> 
       let _ = tok_only ASSIGN tbuf in
       let rvalue = expr tbuf in
       let eloc = tok_only SEMI tbuf in
       { st=StmtAssign (vexp, rvalue); decor=make_location e.decor eloc }
     | _ -> raise (parse_error "This expression type cannot be assigned to" tbuf)
    )
  | SEMI ->
    (match e.e with
     (* Then I could have had StmtCall be just name and args too, not expr *)
     | ExpCall _ ->
       let eloc = tok_only SEMI tbuf in
       { st=StmtCall e; decor=make_location e.decor eloc }
     | _ ->
       raise (parse_error "Expression cannot serve as a statement" tbuf)
    )
  | _ -> raise (unexpect_error tbuf)
       
and return_stmt tbuf =
  let sloc = tok_only RETURN tbuf in
  match (peek tbuf).ttype with
  | SEMI ->
    let eloc = tok_only SEMI tbuf in
    { st=StmtReturn None; decor=make_location sloc eloc }
  | _ ->
    let retexp = expr tbuf in
    let eloc = tok_only SEMI tbuf in
    { st=StmtReturn (Some retexp); decor=make_location sloc eloc }

(** At least one statement, possibly more *)
and stmt_seq tbuf =
  let rec loop () =
    let st = stmt tbuf in
    match (peek tbuf).ttype with
    | ELSE | ELSIF | ENDIF | ENDCASE | ENDPROC | ENDTYPE | ENDWHILE -> [st]
    | _ -> st :: (loop ())
  in
  loop ()

and stmt tbuf =
  match (peek tbuf).ttype with
  | VAR -> decl_stmt tbuf (* | REF *)
  | IF -> if_stmt tbuf
  | WHILE -> while_stmt tbuf
  | CASE -> case_stmt tbuf
  | RETURN -> return_stmt tbuf 
  | NOP -> nop_stmt tbuf
  (* | LC_IDENT _ -> call_stmt tbuf (* call_or_assign *) *)
  | _ -> call_or_assign_stmt tbuf

(* ------------------------ top-level parsers ------------------------ *)

(** Parse a single import statement or nothing. *)
let import tbuf =
  print_string "* import...\n";
  let stok = peek tbuf in
  match stok.ttype with
  | IMPORT ->
    let sloc = tok_only IMPORT tbuf in
    let (mname, _) = uqname "module name" tbuf in
    print_string mname;
    let alias = match (peek tbuf).ttype with
      | AS ->
        let _ = tok_only AS tbuf in
        let (malias, _) = uqname "module alias" tbuf in
        Some malias
      | _ -> None
    in
    let eloc = tok_only SEMI tbuf in
    (make_located (Import (mname, alias)) sloc eloc)
  | OPEN ->
    let sloc = tok_only OPEN tbuf in
    let (mname, _) = uqname "module name" tbuf in 
    let eloc = tok_only SEMI tbuf in 
    (make_located (Open mname) sloc eloc)
  | _ -> failwith "BUG: import called with non-import token"


let typedef_body tbuf = 
  let _ = tok_only IS tbuf in
  (* oh, have to look for "rec" too *)
  match (peek tbuf).ttype with
  | STRUCT ->
    let _ = tok_only STRUCT tbuf in
    let rec fields_loop () =
      let fpriv = match (peek tbuf).ttype with
        | PRIVATE -> ignore (tok_only PRIVATE tbuf); true
        | _ -> false
      in
      let fmut = match (peek tbuf).ttype with
        | MUT -> ignore (tok_only MUT tbuf); true
        | _ -> false
      in
      let fname, floc = uqname "field name" tbuf in
      let _ = tok_only COLON tbuf in
      let ftype = typeExpr tbuf in
      let finfo = { fieldname=fname; priv=fpriv; mut=fmut; fieldtype=ftype;
                    decor=make_location floc ftype.loc} in
      match (peek tbuf).ttype with
      | COMMA -> finfo :: (fields_loop ())
      | _ -> [finfo]
    in fields_loop()
  | VARIANT -> failwith "in progress" (* will return "kindinfo" when done *)
  | UC_IDENT _ -> failwith "in progress" (* newtype *)
  | _ -> raise (parse_error ("expected type or type kind specifier, found " ^
                string_of_token (peek tbuf).ttype) tbuf)

let typedef tbuf =
  let (vis, sloc) = match (peek tbuf).ttype with
    | OPAQUE ->
      let sloc = tok_only OPAQUE tbuf in
      let _ = tok_only TYPE tbuf in
      (Opaque, sloc)
    | PRIVATE ->
      let sloc = tok_only PRIVATE tbuf in
      let _ = tok_only TYPE tbuf in
      (Private, sloc)
    | _ ->
      let sloc = tok_only TYPE tbuf in
      (Open, sloc)
  in
  (* todo: type variables for generics *)
  let tname, _ = typename tbuf in
  let fields = typedef_body tbuf in
  let _ = tok_only SEMI tbuf in
  let eloc = tok_only ENDTYPE tbuf in
  { typename=tname;
    rectype=false;
    typeparams=[];
    kindinfo = Fields fields;
    visibility = vis;
    decor = make_location sloc eloc
  }

(** Type declaration and possible definition for modspec. *)
let type_decl tbuf = 
  (* Private types don't exist in modspecs, and Opaque is shown by having no body *)
  let sloc = tok_only TYPE tbuf in
  let tname, _ = typename tbuf in
  match (peek tbuf).ttype with
  | SEMI -> (* opaque type *)
    let eloc = tok_only SEMI tbuf in
    { typename=tname;
      rectype=false;
      typeparams=[];
      kindinfo=Hidden;
      visibility=Opaque;
      decor=make_location sloc eloc
    }
  | IS ->
    let fields = typedef_body tbuf in
    let _ = tok_only SEMI tbuf in
    let eloc = tok_only ENDTYPE tbuf in
    { typename=tname;
      rectype=false;
      typeparams=[];
      kindinfo=Fields fields;
      visibility=Open;
      decor=make_location sloc eloc
    }
  | _ -> raise (unexpect_error tbuf)
           
let param_info tbuf =
  let sloc = (peek tbuf).loc in
  let mutmark = match (peek tbuf).ttype with
    | DOLLAR ->
      ignore (tok_only DOLLAR tbuf); true
    | _ -> false
  in
  let (varname, _) = uqname "parameter name" tbuf in
  let _ = tok_only COLON tbuf in
  let texp = typeExpr tbuf in
  ((mutmark, varname, texp), make_location sloc texp.loc)
  
let param_list tbuf =
  separated_list_of param_info COMMA RPAREN tbuf

let visibility tbuf =
  let stok = peek tbuf in
  let vis: visibility = match stok.ttype with
    | PRIVATE -> let _ = tok_only PRIVATE tbuf in Private 
    | _ -> Public
  in 
  (vis, stok.loc)

let proc_header tbuf = 
  let vis, sloc = visibility tbuf in 
  let _ = tok_only PROC tbuf in
  let (pname, _) = uqname "procedure name" tbuf in
  (* TODO: generic params *)
  let _ = tok_only LPAREN tbuf in
  let (params, _) = param_list tbuf in 
  let eloc = tok_only RPAREN tbuf in
  let rettype = match (peek tbuf).ttype with
    | ARROW ->
      let _ = tok_only ARROW tbuf in
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
  let decl = proc_header tbuf in
  let _ = tok_only DO tbuf in
  let stmts = stmt_seq tbuf in
  let eloc = tok_only ENDPROC tbuf in
  { decl=decl; body=stmts; decor=make_location decl.decor eloc }
      
let module_body mname tbuf =
  (* I can make imports come first, yay. *)
  let imports =
    let rec imploop () =
      match (peek tbuf).ttype with
      | IMPORT | OPEN ->
        (* must be sure the statement is parsed first or infinite loop! *)
        let istmt = import tbuf in istmt :: (imploop ())
      | _ -> []
    in imploop ()
  in
  let typedefs =
    let rec typedefs_loop () =
      if (peek tbuf).ttype = TYPE || (peek2 tbuf).ttype = TYPE then
        let ty = typedef tbuf in
        ty :: (typedefs_loop ())
      else []
    in typedefs_loop ()
  in 
  let globals =
    let rec globals_loop () =
      if (peek tbuf).ttype = VAR || (peek2 tbuf).ttype = VAR then
        let vis: visibility = match (peek tbuf).ttype with
          | PRIVATE -> Private
          | _ -> Public in
        let gdecl = match decl_stmt tbuf with
          | { st=StmtDecl (vname, tyexp, init); decor=stloc } ->
            { visibility=vis; varname=vname; typeexp=tyexp;
              init=init; decor=stloc }
          | _ -> failwith "BUG: didn't get StmtDecl for global statement"
        in gdecl :: (globals_loop ())
      else []
    in globals_loop ()
  in 
  let procs =
    let rec procloop () =
      if (peek tbuf).ttype = PROC || (peek2 tbuf).ttype = PROC then
        let p = proc tbuf in p :: (procloop ())
      else []
    in procloop ()
  in
  { name = mname;
    imports = imports;
    typedefs = typedefs;
    globals = globals;
    procs = procs;
  }

(** Separate parser for global variable decl in a modspec only. *)
let global_decl tbuf = 
    let sloc = tok_only VAR tbuf in
    let (vname, _) = uqname "global variable name" tbuf in
    let ty = 
      (match (peek tbuf).ttype with
       | COLON ->  (* has type expression *)
         ignore (tok_only COLON tbuf);
         typeExpr tbuf
       | _ -> (* give more detailed error message *)
         raise (parse_error ("(modspec): Global variable declaration must "
                             ^ "include a type annotation") tbuf)
      ) in
    let eloc = tok_only SEMI tbuf in
    { varname=vname; typeexp=ty; decor=make_location sloc eloc }
    
let modspec tbuf = 
  let _ = tok_only MODSPEC tbuf in
  let (mname, _) = uqname "module name" tbuf in
  let _ = tok_only IS tbuf in
  let requires =
    let rec requires_loop () =
      if (peek tbuf).ttype = REQUIRE then
        let sloc = tok_only REQUIRE tbuf in
        let (req, _) = uqname "module name" tbuf in
        let eloc = tok_only SEMI tbuf in
        (make_located req sloc eloc)::(requires_loop ())
      else []
    in requires_loop() in
  let typedefs =
    let rec typedecls_loop () = 
      if (peek tbuf).ttype = TYPE then  (* no qualifier *)
        (type_decl tbuf)::(typedecls_loop ())
      else []
    in typedecls_loop () in
  let globals =
    let rec globals_loop () =
      if (peek tbuf).ttype = VAR then
        let gd = global_decl tbuf in gd :: (globals_loop ())
      else []
    in globals_loop () in
  let procdecls =
    let rec procs_loop () =
      if (peek tbuf).ttype = PROC || (peek2 tbuf).ttype = PROC then
        let ph = proc_header tbuf in
        let _ = tok_only SEMI tbuf in
        ph :: (procs_loop ())
      else []
    in procs_loop () in
  { name=mname;
    alias=mname;  (* replaced at higher level *)
    requires=requires;
    typedefs=typedefs;
    globals=globals;
    procdecls=procdecls
  }
  
let dill_source tbuf =
  let stok = peek tbuf in
  match stok.ttype with
  | MODULE ->
    let _ (* spos *) = tok_only MODULE tbuf in
    let (mname, _) = uqname "module name" tbuf in
    let _ = tok_only IS tbuf in 
    let the_module = module_body mname tbuf in
    let _ (* epos *) = tok_only ENDMODULE tbuf in
    [the_module]
  (* Thought: allowing top-level code makes it unclear if signatures are
     to be placed "outside"? No it doesn't! *)
  (* need to get location from returned body. *)
  | _ -> [module_body "" tbuf] 

(* for testing the lexer and token buffer. Any sequence of valid tokens. *)
let rec any_tokens buf =
  match (consume_any buf).ttype with 
  | I_LIT i -> print_string ("(I_LIT " ^ Int64.to_string i ^ ") ");
    any_tokens buf
  | F_LIT x -> print_string ("(F_LIT " ^ string_of_float x ^ ") ");
    any_tokens buf
  | B_LIT c -> print_string ("(B_LIT '" ^ Char.escaped c ^ "') ");
    any_tokens buf
  | S_LIT s -> print_string ("(S_LIT \"" ^ String.escaped s ^ "\") ");
    any_tokens buf
  | LC_IDENT s -> print_string ("(LC_IDENT " ^ s ^ ") "); any_tokens buf
  | UC_IDENT s -> print_string ("(UC_IDENT " ^ s ^ ") "); any_tokens buf
  | EOF -> print_string "EOF\n "; (* don't recurse *)
  | _ -> print_string "token "; any_tokens buf

(* top-level testing code *)
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
  let modules = dill_source tbuf in
  print_string ("Parsed " ^ string_of_int (List.length modules)
                ^ " module(s).\n");
  print_string (String.concat "\n" (List.map module_to_string modules))
