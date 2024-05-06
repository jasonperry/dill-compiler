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

(** Consume token of given type, with error message if not *)
let get_tok ttype descrip tbuf =
  match (consume tbuf ttype) with
  | None -> raise (expect_error descrip tbuf)
  | Some tok -> tok

(** Parse a given token type without data, returning only location *)
let parse_tok ttype tbuf =
  (get_tok ttype (string_of_ttype ttype) tbuf).loc

let iconst tbuf =
  let tok = get_tok (I_LIT Int64.zero) "integer constant" tbuf in
  (tok_ival tok, tok.loc)
                
let fconst tbuf =
  let tok = get_tok (F_LIT 0.0) "float constant" tbuf
  in (tok_fval tok, tok.loc)

let bconst tbuf =
  let tok = get_tok (B_LIT '@') "byte constant" tbuf
  in (tok_cval tok, tok.loc)

let sconst tbuf =
  let tok = get_tok (S_LIT "") "string constant" tbuf
  in (tok_sval tok, tok.loc)

(** Convert a token to its operator type *)
let binop_tok = function
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

(** Parse unqualified lowercase name. Takes a description string from context
    so errors can say what the value is for. *)
let uqname descrip tbuf =
  let tok = get_tok (LC_IDENT "") descrip tbuf in
  (tok_sval tok, tok.loc)

let qname descrip tbuf =
  let name1 = get_tok (LC_IDENT "") ("module name or " ^ descrip) tbuf in
  match (peek tbuf).ttype with
  | DCOLON ->
    let _ = parse_tok DCOLON tbuf in
    let name2 = get_tok (LC_IDENT "") descrip tbuf in
    (tok_sval name1, tok_sval name2, make_location name1.loc name2.loc)
  | _ ->
    ("", tok_sval name1, name1.loc)

(* possibly qualified? *)
let typename tbuf =
  let tok = get_tok (UC_IDENT "") "class name" tbuf in
  (tok_sval tok, tok.loc)

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


(** Parse a string with idents and see if it's a varexpr or callexpr later *)
(* something with a call in it can still be a varexpr but not lvalue. *)
let rec var_or_call_expr tbuf =
  let mname, id, sloc = qname "identifier" tbuf in
  let qident = if mname = "" then id else mname ^ "::" ^ id in
  match (peek tbuf).ttype with
  | LPAREN -> (* CallExpr *)
    let _ = parse_tok LPAREN tbuf in
    let args = arg_list tbuf in
    let eloc = parse_tok RPAREN tbuf in
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
  let sloc = parse_tok LSQRB tbuf in
  let rec loop () = 
    let iexpr = expr tbuf in
    let eloc = parse_tok RSQRB tbuf in
    match (peek tbuf).ttype with
    | LSQRB ->
      let _ = parse_tok LSQRB tbuf in
      let tail, eloc = loop () in
      (iexpr::tail, make_location sloc eloc)
    | _ -> ([iexpr], make_location sloc eloc)
  in loop ()
  
     
and expr tbuf =
  (* Get a single expression, then look for operators, and finally
     compute precedence *)
  let rec base_expr () = 
    match (peek tbuf).ttype with
    | LPAREN ->
      let sloc = parse_tok LPAREN tbuf in
      let e = expr tbuf in (* exprs already have location *)
      let eloc = parse_tok RPAREN tbuf in
      { e=e.e; decor=make_location sloc eloc }
    | I_LIT _ ->
      let (n, tloc) = iconst tbuf in
      { e=ExpLiteral (IntVal n); decor=make_location tloc tloc }
    | F_LIT _ ->
      let (x, tloc) = fconst tbuf in
      { e=ExpLiteral (FloatVal x); decor=make_location tloc tloc }
    | B_LIT _ ->
      let (c, tloc) = bconst tbuf in
      { e=ExpLiteral (ByteVal c); decor=make_location tloc tloc }
    | S_LIT _ ->
      let (s, tloc) = sconst tbuf in
      { e=ExpLiteral (StringVal s); decor=make_location tloc tloc }
    | TRUE ->
      let tloc = parse_tok TRUE tbuf in
      { e=ExpLiteral (BoolVal true); decor=make_location tloc tloc }
    | FALSE ->
      let tloc = parse_tok FALSE tbuf in
      { e=ExpLiteral (BoolVal false); decor=make_location tloc tloc }
    | NULL ->
      let tloc = parse_tok NULL tbuf in
      { e=ExpLiteral NullVal; decor=make_location tloc tloc }
    | MINUS ->
      let sloc = parse_tok MINUS tbuf in
      let e = base_expr () in
      { e=ExpUnop (OpNeg, e); decor=make_location sloc e.decor }
    | NOT ->
      let sloc = parse_tok NOT tbuf in
      let e = base_expr () in
      { e=ExpUnop(OpNot, e); decor=make_location sloc e.decor }
    | TILDE -> (* bitwise not *)
      let sloc = parse_tok TILDE tbuf in
      let e = base_expr () in
      { e=ExpUnop(OpBitNot, e); decor=make_location sloc e.decor }
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

(*  if List.length tail = 1 then
    let oper, e2 = List.hd tail in
    { e=ExpBinop(e1, oper, e2); decor=make_location e1.decor e2.decor }
  else
    failwith "prec climbing not implemented yet" *)

(** Generate an expression tree based on precedence *)
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
        
  (* | _ -> raise (expect_error "Unknown expression token" tbuf) *)
             
(* and operTail tbuf = (\* look for operators following *\) *)

(** List of arguments to a function call. *)
and arg_list tbuf =
  (* Don't need overall location, each expr has its own *)
  let rec loop () =
    if (peek tbuf).ttype = RPAREN then []
    else
      let mutmark = match (peek tbuf).ttype with
        | DOLLAR -> (ignore (parse_tok DOLLAR tbuf); true)
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

  (* want to try multiple things in a natural way... *)
  (* Maybe I should raise errors always and catch them... *)
  (* Where do I put the logic of when I'm "committed" to parsing that type
     of thing? *)
  (* step 1: constExp vs OpExp *)
(* exp's recursive "buddies" can be different from other things *)


(* if initializer is required, the caller will check, right? *)
(* Yes, I think that's better than trying to divide syntactically. *)
and decl_stmt tbuf =
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
    { st=StmtDecl (vname, tyopt, initopt);
      decor=make_location sloc eloc }
  | _ -> failwith "decl_stmt invalid state"

and if_stmt tbuf =
  let sloc = parse_tok IF tbuf in
  let cond = expr tbuf in
  let _ = parse_tok THEN tbuf in
  let then_block = stmt_seq tbuf in
  let elsif_blocks = match (peek tbuf).ttype with
    | ELSIF ->
      let rec elsif_loop () =
        (* have to do (optional) else in here too? *)
        let _ = parse_tok ELSIF tbuf in
        let cond = expr tbuf in
        let _ = parse_tok THEN tbuf in
        let block = stmt_seq tbuf in
        match (peek tbuf).ttype with
        | ELSIF -> (cond, block) :: (elsif_loop ())
        | _ -> [(cond, block)]
      in elsif_loop ()
    | _ -> []
  in
  let elseopt = match (peek tbuf).ttype with
    | ELSE ->
      let _ = parse_tok ELSE tbuf in
      let else_block = stmt_seq tbuf in
      Some else_block
    | _ -> None
  in
  let eloc = parse_tok ENDIF tbuf in
  { st=StmtIf (cond, then_block, elsif_blocks, elseopt);
    decor=make_location sloc eloc }

and while_stmt tbuf =
  let sloc = parse_tok WHILE tbuf in
  let cond = expr tbuf in
  let _ = parse_tok LOOP tbuf in
  let body = stmt_seq tbuf in
  let eloc = parse_tok ENDWHILE tbuf in
  { st=StmtWhile (cond, body); decor=make_location sloc eloc }

and case_stmt tbuf =
  let sloc = parse_tok CASE tbuf in
  let matchexp = expr tbuf in
  let caseblocks =
    let rec case_loop () =
      let _ = parse_tok OF tbuf in
      let patexp = expr tbuf in
      let _ = parse_tok THEN tbuf in
      let body = stmt_seq tbuf in
      match (peek tbuf).ttype with
      | OF -> (patexp, body) :: (case_loop ())
      | _ -> [(patexp, body)]
    in case_loop()
  in
  let elseopt = match (peek tbuf).ttype with
    | ELSE ->
      let _ = parse_tok ELSE tbuf in
      Some (stmt_seq tbuf)
    | _ -> None
  in 
  let eloc = parse_tok ENDCASE tbuf in
  { st=StmtCase (matchexp, caseblocks, elseopt);
    decor=make_location sloc eloc }

and nop_stmt tbuf =
  let sloc = parse_tok NOP tbuf in
  let eloc = parse_tok SEMI tbuf in
  { st=StmtNop; decor=make_location sloc eloc }

and call_stmt tbuf =
  let e = expr tbuf in
  match e.e with
  | ExpCall _ ->
    let eloc = parse_tok SEMI tbuf in
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
       let _ = parse_tok ASSIGN tbuf in
       let rvalue = expr tbuf in
       let eloc = parse_tok SEMI tbuf in
       { st=StmtAssign (vexp, rvalue); decor=make_location e.decor eloc }
     | _ -> raise (parse_error "This expression type cannot be assigned to" tbuf)
    )
  | SEMI ->
    (match e.e with
     (* Then I could have had StmtCall be just name and args too, not expr *)
     | ExpCall _ ->
       let eloc = parse_tok SEMI tbuf in
       { st=StmtCall e; decor=make_location e.decor eloc }
     | _ ->
       raise (parse_error "Expression cannot serve as a statement" tbuf)
    )
  | _ -> raise (unexpect_error tbuf)
       

and return_stmt tbuf =
  let sloc = parse_tok RETURN tbuf in
  match (peek tbuf).ttype with
  | SEMI ->
    let eloc = parse_tok SEMI tbuf in
    { st=StmtReturn None; decor=make_location sloc eloc }
  | _ ->
    let retexp = expr tbuf in
    let eloc = parse_tok SEMI tbuf in
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
  
let param_list tbuf =
  separated_list_of param_info COMMA RPAREN tbuf

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
  let decl = proc_header tbuf in
  let rec stmtLoop () =
    match (peek tbuf).ttype with
    | ENDPROC -> []
    | _ -> (stmt tbuf)::(stmtLoop ())
  in
  let stmts = stmtLoop () in
  let eloc = parse_tok ENDPROC tbuf in
  { decl=decl; body=stmts; decor=make_location decl.decor eloc }
      
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
