
(* "Lexing" is the runtime for ocamllex-generated lexers. *)
open Ast


(** Format two Lexing.location objects as a string showing the range. *)
let format_loc (spos: Lexing.position) (epos: Lexing.position) =
  if spos.pos_lnum = epos.pos_lnum then
    Format.sprintf "%d:%d-%d"
      spos.pos_lnum
      (spos.pos_cnum - spos.pos_bol)
      (epos.pos_cnum - epos.pos_bol)
  else 
    Format.sprintf "%d:%d-%d:%d"
      spos.pos_lnum
      (spos.pos_cnum - spos.pos_bol)
      epos.pos_lnum
      (epos.pos_cnum - epos.pos_bol)

(** Generate string buffer showing a sequence of errors. *)
let format_errors elist =
  let format1 {loc; value} =
    (* TODO: distinguish between error and warning. *)
    "Error: " ^ format_loc (fst loc) (snd loc) ^ ":\n    " ^ value
  in
  (* errors append at beginning, so need to reverse the list. *)
  let errstrs = List.rev_map format1 elist in
  String.concat "\n" errstrs ^ "\n"

(** Run as many phases as we have on one module. *)
let process_module channel =
  let buf = Lexing.from_channel channel in
  let parsedmod = try
      Parser.main Lexer.token buf
    with
    | Lexer.Error msg ->
       let spos, epos = (Lexing.lexeme_start_p buf, Lexing.lexeme_end_p buf) in
       print_string
         ("At line " ^ format_loc spos epos ^ ": lexical error:\n    "
          ^ msg ^ "\n");
       failwith "Compilation terminated at lexing."
    | Parser.Error ->
       let spos, epos = (Lexing.lexeme_start_p buf, Lexing.lexeme_end_p buf) in
       print_string
         ("At line " ^ format_loc spos epos ^ ": syntax error.\n");
       failwith "Compilation terminated at parsing." 
  in
  let open Symtable1 in 
  let analyzedmod = Analyzer.check_module
                      (* Wow, this works? *)
                      (Symtable.make_empty (): Llvm.llvalue st_node)
                      base_tenv
                      parsedmod in
  match analyzedmod with
  | Error errs -> print_string (format_errors errs)
  | Ok themod ->
    print_string (module_to_string themod)
    (* let modcode = Codegen.gen_module base_tenv themod in 
    Llvm.dump_module modcode  (* prints at top! *) *)

(* let () =
  repeat (Lexing.from_channel stdin) *)

let () =
  let infile =
    if Array.length Sys.argv > 1 then
      open_in Sys.argv.(1)
    else stdin
  in
  process_module infile
  
