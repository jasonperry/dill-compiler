
(* "Lexing" is the runtime for ocamllex-generated lexers. *)
open Ast
open Pervasives

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
let process_source channel =
  let buf = Lexing.from_channel channel in
  let open Lexing in 
  try
    Parser.main Lexer.token buf
  with
  | Lexer.Error msg ->
     let spos, epos = (lexeme_start_p buf, lexeme_end_p buf) in
     print_string
       ("At line " ^ format_loc spos epos ^ ": lexical error:\n    "
          ^ msg ^ "\n");
     failwith "Compilation terminated at lexing."
  | Parser.Error ->
     let spos, epos = (lexeme_start_p buf, lexeme_end_p buf) in
     print_string
       ("At line " ^ format_loc spos epos ^ ": syntax error.\n");
     failwith "Compilation terminated at parsing."

let process_module parsedmod = 
  let open Symtable1 in
  (* populate top-level symbol table. *)
  let topsyms : Llvm.llvalue st_node = pervasive_syms () in
  let analyzedmod = Analyzer.check_module topsyms base_tenv parsedmod in
  match analyzedmod with
  | Error errs -> Error errs
  | Ok themod ->
     (* print_string (module_to_string themod); *)
     let modcode = Codegen.gen_module base_tenv topsyms themod in
     let header = Analyzer.create_module_interface themod in
     Ok (modcode, header)

let write_module dir (modcode, header) = 
  let headername = String.lowercase_ascii header.name in
  let headerfile = open_out (dir ^ "/" ^ headername ^ ".dms") in
  output_string headerfile (interface_to_string header);
  close_out headerfile;
  Llvm.set_target_triple "x86_64-pc-linux-gnu" modcode;
  Llvm.print_module (headername ^ ".ll") modcode

let () =
  let infile =
    if Array.length Sys.argv > 1 then
      open_in Sys.argv.(1)
    else stdin
  in
  (* TODO: check if there are headers or mods *)
  let (_, mods) = process_source infile in
  let mod_results = List.map process_module mods in
  if List.exists Result.is_error mod_results then (
    prerr_string (format_errors
                    (Analyzer.concat_errors mod_results));
    exit 1)
  else
    let srcdir =
      if Array.length Sys.argv > 1 then Filename.dirname Sys.argv.(1)
      else "." in
  List.iter (write_module srcdir) (Analyzer.concat_ok mod_results)
