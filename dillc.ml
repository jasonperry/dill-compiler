(** Top-level module of the Dill compiler. *)
open Common
open Ast
open Pervasives


(** Record for compiler configuration settings. *)
type dillc_config = {
    include_paths : string list
  }


(** Format two Lexing.location objects as a string showing the range. *)
(* Maybe put this in a common thing too. *)
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
(* Is this only used here at the top level? Should it go in common? *)
let format_errors elist =
  let format1 {loc; value} =
    (* TODO: distinguish between error and warning. *)
    "Error: " ^ format_loc (fst loc) (snd loc) ^ ":\n    " ^ value
  in
  (* errors append at beginning, so need to reverse the list. *)
  let errstrs = List.rev_map format1 elist in
  String.concat "\n" errstrs ^ "\n"


(** Lex and parse an open source or header file, returning the AST
 *  with location decoration *)
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


(** Do analysis and codegen phases, return module code and header object *)
let process_module ispecs (parsedmod: (locinfo, locinfo) dillmodule) = 
  let open Symtable1 in
  (* populate top-level symbol table. *)
  let topsyms : Llvm.llvalue st_node = pervasive_syms () in
  let modsyms = Symtable.new_scope topsyms in
  (* Maybe get headers from the AST here,
   ( so the analyzer doesn't have to call back out. *)
  let analyzedmod = Analyzer.check_module modsyms base_tenv ispecs parsedmod in
  match analyzedmod with
  | Error errs -> Error errs
  | Ok themod ->
     (* print_string (module_to_string themod); *)
     let modcode = Codegen.gen_module base_tenv modsyms themod in
     let header = Analyzer.create_module_spec themod in
     Ok (modcode, header)


(** Write a module and its header out to disk *)
let write_module dir (modcode, header) = 
  let headername = String.lowercase_ascii header.name in
  let headerfile = open_out (dir ^ "/" ^ headername ^ ".dms") in
  output_string headerfile (modspec_to_string header);
  close_out headerfile;
  Llvm.set_target_triple "x86_64-pc-linux-gnu" modcode;
  Llvm.print_module (headername ^ ".ll") modcode


(** Try to open a given filename, searching paths *)
let rec open_from_paths plist filename =
  match plist with
  | [] -> None
  | path :: rest -> 
     try
       Some (open_in (path ^ "/" ^ filename))
     with Sys_error _ ->
       open_from_paths rest filename


(** Recursively scan all modspec files and populate the map of known ones. *)
let load_imports cconfig (modmap: 'sd module_spec StrMap.t) istmts =
  let rec load_import mmap istmt =
    let modname = match istmt with
      | Using (mn, _) -> mn
      | Open mn -> mn in
    if StrMap.mem modname mmap then mmap (* already there *)
    else
      let specfilename = String.lowercase_ascii modname ^ ".dms" in
      match open_from_paths cconfig.include_paths specfilename with
      | None -> failwith ("Could not find spec file " ^ specfilename)
      | Some specfile -> (
        (* what kind of ('ed, 'sd) are they? Location, at first... *)
        match process_source specfile with
        | (Some spec, []) ->
           let newmap = StrMap.add modname spec mmap in
           List.fold_left load_import newmap spec.imports
        | (None, _) -> failwith ("No modspec found in " ^ specfilename)
        | (Some _, _) ->
           failwith ("Spec file " ^ specfilename ^ " cannot contain a module")
      )
  in 
  List.fold_left load_import modmap istmts

let () =
  let srcdir =
    if Array.length Sys.argv > 1 then Filename.dirname Sys.argv.(1)
    else "." in
  let cconfig = { include_paths = [srcdir] } in
  let infile =
    if Array.length Sys.argv > 1 then
      open_in Sys.argv.(1)
    else stdin
  in
  let (hdr, mods) = process_source infile in
  if Option.is_some hdr then
    failwith ("Module specs cannot be given on the command line "
              ^ "or in Dill source files.");
  let all_istmts = List.concat_map (
                       fun (m: ('ed, 'sd) dillmodule) -> m.imports
                     ) mods in
  let ispecs = load_imports cconfig StrMap.empty all_istmts in
  let mod_results = List.map (process_module ispecs) mods in
  if List.exists Result.is_error mod_results then (
    prerr_string (format_errors
                    (concat_errors mod_results));
    exit 1)
  else
  List.iter (write_module srcdir) (concat_ok mod_results)
