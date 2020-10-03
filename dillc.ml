(** Top-level module of the Dill compiler. *)
open Common
open Ast
open Pervasives


(** Record for compiler configuration settings. *)
type dillc_config = {
    include_paths : string list;
    source_dir : string;
    parse_only : bool;
    typecheck_only : bool;
    emit_llvm : bool;
    link : bool;
    print_ast : bool;
    print_symtable : bool;
  }

let default_config = {
    include_paths = ["."];
    source_dir = ".";
    parse_only = false;
    typecheck_only = false;
    emit_llvm = false;
    link = false; (* later to be true by default *)
    print_ast = false;
    print_symtable = false;
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
let parse_sourcefile channel =
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
  (* don't need to create sub-module, analyzer does, we just start the ball *)
  (* let modsyms = Symtable.new_scope topsyms in *)
  (* We pass in the headers from the AST here,
   ( so the analyzer doesn't have to call back out. *)
  let analyzedmod = Analyzer.check_module topsyms base_tenv ispecs parsedmod in
  match analyzedmod with
  | Error errs -> Error errs
  | Ok themod ->
     print_string (module_to_string themod);
     let modcode = Codegen.gen_module base_tenv topsyms themod in
     let header = Analyzer.create_module_spec themod in
     Ok (modcode, header)

let write_header srcdir header = 
  let headerfilename =
    String.lowercase_ascii (String.sub header.name 0 1)
    ^ String.sub header.name 1 (String.length header.name - 1) in
  let headerfile = open_out (srcdir ^ "/" ^ headerfilename ^ ".dms") in
  output_string headerfile (modspec_to_string header);
  close_out headerfile

(** Write a module to disk as native code. *)
let write_module_native filename modcode =
  Llvm_all_backends.initialize (); (* was _X86 *)
  let open Llvm_target in
  let ttriple = "x86_64-pc-linux-gnu" in
  Llvm.set_target_triple ttriple modcode;
  let ttriple = Llvm.target_triple modcode in
  let target = Target.by_triple ttriple in
  let machine = Llvm_target.TargetMachine.create
                  ~triple:ttriple
                  ~cpu:"generic"
                  ~features:"" target in
  let dlstring =DataLayout.as_string
                  (TargetMachine.data_layout machine) in
  Llvm.set_data_layout dlstring modcode; 
  (* let passmgr = Llvm.PassManager.create () in (* for optim only? *) *)
  let outfilename =
    Filename.chop_extension (Filename.basename filename) ^ ".o" in
  TargetMachine.emit_to_file
    modcode
    CodeGenFileType.ObjectFile
    outfilename
    machine

(** Write a module to disk as LLVM IR text. *)
let write_module_llvm filename modcode = 
  Llvm.set_target_triple "x86_64-pc-linux-gnu" modcode;
  Llvm.print_module
    (Filename.chop_extension (Filename.basename filename) ^ ".ll") modcode


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
        match parse_sourcefile specfile with
        | (Some spec, None) ->
           let newmap = StrMap.add modname spec mmap in
           List.fold_left load_import newmap spec.imports
        | (None, _) -> failwith ("No modspec found in " ^ specfilename)
        | (Some _, _) ->
           failwith ("Spec file " ^ specfilename ^ " cannot contain a module")
      )
  in 
  List.fold_left load_import modmap istmts

let parse_cmdline args =
  let rec ploop i srcfiles config =
    if i == Array.length args then (List.rev srcfiles, config)
    else 
      match args.(i) with
      | "--print-ast" ->
         ploop (i+1) srcfiles { config with print_ast = true }
      | "--print-symtable" ->
         ploop (i+1) srcfiles { config with print_symtable = true }
      | "--parse-only" ->
         ploop (i+1) srcfiles { config with parse_only = true }
      | "--typecheck-only" ->
         ploop (i+1) srcfiles { config with typecheck_only = true }
      | "--emit-llvm" ->
         ploop (i+1) srcfiles { config with emit_llvm = true }
      | fname when (String.get fname 0) <> '-' ->
         (* really shouldn't set include path in a hacky way like this. *)
         let (ipaths, srcdir) = match Filename.dirname fname with
           | "" -> (config.include_paths, config.source_dir)
           | srcdir -> (srcdir :: config.include_paths,
                        srcdir) in
         ploop (i+1) (fname :: srcfiles)
           { config with include_paths = ipaths; source_dir = srcdir }
      | other -> failwith ("Unknown option " ^ other)
  in
  ploop 1 [] default_config

let () =
  let (srcfiles, cconfig) = parse_cmdline Sys.argv in
  (* Loop over all source file arguments, with accumulator of
   * interfaces that are loaded. *)
  let process_sourcefile ispecs srcfilename =
    let infile = open_in srcfilename in
    let (specopt, modopt) = parse_sourcefile infile in
    if Option.is_some specopt then
      failwith ("Module specs cannot be given on the command line "
                ^ "or in Dill source files.");
    match modopt with
    | None -> failwith "No module code was parsed from input."
    | Some parsedmod ->
       if cconfig.parse_only then (
         print_string (module_to_string parsedmod);
         ispecs
       )
       else (
         let ispecs = load_imports cconfig ispecs parsedmod.imports in
         match process_module ispecs parsedmod with
         | Error errs -> 
            prerr_string (format_errors errs);
            exit 1
         | Ok (modcode, header) ->
            (* print_string (st_node_to_string topsyms); *)
            write_header cconfig.source_dir header;
            if cconfig.emit_llvm then (
              print_endline ("Writing module : " ^ srcfilename);
              write_module_llvm srcfilename modcode )
            else 
              write_module_native srcfilename modcode
            ;
            ispecs
       )
  in
  List.iter print_endline srcfiles;
  ignore (List.fold_left process_sourcefile StrMap.empty srcfiles)
