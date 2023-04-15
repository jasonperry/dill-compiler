(** Top-level module of the Dill compiler. *)
open Common
open Ast
open Llvm_scalar_opts
(* open Pervasives *)


(** Record for compiler configuration settings. *)
type dillc_config = {
    include_paths : string list;
    source_dir : string;
    parse_only : bool;
    typecheck_only : bool;
    emit_llvm : bool;
    qbe_codegen: bool;
    optimize : bool;
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
    qbe_codegen = false;
    optimize = true;
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
let format_errors filename elist =
  let format1 {loc; value} =
    (* TODO: distinguish between error and warning. *)
    "Error: " ^ filename ^ " " ^ format_loc (fst loc) (snd loc)
    ^ ":\n    " ^ value
  in
  (* errors append at beginning, so need to reverse the list. *)
  let errstrs = List.rev_map format1 elist in
  String.concat "\n" errstrs ^ "\n"


let handle_parse_errors filename buf = function
  | Lexer.Error msg ->
     let open Lexing in
     let spos, epos = (lexeme_start_p buf, lexeme_end_p buf) in
     print_endline ("Error while lexing file " ^ filename ^ ":");
     print_string
       ("  At line " ^ format_loc spos epos ^ ": lexical error:\n    "
        ^ msg ^ "\n");
     failwith "Compilation terminated at lexing."
  | Parser.Error ->
     let open Lexing in
     let spos, epos = (lexeme_start_p buf, lexeme_end_p buf) in
     print_endline ("Error while parsing file " ^ filename ^ ":");
     print_string
       ("  At line " ^ format_loc spos epos ^ ": syntax error.\n");
     failwith "Compilation terminated at parsing."
  | Syntax.SyntaxError ((spos, epos), msg) ->
    print_endline ("Error while parsing file " ^ filename ^ ":");
    print_string ("  At line " ^ format_loc spos epos ^ ": " ^ msg ^ ".\n");
    failwith "Compilation terminated at parsing."
  | _ -> failwith "Unknown error from parser."


(** Lex and parse an open source or spec file, returning the AST
 *  with location decoration *)
let parse_sourcefile channel filename =
  let buf = Lexing.from_channel channel in
  try
    Parser.modsource Lexer.token buf
  with
  | exn -> handle_parse_errors filename buf exn

let parse_modspec channel filename =
  let buf = Lexing.from_channel channel in
  try
    Parser.modspec Lexer.token buf
  with
  | exn -> handle_parse_errors filename buf exn
  

(** Try to open a given filename, searching paths *)
let rec open_from_paths plist filename =
  match plist with
  | [] -> None
  | path :: rest -> 
     try
       Some (open_in (path ^ "/" ^ filename))
     with Sys_error _ ->
       open_from_paths rest filename


(* import handling might be good to move into its own module 
 * (except the file handling) *)
(** Recursively scan all modspec files and populate the map of known ones. *)
let load_imports cconfig (modmap: ('ed,'sd,'tt) module_spec StrMap.t) istmts =
  let rec load_import mmap istmt =
    let modname = match istmt.value with
      | Using (mn, _) -> mn
      | Open mn -> mn in
    if StrMap.mem modname mmap then mmap (* already there *)
    else
      let specfilename = modname ^ ".dms" in
      match open_from_paths cconfig.include_paths specfilename with
      | None -> failwith ("Could not find spec file " ^ specfilename)
      | Some specfile ->
         let spec = parse_modspec specfile specfilename in
         let newmap = StrMap.add modname spec mmap in
         List.fold_left load_import newmap spec.imports
  in 
  List.fold_left load_import modmap istmts

(** Do analysis and codegen phases, return module code and header object *)
let analysis cconfig ispecs (parsedmod: (locinfo, locinfo, 'tt) dillmodule) = 
  let open Symtable1 in
  (* populate top-level symbol table. Formerly with pervasive_syms *)
  let topsyms : Llvm.llvalue st_node = Symtable.make_empty () in 
  (* don't need to create import or module syms, analyzer does *)
  (* We pass in the headers from the AST here,
     so the analyzer doesn't have to call back out. 
     The analyzer creates its own type environment. *)
  let ispecs = load_imports cconfig ispecs parsedmod.imports in
  match Analyzer.check_module topsyms base_tenv ispecs parsedmod with
  | Error errs -> Error (List.rev errs)
  | Ok (typed_mod, mod_tenv) ->
     if cconfig.print_symtable then
       print_string (Symtable1.st_node_to_string topsyms);
     Ok (typed_mod, mod_tenv, topsyms)


let codegen (config: dillc_config) tenv syms layout typedmod =
  (* Unused value here, just to pull in the code. *)
  let _ = if config.qbe_codegen then
      Some (Codegen_qbe.gen_module tenv syms)
    else None in
  let modcode = Codegen.gen_module tenv syms layout typedmod in
  let header = Analyzer.create_module_spec typedmod in
  modcode, header


let write_header srcdir header =
  let headerfilename =
    (*String.lowercase_ascii (String.sub header.name 0 1)
    ^ String.sub header.name 1 (String.length header.name - 1) *)
    header.name ^ ".dms" in
  let headerfile = open_out (srcdir ^ "/" ^ headerfilename) in
  output_string headerfile (modspec_to_string header);
  close_out headerfile;
  print_endline ("Wrote module spec file " ^ headerfilename)


(** Write a module to disk as native code. *)
let write_module_native filename modcode config machine =
  let open Llvm_target in
  if config.optimize then (
    let passmgr = Llvm.PassManager.create () in
    add_memory_to_register_promotion passmgr;
    add_correlated_value_propagation passmgr;
    add_cfg_simplification passmgr;
    (* add_instruction_combination passmgr; (* slowed it down! *) *)
    if Llvm.PassManager.run_module modcode passmgr then
      debug_print "Optimization passes modified module code"
    else
      debug_print "Optimization passes did NOT modify module code"
    (* TargetMachine.add_analysis_passes passmgr machine; *)
  );
  let outfilename =
    Filename.chop_extension (Filename.basename filename) ^ ".o" in
  TargetMachine.emit_to_file
    modcode
    CodeGenFileType.ObjectFile
    outfilename
    machine;
  print_endline ("Wrote object code file " ^ outfilename)

let gen_target_machine () = 
  Llvm_all_backends.initialize (); (* was _X86 *)
  let open Llvm_target in
  (* let ttriple = "x86_64-pc-linux-gnu" in *)
  let ttriple = Target.default_triple () in
  debug_print ("Generating code for machine triple: " ^ ttriple);
  let target = Target.by_triple ttriple in
  Llvm_target.TargetMachine.create
    ~triple:ttriple
    ~reloc_mode:RelocMode.PIC (* unless statically linked? *)
    (* ~cpu:"generic"
    (* got these features from the clang llvm output. *)
    ~features:"+cx8,+fxsr,+mmx,+sse,+sse2,+x87" *)
    target

  
(** Write a module to disk as LLVM IR text. *)
let write_module_llvm filename modcode =
  (* Llvm.set_target_triple "x86_64-pc-linux-gnu" modcode; *)
  let irfilename =
    Filename.chop_extension (Filename.basename filename) ^ ".ll" in
  Llvm.print_module irfilename modcode;
  print_endline ("Wrote LLVM IR code file " ^ irfilename)


let parse_cmdline args =
  let rec ploop i srcfiles config =
    if i == Array.length args then (List.rev srcfiles, config)
    else 
      match args.(i) with
      | "--debug" ->  (* debug is a "true global" *)
         _debug := true;
         ploop (i+1) srcfiles config
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
      | "-O0" ->
        ploop (i+1) srcfiles { config with optimize = false }
      | "-I" ->
         ploop (i+2) srcfiles {
             config with include_paths = args.(i+1) :: config.include_paths
           }
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
  (* Loop over all source file arguments, accumulating map of
   * modspecs that are loaded. *)
  let process_sourcefile ispecs srcfilename =
    let infile = open_in srcfilename in
    let parsedmod = parse_sourcefile infile srcfilename in
    if cconfig.parse_only then (
      print_string (module_to_string parsedmod);
      ispecs (* import specifications carried through *)
    )
    else (
      match analysis cconfig ispecs parsedmod with
      | Error errs -> 
         prerr_string (format_errors srcfilename errs);
         exit 1
      (* Here is where I may want to generate a new spec from the 
         module that was just analyzed. *)
      | Ok (typedmod, tenv, syms(*, new_ispecs? *)) -> (
        if not cconfig.typecheck_only then (
          debug_print "* codegen stage reached";
          let open Llvm_target in
          let machine = gen_target_machine () in
          let layout = TargetMachine.data_layout machine in
          let modcode, header = codegen cconfig tenv syms layout typedmod in
          (* should we set this before codegen? *)
          Llvm.set_target_triple (TargetMachine.triple machine) modcode;
          (* print_string (st_node_to_string topsyms); *)
          if parsedmod.name <> "" then 
            write_header cconfig.source_dir header;
          if cconfig.emit_llvm then 
            write_module_llvm srcfilename modcode
          else 
            write_module_native srcfilename modcode cconfig machine
        )
      ); ispecs
    )
  in
  (* We accumulate module headers for efficiency, to avoid reading the same 
   * one multiple times. *)
  ignore (List.fold_left process_sourcefile StrMap.empty srcfiles)
