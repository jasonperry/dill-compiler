(** The obligatory utilities-needed-by-everything module. *)

let _debug = ref false

let debug_print s =
  if !_debug then print_endline s
  else ()

(** Utility function to find index of an item in a list *)
let listIndex_opt es e =
  let rec loop es i =
    match es with
    | [] -> None
    | elt::rest ->
      if elt = e then (Some i)
      else loop rest (i+1)
  in
  loop es 0

(** in-place type variables for generics, with signature impl requirements *)
(* wait, should this go in types.ml? *)
type typevar = string (* {
    varname: string;
    impls: string list (* probably should be a set later. *)
  } *)

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)

module StrPairs =
  struct
    type t = string * string
    let compare (x0,y0) (x1,y1) =
      match Stdlib.compare x0 x1 with
        0 -> Stdlib.compare y0 y1
      | c -> c
  end

(** Map from string pairs. Currently only used for (module, classname)
   types in the tenv. *)
module PairMap = Map.Make(StrPairs)

let print_typekeys (tmap: 'a PairMap.t) =
  PairMap.bindings tmap
  |> List.iter (fun ((modalias, tname), _) ->
         print_endline (modalias ^ " :: " ^ tname))

(** position info to decorate the AST with. TODO: don't put it here. *)
type locinfo = Lexing.position * Lexing.position

(** This is still used for error messages. And importStmt! *)
type 'a located =
  { loc: Lexing.position * Lexing.position; value: 'a }

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
let format_errors (elist: string located list) =
  let format1 {loc; value} =
    (* TODO: distinguish between error and warning. *)
    "Error: " ^ (fst loc).pos_fname ^ " " ^ format_loc (fst loc) (snd loc)
    ^ ":\n    " ^ value
  in
  (* errors append at beginning, so need to reverse the list. *)
  let errstrs = List.rev_map format1 elist in
  String.concat "\n" errstrs ^ "\n"

(* List.concat_map doesn't exist until OCaml 4.10 *)
let concat_map f l = List.concat (List.map f l)

(** Mash list of error lists into a single list *)
let concat_errors rlist =
  (* the list of errors are each themselves lists. *)
  List.concat (
      concat_map (
          fun r -> match r with
                   | Ok _ -> []
                   | Error erec -> [erec]
        ) rlist
    )

(** Combine all OKs into a single list *)
let concat_ok rlist = concat_map Result.to_list rlist

(* TODO: a check_list that does the map and concat error/Ok *)

(** This might replace most concat_errors and concat_ok *)
let unzip_results rlist =
  (* the list of errors are each themselves lists. *)
  let errs = List.concat (
      concat_map (
          fun r -> match r with
                   | Ok _ -> []
                   | Error erec -> [erec]
        ) rlist
    )
  in
  (concat_map Result.to_list rlist, errs)

(** Fold over a list with a function that returns a result *)
let rec fold_list_result f blist res =
  match blist with
  | [] -> res
  | b::bs -> (match (f b res) with
      | Ok rnew -> fold_list_result f bs rnew
      | Error e -> Error e)             
