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
