(** The obligatory utilities-needed-by-everything module. *)

let _debug = ref false

let debug_print s =
  if !_debug then print_endline s
  else ()

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
module TypeMap = Map.Make(StrPairs)

let print_typekeys (tmap: 'a TypeMap.t) =
  TypeMap.bindings tmap
  |> List.iter (fun ((modalias, tname), _) ->
         print_endline (modalias ^ " :: " ^ tname))

(* List.concat_map doesn't exist until OCaml 4.10 *)
let concat_map f l = List.concat (List.map f l)

(** Mash list of error lists into a single list *)
let concat_errors rlist =
  (* the list of errors are each themselves lists. *)
  List.concat (
      (* List.concat_map ( (* 4.10 only *) *)
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
