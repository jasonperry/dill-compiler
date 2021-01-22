(** The obligatory utilities-needed-by-everything module. *)

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

(* Currently only used for (module, classname) types. But we'll see. *)
(* Oh, but maybe I have to use it for tenv now too! *)
module TypeMap = Map.Make(StrPairs)

(* List.concat_map doesn't exist until 4.10 *)
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
