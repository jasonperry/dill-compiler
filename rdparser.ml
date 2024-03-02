(** Recursive descent parser for dill *)

open Common
open Slexer

let modsource buf =
  match (token buf).ttype with
  | ICONST i -> print_string ("ICONST " ^ Int64.to_string i ^ "\n")
  | _ -> print_string "something else"

(* temporary top-level code *)
let _ =
  (* Could go in dillc.ml *)
  Printexc.register_printer (
    function 
    | SyntaxError e -> Some (
        (fst e.loc).pos_fname ^ ":" ^ format_loc (fst e.loc) (snd e.loc)
        ^ ":" ^ e.msg
      )
    | _ -> None);
  let lexbuf = Sedlexing.Utf8.from_string "42" in
  modsource lexbuf
