(** Recursive descent parser for dill *)

open Slexer

let modsource buf =
  match (token buf).ttype with
  | _ -> print_string "hooray"

(* temporary top-level code *)
let _ =
  Printexc.register_printer (
    function 
    | SyntaxError e -> Some (e.msg ^ " somehwere")
    | _ -> None);
  let lexbuf = Sedlexing.Utf8.from_string "42" in
  modsource lexbuf
