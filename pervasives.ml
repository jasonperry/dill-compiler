(** Symtable entries for the always-open module (later to be replaced
   with code that reads an interface file and generates the entries. *)

(* open Types *)
open Symtable1

(* TODO: make just fsyms to add to some other symtable. *)

(* generic over address type *)
let pervasive_syms () =
  (* Actually, I kind of want pervasives to have "no module". *)
  let syms = Symtable.make_empty () in
  (* Symtable.addproc syms "printInt" {
      procname="printInt";  (* leaving module off will work? *)
      rettype=void_ttag;
      fparams=[{symname="n"; symtype=int_ttag; var=false; addr=None}];
    };
  Symtable.addproc syms "printFloat" {
      procname="printFloat";
      rettype=void_ttag;
      fparams=[{symname="x"; symtype=float_ttag; var=false; addr=None}];
    }; *)
  (* Symtable.addproc syms {
      procname="printBool";
      rettype=void_ttag;
      fparams=[{symname="b"; symtype=float_ttag; var=false; addr=None}];
    }; *)
  syms
