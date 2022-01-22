open Arg
open Driver

(* testing harness ---------------------------------------------------------- *)

(* command-line arguments --------------------------------------------------- *)
let args =
  [ 
    ("-op", Set_string Platform.output_path, "set the path to the output files directory  [default='output']")
  ; ("-v", Unit Platform.enable_verbose, "enables more verbose compilation output")
  ; ("-pa", Set Semantics.Atom.pretty, "turn on pretty printing of atoms ")
  ] 


(* Files found on the command line *)
let files = ref []

let main () =
  Platform.configure_os ();
  Platform.create_output_dir ();
    Arg.parse args (fun filename -> files := filename :: !files)
      "Simply Typed Lambda Calculus\n\
       USAGE: ./Main.native [options] <files>\n\
       see README for details about using the compiler";
    
    process_files !files

;; main ()
