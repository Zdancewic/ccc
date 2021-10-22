open Printf

(* files processed during this run of the compiler *)
let files : string list ref = ref []

(* terminal output ---------------------------------------------------------- *)
  
let print_banner s =
  let rec dashes n = if n = 0 then "" else "-"^(dashes (n-1)) in
  printf "%s %s\n%!" (dashes (79 - (String.length s))) s

let print_lc file lc_ast =
    print_banner (file ^ ".stlc");
    print_endline (AstLib.string_of_prog lc_ast)

(* file i/o ----------------------------------------------------------------- *)

let read_file (file:string) : string =
  let lines = ref [] in
  let channel = open_in file in
  try while true; do
      lines := input_line channel :: !lines
  done; ""
  with End_of_file ->
    close_in channel;
    String.concat "\n" (List.rev !lines)

let write_file (file:string) (out:string) =
  let channel = open_out file in
  fprintf channel "%s" out;
  close_out channel


  
(* compiler pipeline -------------------------------------------------------- *)

(* These functions implement the compiler pipeline for a single stlc file:
     - parse the file 
     - print the file
*)
let parse_lc_file filename =
  let program = read_file filename |> 
                Lexing.from_string |>
                Parser.prog Lexer.token
  in
  program


let string_of_lc_ast path lc_ast =
  let lc_str = AstLib.string_of_prog lc_ast in
  let prog = Printf.sprintf "; generated from: %s\n%s\n"
      path lc_str in
  prog


let process_lc_ast path file lc_ast =
  let _ = print_lc file lc_ast in
  let _ = Printf.printf "\n---------------------------------------------------\n" in
  let (tydefs, e) = lc_ast in
  let tc = Typecheck.Infer.elaborate_ctx tydefs in
  let tm = Typecheck.Infer.elaborate_tm tc e in
  let stlc_tm = Typecheck.Translate.translate_tm [] tm in
  let d = Top.D.denote_tm (fun _ -> failwith "const") [] stlc_tm in
  Printf.printf "DENOTATION: \n%s\n%!"
    (Top.D.string_of_denotation d)
    

  

let process_lc_file path file =
  let lc_ast = parse_lc_file path in
  process_lc_ast path file lc_ast

(* process files based on extension ----------------------------------------- *)

let process_file path =
  let basename, ext = Platform.path_to_basename_ext path in
  begin match ext with
    | "stlc" -> process_lc_file path basename
    | _ -> failwith @@ Printf.sprintf "found unsupported file type: %s" path
  end

(* process each file separately and then link all of them together *)
let process_files files =
  if (List.length files) > 0 then begin

    List.iter process_file files

  end


