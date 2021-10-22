(* astlib.ml *)
(* Helper functions of abstract syntax of trees. *)
(******************************************************************************)

open Format
open Ast
open Range

(* Precedence for expressions and operators *)
(* Higher precedences bind more tightly     *)

let prec_of_ty = function
| TArr(_,_) -> 50
| TProd(_,_) -> 80
| TSum(_,_) -> 80
| _  -> 100

let prec_of_exp = function
| App(_,_) -> 10
| Let(_,_,_) -> 50
| Lam(_,_) -> 50
| _ -> 130




(* Pretty Printer for AST *)

let string_of ppx x : string =
  pp_open_hvbox str_formatter 0;
  ppx str_formatter x;
  pp_close_box str_formatter ();
  flush_str_formatter ()


let print_id_aux fmt (x:id) = pp_print_string fmt x

let rec print_list_aux fmt sep pp l =
  begin match l with
    | []    -> ()
    | [h]   -> pp fmt h
    | h::tl -> pp fmt h; sep ();
	           print_list_aux fmt sep pp tl
  end

let rec print_ty_aux level fmt t =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in  
  let this_level = prec_of_ty t.elt in
  if this_level < level then pps "(";  
  begin match t.elt with
  | TId(x)      -> print_id_aux fmt x
  | TBase(n)    -> pps (Printf.sprintf "Base[%d]" n)
  | TZero       -> pps "Zero"
  | TSum(t,u)   ->
     begin
       pp_open_box fmt 0;
       print_ty_aux this_level fmt t;
       ppsp (); pps "+"; ppsp ();
       print_ty_aux this_level fmt u;
       pp_close_box fmt ()
     end
  | TUnit       -> pps "One"
  | TProd(t,u)   ->
     begin
       pp_open_box fmt 0;
       print_ty_aux this_level fmt t;
       ppsp (); pps "*"; ppsp ();
       print_ty_aux this_level fmt u;
       pp_close_box fmt ()
     end
  | TArr(t,u)   ->
     begin
       pp_open_box fmt 0;
       print_ty_aux (this_level + 5) fmt t;      (*  A * B -> C + D  *)
       ppsp (); pps "->"; ppsp ();
       print_ty_aux this_level fmt u;
       pp_close_box fmt ()
     end
  end;
  if this_level < level then pps ")"
     

and print_exp_aux level fmt e =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  let ppnl = pp_force_newline fmt in
  let this_level = prec_of_exp e.elt in

  if this_level < level then pps "(";
  begin match e.elt with
  | Const(x,t) -> pps (Printf.sprintf "c[%d : %s]" x (string_of (print_ty_aux 0) t))

  | Id id -> print_id_aux fmt id

  | Abort -> pps "abort"
        
  | Inl   -> pps "inl"

  | Inr   -> pps "inr"

  | Case(e1, x, ex, y, ey) ->
     pp_open_box fmt 0;
     pps "begin match "; print_exp_aux 0 fmt e1; pps " with"; ppnl ();
     pps "  | inl "; print_id_aux fmt x; pps " -> ";
     pp_open_box fmt 4; print_exp_aux 0 fmt ex;
     pp_close_box fmt (); ppnl ();
     pps "  | inr "; print_id_aux fmt y; pps " -> ";
     pp_open_box fmt 4; print_exp_aux 0 fmt ey;
     pp_close_box fmt (); ppnl ();
     pps "end";
     pp_close_box fmt ()

  | Unit -> pps "()"

  | Pair(e1, e2) -> pps "("; print_exp_aux 0 fmt e1; pps ", "; print_exp_aux 0 fmt e2; pps ")"

  | Fst -> pps "fst"

  | Snd -> pps "snd"

  | Let((x, t), e1, e2) ->
     pp_open_hbox fmt ();
     pps "let "; print_id_aux fmt x; pps " : "; print_ty_aux 0 fmt t; pps " ="; ppsp ();
     print_exp_aux 0 fmt e1;
     ppsp (); pps "in";
     pp_close_box fmt ();
     ppnl ();
     print_exp_aux 0 fmt e2;
     pp_close_box fmt ()

  | Lam(args, body) ->
     pp_open_box fmt 0;
     pps "fun ";
     print_list_aux fmt ppsp print_bnd_aux args;
     pps " ->"; ppsp ();
     print_exp_aux 0 fmt body;
     pp_close_box fmt ()

  | App(e1, e2) ->
    pp_open_hbox fmt ();
    print_exp_aux this_level fmt e1; ppsp (); print_exp_aux 100 fmt e2;
    pp_close_box fmt ()
      
  end; if this_level < level then pps ")"

and print_bnd_aux fmt (id, t) =
  let pps = pp_print_string fmt in
  pps "("; print_id_aux fmt id; pps " : "; print_ty_aux 0 fmt t; pps ")"

let print_tydef_aux fmt (tid, t) =
  let pps = pp_print_string fmt in
  let ppsp = pp_print_space fmt in
  pp_open_box fmt 0;
  pps "type"; ppsp ();
  print_id_aux fmt tid; ppsp();
  pps "="; ppsp ();
  print_ty_aux 0 fmt t;
  pp_close_box fmt ()
  

let print_prog_aux fmt (p:'d prog) =
  let ppnl = pp_force_newline fmt in
  pp_open_vbox fmt 0;
  List.iter (fun td -> print_tydef_aux fmt td; ppnl (); ppnl ()) (fst p);
  ppnl ();
  print_exp_aux 0 fmt (snd p);
  pp_close_box fmt ()

let print ppx x : unit =
  pp_open_hvbox std_formatter 0;
  ppx std_formatter x;
  pp_close_box std_formatter ();
  pp_print_newline std_formatter ()

let print_prog (p:'d prog) : unit = print print_prog_aux p
let string_of_prog (p:'d prog) : string = string_of print_prog_aux p

let print_ty (t:(unit, ty) node) : unit = print (print_ty_aux 0) t
let string_of_ty (t:(unit, ty) node) : string = string_of (print_ty_aux 0) t

let print_exp (e:('d, 'd exp) node) : unit = print (print_exp_aux 0) e
let string_of_exp (e:('d, 'd exp) node) : string = string_of (print_exp_aux 0) e

let print_ty (t:(unit, ty) node) : unit = print (print_ty_aux 0) t
let string_of_ty (t:(unit, ty) node) : string = string_of (print_ty_aux 0) t

