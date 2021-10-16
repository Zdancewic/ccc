
(* Types *)
type typ =
  | Base of int
  | Zero
  | Plus of typ * typ
  | One
  | Prod of typ * typ
  | Arr  of typ * typ


type ctx = typ list

(* Terms - these are translated from a dependently typed syntax *)
type var =
  | Z
  | S of var

type lit = int * typ

type tm =
  | Const of lit    (* Const(i,t) : t *)
  | Var of var
  | Err of tm       (* Abort *)
  | Inl of typ * typ * tm
  | Inr of typ * typ * tm
  (* case t1 t2 t (e : (t1+t2)) (br1 : t1 |- t) (br2 : t2 |- t) *)  
  | Case of typ * typ * typ * tm * tm * tm
  | Unit
  | Fst of typ * typ * tm
  | Snd of typ * typ * tm
  | Pair of typ * typ * tm * tm
  | Abs of tm * tm * tm
  | App of typ * typ * tm * tm


(*
  (* var g2 t -> var (g1 ++ g2) t *)
  let rec weaken_var_l (g1 : ctx) (* g2 : ctx *) (v:var) : var =
    begin match g1 with
    | [] -> v
    | _::g1' -> S (weaken_var_l g1' v)
    end

  (* var g1 t -> var (g1 ++ g2) t *)
  let rec weaken_var_r (* (g1 g2 : ctx) *) (v:var) : var = v

  (* var [u1]++[u2]++g t -> var [u2]++[u1]++g t *)
  let swap_var (* (g:ctx) *) (v:var) : var =
    begin match v with
    | Z -> S Z
    | S Z -> Z
    | S n -> v
    end

  (*
      var ([u1] ++ G1 ++ [u2] ++ G2) t ->
      var ([u2] ++ G1 ++ [u1] ++ G2) t.                                           
                               *)
  let rec exchange_var_r (g:ctx) (v:var) : var =
    begin match g with
    | [] -> swap_var v
    | _::g1' -> 

 *)

