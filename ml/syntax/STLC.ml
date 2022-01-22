
(* Types *)
type typ =
  | Base of int
  | Zero   (* void *)
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
  | Const of lit          (* Const(i,t) : t *)
  | Var of var
  | Err of typ * tm       (* Abort *)
  | Inl of typ * tm
  | Inr of typ * tm
  (* case (t1+t2) t (e : (t1+t2)) (br1 : t1 |- t) (br2 : t2 |- t) *)  
  | Case of typ * typ * tm * tm * tm
  | Unit
  | Fst of typ * tm
  | Snd of typ * tm
  | Pair of typ * tm * tm
  | Abs of typ * tm
  | App of typ * tm * tm


(* fun (x:B(2)) -> x *)
let ex1 : tm =
  Abs(Base 2, Var Z)

(* fun (x:Unit + Unit) -> x *)
let bool_t = Plus(One, One)
let ex2 : tm =
  Abs(bool_t, Var Z)

let ex3 : tm =
  App(Arr(bool_t, bool_t), ex2, (Inl(Plus(One, One), Unit)))

(* fun x -> begin match z with | inl(x) -> inr(x) | inr(x) -> inl(x) end *)
let ex4 : tm =
  Abs(bool_t,
      Case(Plus(One, One), bool_t, (Var Z), (Inr(Plus(One, One), Var Z)), (Inl(Plus(One, One), Var Z))))

