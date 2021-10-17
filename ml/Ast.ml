
type 'a node = { elt : 'a; loc : Range.t }

(** val no_loc : 'a1 -> 'a1 node **)

let no_loc x =
  { elt = x; loc = Range.norange }

type id = string

type ty =
  | TId of id                            (* X, T, Bool *)
  | TBase of int                         (* B[n] *)
  | TZero                                (* Zero *)
  | TSum of ty node * ty node            (* ty1 + ty2 *)
  | TUnit                                (* One *)
  | TProd of ty node * ty node           (* ty1 * ty2 *)
  | TArr of ty node * ty node            (* ty1 -> ty2 *)

type tydef = id * ty node                (* type Tid = ty *)
 
type bnd = id * ty node                  (* x : ty *)

type exp =
  | Const of int * ty node               (* const[i : t] *)
  | Id of id                             (* x *)
  | Unit                                 (* () *)
  | Inl of exp node                      (* inl(e) *)
  | Inr of exp node                      (* inr(e) *)
  | Case of exp node
            * id * exp node
            * id * exp node              (* begin match e with | inl(x) -> e1 | inr(y) -> e2 end *)
  | Pair of exp node * exp node          (* ( e1 , e2 ) *)
  | Fst of exp node                      (* fst e *)
  | Snd of exp node                      (* snd e *)
  | Let of bnd * exp node * exp node     (* let x : ty = e1 in e2 *)
  | Lam of bnd list * exp node           (* fun (x1 : ty1) ... (xn : tyn) -> e *)
  | App of exp node * exp node           (* e1 e2 *)


type prog = tydef list * exp node
