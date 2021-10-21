
type ('d, 'a) node = { elt : 'a; loc : Range.t; dec : 'd option}

(** val no_loc : 'a1 -> 'a1 node **)

let no_loc x =
  { elt = x; loc = Range.norange ; dec = None }

type id = string

type ty =
  | TId of id                            (* X, T, Bool *)
  | TBase of int                         (* B[n] *)
  | TZero                                (* Zero *)
  | TSum of (unit, ty) node * (unit, ty) node            (* ty1 + ty2 *)
  | TUnit                                (* One *)
  | TProd of (unit, ty) node * (unit, ty) node           (* ty1 * ty2 *)
  | TArr of (unit, ty) node * (unit, ty) node            (* ty1 -> ty2 *)

type tydef = id * (unit, ty) node                (* type Tid = ty *)
 
type bnd = id * (unit, ty) node                  (* x : ty *)

type 'd exp =
  | Const of int * (unit, ty) node               (* const[i : t] *)
  | Id of id                             (* x *)
  | Abort                                (* abort (must be applied) *)
  | Inl of ('d, 'd exp) node                      (* inl(e) *)
  | Inr of ('d, 'd exp) node                      (* inr(e) *)
  | Case of ('d, 'd exp) node
            * id * ('d, 'd exp) node
            * id * ('d, 'd exp) node              (* begin match e with | inl(x) -> e1 | inr(y) -> e2 end *)
  | Unit                                 (* () *)
  | Fst                                  (* fst (must be applied) *)
  | Snd                                  (* snd (must be applied) *)
  | Pair of ('d, 'd exp) node * ('d, 'd exp) node          (* ( e1 , e2 ) *)
  | Let of bnd * ('d, 'd exp) node * ('d, 'd exp) node     (* let x : ty = e1 in e2 *)
  | Lam of bnd list * ('d, 'd exp) node           (* fun (x1 : ty1) ... (xn : tyn) -> e *)
  | App of ('d, 'd exp) node * ('d, 'd exp) node           (* e1 e2 *)


type 'd prog = tydef list * ('d, 'd exp) node

