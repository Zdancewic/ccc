type var = int

type tm =
  | Var of var
  | Leaf of int
  | Pair of tm * tm

(* Invariants: 
    - the substitution is sorted by vars 
    - if (x, Var y) is in the list, then x <> y
*)
type subst = (var * tm) list

let empty : subst = []

let check (x:var) (t:tm) : bool =
  t = Var x

let rec contains (t:tm) (x:var) : bool =
  begin match t with
  | Var y -> x = y
  | Leaf _ -> false
  | Pair(t1, t2) -> (contains t1 x) || (contains t2 x)
  end

let assign (s:subst) (x:var) (t:tm) : subst =

  let rec assign' (s:subst) =
    begin match s with
    | [] -> [(x, t)]
    | (y,u)::rest ->
       if x = y then (y,t)::rest else
       if x < y then (x,t)::(y,u)::rest
       else (y,u)::(assign' rest)
    end
  in
  if check x t then failwith "illegal identity assignment" else 
    assign' s

let rec lookup (s : subst) (x:var) : tm =
  begin match s with
  | [] -> Var x
  | (y,u)::rest ->
     if x = y then u else
     if x < y then Var x
     else lookup rest x
  end

let rec apply (s : subst) (t:tm) : tm =
  begin match t with
  | Var x -> lookup s x
  | Leaf _ -> t
  | Pair(t1, t2) -> Pair(apply s t1, apply s t2)
  end

let rec compose_subst (s1:subst) (s2:subst) : subst =
  begin match s1 with
  | [] -> s2
  | (x,t)::s1' ->
     begin match s2 with
     | [] -> s1
     | (y,u)::s2' ->
        if x = y then failwith "non-disjoint substitution composition!" else
          if x < y then (x, apply s2 t)::compose_subst s1' s2 else
            (y,u)::(compose_subst s1 s2')
     end
  end

let bind (m:'a option) (k: 'a -> 'b option) : 'b option =
  begin match m with
  | None -> None
  | Some x -> k x
  end

let elim (x:var) (t:tm) : (tm * tm) list -> (tm * tm) list  =
  List.map (fun (t1,t2) -> (apply [(x,t)] t1, apply [(x,t)] t2))

let elim_s (x:var) (t:tm) : subst -> subst =
  List.map (fun (y,u) -> (y, apply [(x,t)] u))


let rec unify (eqns:(tm * tm) list) (so:subst option) : subst option =
  begin match so with
  | None -> None
  | Some s ->
     begin match eqns with
       | [] -> Some s
       | (t1,t2)::eqns' ->
          begin match t1 with
          | Var x ->
             if t2 = Var x then unify eqns' so else
             if contains t2 x then None else   (* occurs check *)
             unify (elim x t2 eqns') (Some (assign (elim_s x t2 s) x t2))             
          | Leaf n ->
             begin match t2 with
             | Var y -> unify ((t2, t1)::eqns') so
             | Leaf m ->
                if n = m then unify eqns' so else None
             | Pair(_,_) -> None
             end
          | Pair(t11, t12) ->
             begin match t2 with
             | Var y ->  unify ((t2, t1)::eqns') so
             | Leaf _ -> None
             | Pair(t21, t22) ->
                unify ((t11, t21)::(t12, t22)::eqns') so
             end
          end
     end
  end


type tm_ =
  | Conflict_ of tm * tm
  | Var_ of var
  | Leaf_ of int
  | Pair_ of tm_ * tm_

let rec inc (t:tm) : tm_ =
  begin match t with
  | Var x -> Var_ x
  | Leaf n -> Leaf_ n
  | Pair (t11, t12) -> Pair_ (inc t11, inc t12)
  end

let rec apply_ (s:subst) (u : tm_) : tm_ =
  begin match u with
  | Conflict_ (t1, t2) -> Conflict_ (apply s t1, apply s t2)
  | Var_ y -> inc (lookup s y)
  | Leaf_ n -> u
  | Pair_ (u11, u12) -> Pair_ (apply_ s u11, apply_ s u12)
  end

let rec i_unify (t1:tm) (t2:tm) (k : tm_ * subst -> 'a) : 'a =
  begin match t1 with
  | Var x ->
     begin match t2 with
     | Var y ->
        if x = y then k (Var_ x, [])
        else if x < y then k (Var_ x, [(y, Var x)])
        else k (Var_ y, [(x, Var y)])

     | t2' ->
        if contains t2 x
        then k (Conflict_ (t1 ,t2), [])   (* This is the case where there is a cycle *)
        else k (inc t2', [(x, t2')])
     end

  | Leaf n ->
     begin match t2 with
     | Var y ->
        k (Leaf_ n, [(y, Leaf n)])
        
     | Leaf m ->
        if n = m
        then k (Leaf_ n, [])
        else k (Conflict_ (t1, t2), [])

     | Pair(_,_) ->
        k (Conflict_(Leaf n, t2), [])
     end
     
  | Pair(t11, t12) ->
     begin match t2 with
     | Var y ->
        if contains t1 y
        then k (Conflict_ (t1, t2), [])
        else k (inc t2, [(y, t2)])
        
     | Leaf _ ->
        k (Conflict_(t1, t2), [])
        
     | Pair(t21, t22) ->
        i_unify t11 t21
          (fun (lft, s1) ->
            i_unify (apply s1 t12) (apply s1 t22)
              (fun (rgt, s2) ->
                k (Pair_(apply_ s2 lft, rgt), compose_subst s1 s2)))
     end     
  end


(*
  (x, x) = ((1, 2), 3)
  ==>
  ((1,2),CC[(1,2)|3]) , [x=(1,2)]
  -of-
  (3, CC[3 | (1,2)])  , [x=3]


  (x, (y, y)) = ((y, y), (1, 2))
  ==>
  



  (x, (x,x)) = (1, (2, 3))
   ==>
  (x, (-,-)), [x=1], [(rl->(1,2)), (rr->(1,3))

 -or-
  (-, (x,-)), [x=2], [(l->(1,2)), (rr->(2,3))]

 -or-
  (-, (-, x)), [x=3], [(l->(1,3)), (rl->(2,3))]


  (x, (x,x)) = ((1,2), (2, (1,3)))
   ==>
  (x, (-,-)), [x = (1,2)], [rl->((1,2),2), rrr->(2,3)]
  -or-
  (-, (x,-)), [x = 2], [l->(2,(1,2)), rr->(2,(1,3))]
  -or-
  (-, (-,x)), [x = (1,3)], [lr->(3,2), rl->((1,3),2)]

 



  ((x, (x, x)), (y, 1)) = ((1, (2, 3), (x, x)))
  ==>
  ((x, (-, -)), (y, 1)), [x->1, y->1], [lrl->(1,2), lrr->(1,3)]
  -or-
  ((1, (-, -)), (y, x)), [x->1, y->1], [lrl->(1,2), lrr->(1,3)]
  -or-
  ((-, (x, -)), (y, -)), [x->2, y->2], [ll->(1,2), lrr->(2,3), rr->(1,2)]
  -or-
  ((-, (-, x)), (y, -)), [x->3, y->3], [ll->(1,3), lrl->(2,3), rr->(1,3)]
  -or-
  

  (x,x) = (y,1)
     [x->1, y->1]


  (x, (x,x)) , [(x, [1;2;3]))

  (x, (y,z)) = (1, (2, 3))
   ==>
  (x, (y, z)), [(x, [1]); (y, [2]); (z, [3])]

  (1, (2, 3)) = (3, 2, 1))
   ==>
  (a, (2, b)), [(a,[(1,3)]); (b,[(3,1)]]]

 *)


(*

let rec unify (t1:tm) (t2:tm) : subst option =
  begin match t1 with
  | Var x ->
     begin match t2 with
     | Var y -> if x = y then Some [] else Some (assign empty x t2)
     | Leaf -> Some (assign empty x t2)
     | Pair(_,_) -> Some (assign empty x t2)
     end
  | Leaf ->
     begin match t2 with
     | Var y -> Some (assign empty y t1)
     | Leaf -> Some empty
     | Pair(_,_) -> None
     end
  | Pair(t11, t12) ->
     begin match t2 with
     | Var y -> Some (assign empty y t1)
     | Leaf -> None
     | Pair(t21, t22) ->
        bind (unify t11 t21)
          (fun s ->
            let t12' = apply s t12 in
            let t22' = apply s t22 in
            bind (unify t12' t22')
           (fun s' -> -> combine s s'))
     end
  end
and combine (s1 : subst) (s2 : subst) : subst option =
  begin match s1, s2 with
  | [], [] -> Some []
  | [], s2 -> Some s2
  | s1, [] -> Some s1
  | (x,t)::r1, (y,u)::r2 ->
     if x < y then bind (combine r1 s2) (fun s -> (x,t)::s) else
     if x = y then
 *)     


let ex1 : tm = Pair(Var 0, Pair(Var 1, Var 1))
let ex2 : tm = Pair(Pair(Leaf 0, Leaf 0), Var 0)
let ex3 : tm = Pair(Pair(Var 0, Var 1), Var 1)     
let ex4 : tm = Pair(Pair(Var 0, Var 1), Pair(Leaf 0,Var 1))
let ex5 : tm = Pair(Var 0, Var 0)
let ex6 : tm = Pair(Var 1, Leaf 0)
let ex7 : tm = Pair(Var 0, Pair (Var 1, Var 2))
let ex8 : tm = Pair(Var 1, Pair (Var 2, Var 0))
let ex9 : tm = Pair(Leaf 1, Pair (Leaf 2, Leaf 3))

