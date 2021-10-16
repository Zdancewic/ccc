;; open StringLib

(*
  This is a type for "finite sets" with some structure.  Atom.t forms a total order
  and we can therefore put them into Set data structures.

  Morally, we will think of atoms as being "typed" by this type system:

    T,U ::=   Fin(n)  | T + U  | T * U  |  T => U

   [[T]]  : Atom.t Set.t

   [[Fin(n)]] = {Base(0), ... , Base(n-1)}
   [[T + U]]  = {Inl t | t \in [[T]]} \cup {Inr u | u \in [[U]] }
   [[T * U]]  = {Prod(t,u) | t \in [[T]], u \in [[U]]}
   [[T => U]] = {Map m | List.map fst (AtomMap.bindings m) = Set.to_list [[T]]}


     x < n
  ---------------
  Base x : Fin(n)
  
       t : T              u : U
  ---------------    ---------------    
   Inl t : T + U      Inr u : T + U


     t : T    u : U
  -------------------
   Prod(t,u) : T * U


  domain(m) = [[T]] and forall t in domain(m)   m(t) : U
  ---------------------------------------------------------
    Map m : T => U



 *)
module
  rec Atom : sig
    type t =
      | Base of int
      | Inl of t
      | Inr of t
      | Prod of t * t
      | Map of t AtomMap.t
    
    val compare : t -> t -> int
    val to_string : t -> string
  end =
  
  struct
    type t =
      | Base of int
      | Inl of t
      | Inr of t
      | Prod of t * t
      | Map of t AtomMap.t
    
    let rec compare t1 t2 =
      begin match t1, t2 with
      | Base x, Base y -> Int.compare x y
      | Base _, _ -> -1

      | Inl _, Base _ -> 1
      | Inl x, Inl y -> compare x y
      | Inl _, _ -> -1

      | Inr _, Base _ -> 1
      | Inr _, Inl _ -> 1
      | Inr x, Inr y -> compare x y
      | Inr _, _ -> -1

      | Prod(_,_), Base _ -> 1
      | Prod(_,_), Inl _ -> 1
      | Prod(_,_), Inr _ -> 1
      | Prod(x1,x2), Prod(y1,y2) ->
         let c1 = compare x1 y1 in
         if c1 = 0 then compare x2 y2
         else c1
      | Prod(_,_), _ -> -1

      | Map x, Map y -> AtomMap.compare compare x y
      | Map _, _ -> 1
      end

    let rec to_string t =
      begin match t with
      | Base x -> Int.to_string x
      | Inl x -> "Inl " ^ (to_string x)
      | Inr x -> "Inr " ^ (to_string x)
      | Prod(x,y) -> "(" ^ (to_string x) ^ "," ^ (to_string y) ^ ")"
      | Map m ->
         let s = String.concat ", "
                   (List.map 
                      (fun (k,v) -> (to_string k) ^ "->" ^ (to_string v))
                      (AtomMap.bindings m) )
         in
         "[" ^ s ^ "]"
      end
         
    
  end

and AtomMap : Map.S with type key = Atom.t = Map.Make(Atom)

module AtomSet : Set.S with type elt = Atom.t = Set.Make(Atom)


