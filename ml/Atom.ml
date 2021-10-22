;; open StringLib


let pretty = ref false 
    
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
    val pp : Format.formatter -> t -> unit
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

    let rec pp (f : Format.formatter) t =
      let open Format in
      let ps = pp_print_space f in
      let pps = pp_print_string f in
      begin match t with
        | Base x -> pp_print_int f x
        | Inl x ->
          if !pretty && x = (Base 0)
          then pps "T"
          else (pps "Inl"; ps (); pp f x)
        | Inr x ->
          if !pretty && x = (Base 0)
          then pps "F"
          else (pps "Inr"; ps (); pp f x)
        | Prod(x,y) ->
          pp_open_hbox f ();
          pps "("; pp f x; pps ","; ps (); pp f y; pps ")";
          pp_close_box f ()
        | Map m ->
          pps "["; pp_open_hovbox f 0;
          (pp_print_list ~pp_sep:(fun f () -> pp_print_string f ","; pp_print_space f ())
             (fun f (k,v) ->
                pp f k;
                pp_print_space f (); pp_print_string f "->"; pp_print_space f ();
                pp f v)
            f
            (AtomMap.bindings m));
          pp_close_box f ();          
          pps "]"
      end


  let string_of ppx x : string =
    let open Format in 
    pp_open_hvbox str_formatter 0;
    ppx str_formatter x;
    pp_close_box str_formatter ();
    flush_str_formatter ()

  let to_string t : string =
    string_of pp t
    
  end

and AtomMap : Map.S with type key = Atom.t = Map.Make(Atom)

module AtomSet : Set.S with type elt = Atom.t = Set.Make(Atom)


