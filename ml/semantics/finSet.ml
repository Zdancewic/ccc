;; open Atom
;; open CCC

module FinSet : CCC = struct

  (*
  type base = Atom.t
  type one = Atom.t
  type ('a, 'b) prod = Atom.t
  type zero = Atom.t
  type ('a, 'b) sum = Atom.t
  type ('a, 'b) exp = Atom.t
   *)

  type obj = AtomSet.t
  type hom = Atom.t AtomMap.t

  let eq2 f g = AtomMap.compare Atom.compare f g = 0

  let id a = AtomSet.fold (fun x m -> AtomMap.add x x m)  a AtomMap.empty
  let (>>>) f g =
    try
      AtomMap.fold (fun k v m ->
          AtomMap.add k (AtomMap.find v g) m) f AtomMap.empty
    with
    | Not_found -> Printf.printf ("f = %s\n\ng = %s\n\n")
                     (Atom.to_string (Atom.Map f))
                     (Atom.to_string (Atom.Map g)); failwith "ERROR: f >>> g FAILED"

  
  (* In FinSet, [b x] is the Finite Set {0, 1, ..., x} *)
  let b x =
    let rec loop n acc =
      if n = 0 then acc else loop (n-1) (AtomSet.add (Atom.Base (n-1)) acc)
    in
    loop x AtomSet.empty

  (* one is the same as the singleton set {0} *)
  let one = b 1

  let zero = b 0
  
  let abort _ = AtomMap.empty

  (* the disjoint union of two sets *)
  let sum a b =
    AtomSet.union
      (AtomSet.map (fun x -> Atom.Inl x) a)
      (AtomSet.map (fun y -> Atom.Inr y) b)

  let inl a b = AtomSet.fold (fun x m -> AtomMap.add x (Atom.Inl x) m) a AtomMap.empty
  let inr a b = AtomSet.fold (fun x m -> AtomMap.add x (Atom.Inr x) m) b AtomMap.empty
  let case f g =
    let m = AtomMap.fold (fun k v m -> AtomMap.add (Atom.Inl k) v m) f AtomMap.empty in
    AtomMap.fold (fun k v m -> AtomMap.add (Atom.Inr k) v m) g m

  
  let unit a = AtomSet.fold (fun x m -> AtomMap.add x (Atom.Base 0) m) a AtomMap.empty

  (* the cartesian product of two finite sets *)
  let prod a b  =
    AtomSet.fold
      (fun ai s ->
        AtomSet.fold
          (fun bj s ->
            AtomSet.add (Atom.Prod(ai, bj)) s)
          b s)
      a AtomSet.empty
  
  let fst a b =
    AtomSet.fold (fun x m ->
        AtomSet.fold (fun y m -> AtomMap.add (Atom.Prod(x,y)) x m) b m) a AtomMap.empty

  let snd a b =
    AtomSet.fold (fun x m ->
        AtomSet.fold (fun y m -> AtomMap.add (Atom.Prod(x,y)) y m) b m) a AtomMap.empty
  
  (* Assumes that dom(f) and dom(g) are the same! *)
  let pair f g =
    AtomMap.fold (fun k x m -> AtomMap.add k (Atom.Prod(x, AtomMap.find k g)) m) f AtomMap.empty



  (* The exponential object in finite sets [a -> b] is the set of all maps from [a] to [b].
     It has cardinality [a -> b] = (cardinality b) ^ (cardinality a) 
  *)
  (* 
     Given sets [a] and [b] computes the set of all functions [a -> b] represented 
     as Atom.Map m where m is a Atom.t AtomMap.t.

     If [a] is {a1, ... , an} and [b] is {b1, ... , bm} then we 

     build the set of all functions [a] to [b] by recursively building the set of all
     functions F from {a2, ..., an} to [b] and then for each such f we add
       f + a1 -> b1
       f + a1 -> b2
       f + a1 -> ...
       f + a1 -> bn
     to the set

  *)
  let exp (a : obj) (b : obj) :  AtomSet.t =
    let base = AtomSet.singleton (Atom.Map (AtomMap.empty)) in
    let extend (ai : Atom.t) (f : Atom.t AtomMap.t) : AtomSet.t =
      AtomSet.fold (fun bj s -> AtomSet.add (Atom.Map (AtomMap.add ai bj f)) s) b AtomSet.empty
    in
    let accumulate (ai : Atom.t) (fs : AtomSet.t) : AtomSet.t =
      AtomSet.fold (fun f s ->
          begin match f with
          | Atom.Map fm ->  AtomSet.union (extend ai fm) s
          | _ -> failwith "accumulate found non-map"
          end
        ) fs AtomSet.empty
    in
    AtomSet.fold accumulate a base

  (* f is an Atom.t AtomMap.t where the domain is assumed to be a cartesian product
     of [a * b] and the range is [c].  It produces a new map with doman [a] and 
     range [b -> c] by "reassociating the map" and collecting the resulting map
     [b -> c].
   *)
  let curry f  =
    AtomMap.fold (fun k z m ->
        begin match k with
        | Atom.Prod(x, y) ->
           AtomMap.update x 
             (fun opt ->
               begin match opt with
               | None                 -> Some (Atom.Map(AtomMap.singleton y z))
               | Some (Atom.Map(exp)) -> Some (Atom.Map(AtomMap.add y z exp))
               | _ -> failwith "curry: not a map!"
               end)
             m
        | _ -> failwith "curry: input not a product!"
        end) f AtomMap.empty

  (* The "apply" morphism in finite sets is basically a big lookup table, where the
     keys are pairs of the form (f, a) where f is a map [a -> b] and each such pair
     is sent by the map to (f a).  The size of the apply map is thus 

   *)  
  let apply a b =
    let exp = exp a b in
    let pairs = prod exp a in
    let app p =
      begin match p with
      | Atom.Prod(Atom.Map m, a) -> AtomMap.find a m
      | _ -> failwith "app: ill-formed pair"
      end
    in
    AtomSet.fold (fun p m -> AtomMap.add p (app p) m) pairs AtomMap.empty

  let pp_obj f o =
    let open Format in
    pp_print_string f "{";
    pp_open_hovbox f 1;
    pp_print_list ~pp_sep:(fun f () -> pp_print_string f ","; pp_print_space f ()) Atom.pp f (AtomSet.elements o);
    pp_print_string f "}";
    pp_close_box f ()

  let pp_hom f h =
    let open Format in
    let pps = pp_print_string f in
    
    pps "["; pp_open_hovbox f 0;
    (pp_print_list ~pp_sep:(fun f () -> pp_print_string f ","; pp_print_space f ())
       (fun f (k,v) -> Atom.pp f k; pp_print_string f " ==> "; Atom.pp f v)
       f
       (AtomMap.bindings h));
    pp_close_box f ();          
    pps "]"
      
  let string_of ppx x : string =
    let open Format in 
    pp_open_hvbox str_formatter 0;
    ppx str_formatter x;
    pp_close_box str_formatter ();
    flush_str_formatter ()
      
  let string_of_obj o =
    string_of pp_obj o

  let string_of_hom (m : Atom.t AtomMap.t) : string =
    string_of pp_hom m
  
end
