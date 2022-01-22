;; open Atom
;; open CCC

module CatSyntax (* : CCC *) = struct

  (*
  type base = Atom.t
  type one = Atom.t
  type ('a, 'b) prod = Atom.t
  type zero = Atom.t
  type ('a, 'b) sum = Atom.t
  type ('a, 'b) exp = Atom.t
   *)

  type obj =
  | Base of int
  | Zero   (* void *)
  | Sum of obj * obj
  | One
  | Prod of obj * obj
  | Exp  of obj * obj

  type base_hom =
    | ABORT 
    | INL 
    | INR
    | CASE of hom * hom
    | UNIT
    | PROD of hom * hom
    | FST
    | SND
    | CURRY of hom
    | APPLY
  
  and hom =
    | HOM of {src: obj; tgt: obj; m: base_hom list}

  (* eq2 is the hard thing to implement in this category, it has to
     "normalize" by the equational theory *)              
  let eq2 f g = failwith "todo!"

  let id a = HOM {src = a; tgt = a; m = [] }
      
  let (>>>)
      (HOM{src=srcf; tgt=tgtf; m=mf})
      (HOM{src=srcg; tgt=tgtg; m=mg}) =
    if tgtf = srcg then HOM{src=srcf; tgt=tgtg; m=mf @ mg}
    else failwith "error! tried to compose incompatible homs"
  
  (* In FinSet, [b x] is the Finite Set {0, 1, ..., x} *)
  let b x = Base x

  (* one is the same as the singleton set {0} *)
  let one = b 1
  let zero = b 0
  
  let abort a = HOM {src = zero; tgt = a; m = [ABORT]}

  (* the disjoint union of two sets *)
  let sum a b = Sum(a, b)

  let inl a b = HOM{src=a; tgt=sum a b; m = [INL]}
  let inr a b = HOM{src=a; tgt=sum a b; m = [INR]}
  let case (HOM f) (HOM g) =
    if f.tgt <> g.tgt then failwith "error! tried to 'case' two incompatible homs"
    else
      HOM{src=sum f.src g.src; tgt=f.tgt; m = [CASE(HOM f, HOM g)]}
  
  let unit a = HOM{src=a; tgt=one; m = [UNIT]}

  (* the cartesian product of two finite sets *)
  let prod a b = Prod(a,b)
      
  let fst a b = HOM{src=prod a b; tgt=a; m = [FST]}
  let snd a b = HOM{src=prod a b; tgt=b; m = [SND]}          
  
  (* Assumes that dom(f) and dom(g) are the same! *)
  let pair (HOM f) (HOM g)  =
    if f.src <> g.src then failwith "error! tried to 'prod' two incompatible homs"
    else
      HOM{src=f.src; tgt=Prod(f.tgt, g.tgt); m = [PROD(HOM f, HOM g)]}

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
  let exp (a : obj) (b : obj) = Exp(a, b)

  (* f is an Atom.t AtomMap.t where the domain is assumed to be a cartesian product
     of [a * b] and the range is [c].  It produces a new map with doman [a] and 
     range [b -> c] by "reassociating the map" and collecting the resulting map
     [b -> c].
   *)
  let curry (HOM f)  =
    begin match f.src with
      | Prod(a, b) -> HOM{src=a; tgt=Exp(b,f.tgt); m = [CURRY(HOM f)]}
      | _ -> failwith "error! tried to curry incompatible hom"
    end
                        
  (* The "apply" morphism in finite sets is basically a big lookup table, where the
     keys are pairs of the form (f, a) where f is a map [a -> b] and each such pair
     is sent by the map to (f a).  The size of the apply map is thus 

   *)  
  let apply a b =
    HOM{src=(Prod(Exp(a,b),a)); tgt=b; m = [APPLY]}
    
  let rec pp_obj f o =
    let open Format in
    pp_open_hovbox f 0;

    
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
