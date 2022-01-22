;; open Atom
;; open CCC
;; open FinSet
    
module DiGraph : CCC = struct

  type obj =
    {
      vert : FinSet.obj;
      edge : FinSet.obj;
      src  : FinSet.hom;
      tgt  : FinSet.hom;
    }
    
  type hom =
    {
      vert_map : FinSet.hom;
      edge_map : FinSet.hom;
    }

  let eq2 f g =
    (FinSet.eq2 f.vert_map g.vert_map) && 
    (FinSet.eq2 f.edge_map g.edge_map)   

  let id a =
    {
      vert_map = FinSet.id (a.vert);
      edge_map = FinSet.id (a.edge);
    }

  let (>>>) f g =
    let open FinSet in 
    {
      vert_map = f.vert_map >>> g.vert_map;
      edge_map = f.edge_map >>> g.edge_map;      
    }

  (* The graph I has two nodes and one edge:  s --> t *)
  let graph_I : obj =
    let open FinSet in 
    {
      vert = sum one one;
      edge = one;
      src = inl one one;
      tgt = inr one one;
    }

  (* SAZ: NOTE! CHEAP HACK [b 2] is graph_I (a graph with a non-trivial edge *)
  
  (* A graph with x "self loops" *)
  let b x =
    if x = 2 then graph_I
    else
    let b = FinSet.b x in
    {
      vert = b;
      edge = b;
      src = FinSet.id b;
      tgt = FinSet.id b;
    }

  let one = b 1

  let zero = b 0

  let abort a =
    {
      vert_map = FinSet.abort a.vert;
      edge_map = FinSet.abort a.edge;
    }
      
  let sum x y =
    let open FinSet in
    {
      vert = sum x.vert y.vert;
      edge = sum x.edge y.edge;
      src = case (x.src >>> (inl x.vert y.vert)) (y.src >>> (inr x.vert y.vert));
      tgt = case (x.tgt >>> (inl x.vert y.vert)) (y.tgt >>> (inr x.vert y.vert));
    }

  let inl x y =
    let open FinSet in
    {
      vert_map = inl x.vert y.vert;
      edge_map = inl x.edge y.edge;
    }

  let inr x y =
    let open FinSet in
    {
      vert_map = inr x.vert y.vert;
      edge_map = inr x.edge y.edge;
    }
      
  let case l r =
    let open FinSet in
    {
      vert_map = case l.vert_map r.vert_map;
      edge_map = case l.edge_map r.edge_map;
    }

  let unit x =
    {
      vert_map = FinSet.unit x.vert;
      edge_map = FinSet.unit x.edge;
    }

  let prod x y =
    let open FinSet in
    let bimap_prod a b f g =
      pair (fst a b >>> f) (snd a b >>> g)
    in
    {
      vert = prod x.vert y.vert;
      edge = prod x.edge y.edge;
      src = bimap_prod x.edge y.edge x.src y.src;
      tgt = bimap_prod x.edge y.edge x.tgt y.tgt;
    }

  let fst x y =
    let open FinSet in
    {
      vert_map = fst x.vert y.vert;
      edge_map = fst x.edge y.edge;
    }

  let snd x y =
    let open FinSet in
    {
      vert_map = snd x.vert y.vert;
      edge_map = snd x.edge y.edge;
    }

  let pair f g =
    let open FinSet in
    {
      vert_map = pair f.vert_map g.vert_map;
      edge_map = pair f.edge_map g.edge_map;
    }


  (*
     To get exponentials to work, we have to be a bit careful with our 
     representation  We are using OCaml records to represent the hom
     set of this category, but we need something that can be reified
     in FinSet.  A hom in graph is a pair of homs in FinSet, but
     we have to work with them at the representation level.


     For graphs x, y:
        - the (set of) vertices are the (_arbitrary_ )functions (maps) from x.vert to y.vert

          we represent this in FinSet as
           [FinSet.exp x.vert y.vert]

        - the (set of) edges is given by the set of graph_homomorphisms
           e :  I * x ==> y     (where I * x is a graph)

          represent this in FinSet as
             (FinSet.exp (prod I x).vert y.vert) * (exp (prod I x).edge y.edge)
           ==
             (exp (prod (I.vert) x.vert) y.vert) *
             (exp (prod (I.edge) x.edge) y.edge)
           ==
              vmt x y * emt x y

        - if e is an edge, then
          src e : [x -> y] is   fun x -> e (inl (), x)
          tgt e : [x -> y] is   fun x -> e (inr (), x)

    represent src : hom (vmt x y * emt x y) (exp x y)



     (bimap (fst (vmt x y * emt x y) x.vert) (pair (unit x.vert >>> inl) id x.vert)) >>> apply 

      f : (vmt x y * emt x y) * x ==> y
     ----------------------------------------
     curry f : (vmt x y * emt x y) ==> [x -> y]


      (<vm,em>, x) ==> <fst, <unit x.vert >>> inl, id>> >>> apply_
                   
     f : [A * B -> C] * A ==> [B -> C]
     curry f  : [A * B -> C] ==> [A -> [B -> C]]

     apply A B : [A -> B] * A ==> B

  *)
  (*  TODO: this is very convoluted and not easy to understand
     also, the only difference between the src and tgt maps is 'inl' vs. 'inr', so it
     would be better to share most of this work.
  *)

  let vert_map_type x y =
    let open FinSet in    
    exp (prod (graph_I.vert) x.vert) y.vert
      
  let edge_map_type x y =
    let open FinSet in
    exp (prod (graph_I.edge) x.edge) y.edge 


  (* Build the FinSet representation of the set of all Graph Morphisms from
      x to y.  This is isomorphic to:
    { (vm : vert_map, em : edge_map) |
          forall e : x.edge. vm (x.src e) = y.src (em e) /\
                             vm (x.tgt e) = y.tgt (em e) }
     
    But we have to represent vert_map as [exp x.vert y.vert] and
    edget_map as [exp x.edge y.edge]

     

  *)
  let graph_morphisms x y : FinSet.obj =
    let open FinSet in
    let vm = exp x.vert y.vert in
    let em = exp x.edge y.edge in
    let m = prod vm em in
    (* Assumes that the elements of the map have the right "shape" *)
    let test (a : Atom.t) =
      begin match a with
        | Prod(Map(vm), Map(em)) ->
          AtomSet.for_all
            (fun e ->
               let e' = AtomMap.find e em in
               let x_src = AtomMap.find e (Obj.magic x.src) in
               let x_tgt = AtomMap.find e (Obj.magic x.tgt) in
               (Atom.compare (AtomMap.find x_src vm) (AtomMap.find e' (Obj.magic y.src)) = 0)
               &&
               (Atom.compare (AtomMap.find x_tgt vm) (AtomMap.find e' (Obj.magic y.tgt)) = 0)
            )
            (Obj.magic x.edge)
          
        | _ -> failwith "graph_morphism build ill-shaped atoms"
      end
    in
    Obj.magic (AtomSet.filter test (Obj.magic m))

    
  
  
  let exp x y =
    let vmt = vert_map_type x y in
    let emt = edge_map_type x y in
    {
      vert = FinSet.exp x.vert y.vert;
      edge = (graph_morphisms (prod graph_I x) y);         (* graph morphisms of type (I * x) ==> y *)
      src  =
        begin
          let open FinSet in
          let f =
                let bimap_prod a b f g =
                  pair (fst a b >>> f) (snd a b >>> g)
                in
                bimap_prod (prod vmt emt) x.vert
                  (fst vmt emt)
                  (pair (unit x.vert >>> inl one one) (id x.vert))
                  
          in
          curry (f >>> apply (prod (graph_I.vert) x.vert) y.vert)
        end
      ;
      tgt  =
        begin
          let open FinSet in
          let f =
                let bimap_prod a b f g =
                  pair (fst a b >>> f) (snd a b >>> g)
                in
                bimap_prod (prod vmt emt) x.vert
                  (fst vmt emt)
                  (pair (unit x.vert >>> inr one one) (id x.vert))
                  
          in
          curry (f >>> apply (prod (graph_I.vert) x.vert) y.vert)
        end
    }
    
  (* apply x y : [x -> y] * x ==> y
         
     ([x -> y] * x).edge =
     prod ([x -> y].edge) x.edge =
     prod (prod (vert_map_type x y) (edge_map_type x y)) x.edge
     prod (prod (vmt x y) (exp (prod I.edge x.edge) y.edge)) x.edge     

     (bimap_prod snd (pair (const_tt) id)) >>> apply
     
  *)
  let apply x y =
    let open FinSet in
    let vmt = vert_map_type x y in
    let emt = edge_map_type x y in
    let bimap_prod a b f g =
      pair (fst a b >>> f) (snd a b >>> g)
    in
    {
      vert_map = apply x.vert y.vert;
      edge_map =
        (bimap_prod (prod vmt emt) x.edge
          (snd vmt emt)
          (pair (unit x.vert) (id x.edge))) >>> (apply (prod (graph_I.edge) x.edge) y.edge)
        
    }


  (* f : x * y ==> z
     curry f : x ==> [y -> z]

     f.edge_map : FinSet.hom (prod x.edge y.edge) z.edge
     
     (curry f).edge_map : hom x.edge [y -> z].edge
     hom x.edge (exp (pr
  *)
  let curry f =
    let open FinSet in
    failwith "todo"
    (* { *)
    (*   vert_map = curry f.vert_map; *)
    (*   edge_map =  *)
    (* } *)


  (* For debugging *)  
  let pp_obj (f:Format.formatter) (x:obj) = 
    let open Format in
    let pps = pp_print_string f in
    let pp_vert f v = pps "\""; Atom.pp f v; pps "\"" in
    let pp_edge f e =
      let s = AtomMap.find e (Obj.magic x.src) in
      let t = AtomMap.find e (Obj.magic x.tgt) in
      pp_vert f s;
      pps " -> ";
      pp_vert f t
    in
    
    pp_print_string f "strict digraph {"; pp_force_newline f ();
    pp_print_string f "/* nodes */"; pp_force_newline f ();
    pp_print_string f "  ";
    pp_open_vbox f 0;
    pp_print_list ~pp_sep:(fun f () -> pp_print_space f ())
      pp_vert
      f
      (AtomSet.elements (Obj.magic x.vert));
    pp_close_box f ();
    pp_force_newline f ();

    pp_print_string f "/* edges */"; pp_force_newline f ();
    pp_print_string f "  ";
    pp_open_vbox f 0;
    pp_print_list ~pp_sep:(fun f () -> pp_print_space f ())
      pp_edge
      f
      (AtomSet.elements (Obj.magic x.edge));
    pp_close_box f ();
    
    pp_force_newline f ();    
    pp_print_string f "}"
    
    
  let pp_hom (f:Format.formatter) (h:hom) =
    failwith "todo"

  let string_of ppx x : string =
    let open Format in 
    pp_open_hvbox str_formatter 0;
    ppx str_formatter x;
    pp_close_box str_formatter ();
    flush_str_formatter ()
      
  let string_of_obj o =
    string_of pp_obj o

  let string_of_hom m : string =
    string_of pp_hom m
      
  
end  
