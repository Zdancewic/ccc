;; open STLC
;; open CCC


module Denote (C : CCC) = struct
  open C

  (* swap : A * B ==>  B * A *)


  (* 
      g : A * B ==> C
      curry g : A ==> (B -> C)


     x:t, g |- e : u
    ----------------------------
     g, |- lam (x:t). e : t -> u


     [[ e ]] : [[x:t, g]] ==> [[u]]
             ; [[t]] * [[g]] ==> [[u]]
    
     (swap >>> [[e]]) : [[g]] * [[t]] ==> [[u]]

     curry (swap >> [[e]]) : [[g]] ==> [[t -> u]]


   *)
  (*
     f : A ==> B
     g : A ==> C

    pair f g : A ==> B * C
   *)

   (*  
    fst : A * B ==> A
    snd : A * B ==> B
    ----------------------------------
    pair snd fst : (A * B) ==> (B * A)
   *)
  let swap (a : obj) (b : obj) : hom =
    pair (snd a b) (fst a b)
  
  let rec denote_typ (t:typ) : obj =
    begin match t with
    | Base n     -> b n
    | Zero       -> z  
    | Plus(t, u) -> sum (denote_typ t) (denote_typ u)
    | One        -> u
    | Prod(t, u) -> prod (denote_typ t) (denote_typ u)
    | Arr(t, u)  -> exp (denote_typ t) (denote_typ u)
    end

  let rec denote_ctx (g:ctx) : obj =
    begin match g with
    | [] -> u
    | t::g' -> prod (denote_typ t) (denote_ctx g')
    end

  (*
       denote_var g v :  denote_ctx g ==> denote_typ (lookup_cxt g v)
   *)
  let rec denote_var (g:ctx) (v:var) : hom =
    begin match g, v with
    | [] , _ -> failwith "denote_var: variable not bound"
    | t::g', Z -> C.fst (denote_typ t) (denote_ctx g')
    | t::g', S n -> (C.snd (denote_typ t) (denote_ctx g')) >>> (denote_var g' n)
    end

  (* denote_tm c g e : (denote_ctx g) ==> (denote_typ t)  where g |- e t  
   *)
  let denote_tm (c:int -> hom) (g:ctx) (e:tm) : hom =
    let rec denote (g:ctx) (e:tm) = 
      begin match e with
      | Const (n,t) -> (unit (denote_ctx g)) >>> (c n)
      | Var v -> denote_var g v
      | Err(t, e) -> (denote g e) >>> (zero (denote_typ t))
      | Inl(t, u, e) -> (denote g e) >>> (inl (denote_typ t) (denote_typ u))
      | Inr(t, u, e) -> (denote g e) >>> (inr (denote_typ t) (denote_typ u))
      | Case(t, u, r, e, lft, rgt)  ->
         let dg = denote_ctx g in 
         (pair
            ((denote g e)
                >>>
                  (case
                     (curry (denote (t::g) lft))
                     (curry (denote (u::g) rgt))
                  ))
            (id dg))
          >>> (apply dg (denote_typ r))
      | Unit -> unit (denote_ctx g)
      | Fst(t, u, e) -> (denote g e) >>> (fst (denote_typ t) (denote_typ u))
      | Snd(t, u, e) -> (denote g e) >>> (snd (denote_typ t) (denote_typ u))
      | Pair(t, u, e1, e2) -> pair (denote g e1) (denote g e2)
      | Abs(t, u, e) ->
         curry ((swap (denote_ctx g) (denote_typ t)) >>> (denote (t::g) e))

      | App(t, u, e1, e2) ->
         (pair (denote g e1) (denote g e2)) >>> (apply (denote_typ t) (denote_typ u))
      end
    in
    denote g e
         
  

  
end  
