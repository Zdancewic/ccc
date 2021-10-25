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
    | Zero       -> zero
    | Plus(t, u) -> sum (denote_typ t) (denote_typ u)
    | One        -> one
    | Prod(t, u) -> prod (denote_typ t) (denote_typ u)
    | Arr(t, u)  -> exp (denote_typ t) (denote_typ u)
    end

  let rec denote_ctx (g:ctx) : obj =
    begin match g with
    | [] -> one
    | t::g' -> prod (denote_typ t) (denote_ctx g')
    end

  (*
       denote_var g v :  denote_ctx g ==> denote_typ (lookup_cxt g v)
   *)
  let rec denote_var (g:ctx) (v:var) : hom =
    begin match g, v with
    | [] , _     -> failwith "denote_var: variable not bound"
    | t::g', Z   -> C.fst (denote_typ t) (denote_ctx g')
    | t::g', S n -> (C.snd (denote_typ t) (denote_ctx g')) >>> (denote_var g' n)
    end

  (* denote_tm c g e : (denote_ctx g) ==> (denote_typ t)  where g |- e t  
   *)
  let denote_tm (c:int -> hom) (g:ctx) (e:tm) : hom =
    let rec denote (g:ctx) (e:tm) = 
      begin match e with
        | Const (n,t) ->
          (unit (denote_ctx g)) >>> (c n)
                                    
        | Var v ->
          denote_var g v

        | Err(t, e) ->
          (denote g e) >>> (abort (denote_typ t))

        | Inl(Plus(t, u), e) ->
          (denote g e) >>> (inl (denote_typ t) (denote_typ u))

        | Inr(Plus(t, u), e) ->
          (denote g e) >>> (inr (denote_typ t) (denote_typ u))

        | Case(Plus(t, u), r, e, lft, rgt)  ->
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
              
        | Unit ->
          unit (denote_ctx g)

        | Fst(Prod(t, u), e) ->
          (denote g e) >>> (fst (denote_typ t) (denote_typ u))

        | Snd(Prod(t, u), e) ->
          (denote g e) >>> (snd (denote_typ t) (denote_typ u))

        | Pair(Prod(t, u), e1, e2) ->
          pair (denote g e1) (denote g e2)

        | Abs(t, e) ->
          curry ((swap (denote_ctx g) (denote_typ t)) >>> (denote (t::g) e))

        | App(Arr(t, u), e1, e2) ->
          (pair (denote g e1) (denote g e2)) >>> (apply (denote_typ t) (denote_typ u))

        | _ -> failwith "ERROR: Denotation - type annotation mismatch"
      end
    in
    denote g e

  
  let pp_denotation (f : Format.formatter) (h : hom) : unit =
    C.pp_hom f h
        
  let string_of ppx x : string =
    let open Format in 
    pp_open_hvbox str_formatter 0;
    ppx str_formatter x;
    pp_close_box str_formatter ();
    flush_str_formatter ()

  let string_of_denotation (h:hom) : string =
    string_of pp_denotation h
  
end  
