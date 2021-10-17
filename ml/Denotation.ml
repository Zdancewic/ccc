;; open STLC
;; open CCC


module Denote (C : CCC) = struct
  open C

  let swap (o1 : obj) (o2 : obj) : hom =
    pair (snd o1 o2) (fst o1 o2)
  
  let rec denote_typ (t:typ) : obj =
    begin match t with
    | Base n -> b n
    | Zero   -> z  (* Thunked? *)
    | Plus(t, u) -> sum (denote_typ t) (denote_typ u)
    | One -> u
    | Prod(t, u) -> prod (denote_typ t) (denote_typ u)
    | Arr(t, u) -> exp (denote_typ t) (denote_typ u)
    end

  let rec denote_ctx (g:ctx) : obj =
    begin match g with
    | [] -> u
    | t::g' -> prod (denote_typ t) (denote_ctx g')
    end

  let rec denote_var (g:ctx) (v:var) : hom =
    begin match g, v with
    | [] , _ -> failwith "denote_var: variable not bound"
    | t::g', Z -> C.fst (denote_typ t) (denote_ctx g')
    | t::g', S n -> (C.fst (denote_typ t) (denote_ctx g')) >>> (denote_var g' n)
    end

  let denote_tm (c:int -> hom) (g:ctx) (e:tm) : hom =
    let rec denote (g:ctx) (e:tm) = 
      begin match e with
      | Const (n,t) -> (unit (denote_ctx g)) >>> (c n)
      | Var v -> denote_var g v
      | Err e -> (denote g e) >>> zero
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
