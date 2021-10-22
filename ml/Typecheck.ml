;; open Ast
;; open STLC

let error loc s =
  failwith @@ Printf.sprintf "ERROR: %s - %s" (Range.string_of_range loc) s

module Unify = struct

type uvar = int

let gensym : unit -> uvar =
  let cnt = ref 0 in
  fun () -> let n = !cnt in cnt := (n+1); n

(* This could be made simpler/more uniform by factoring out constructors. *)
type t =
  | UVar of uvar       (* unification variable *)
  | Base of int
  | Zero
  | Plus of t * t
  | One
  | Prod of t * t
  | Arr of t * t


let fresh_uvar () = UVar (gensym ())

(* Invariants: 
    - the substitution is sorted by vars 
    - if (x, Var y) is in the list, then x <> y
*)
type subst = (uvar * t) list

let empty : subst = []

let check (x:uvar) (t:t) : bool =
  t = UVar x

let rec contains (t:t) (x:uvar) : bool =
  begin match t with
  | UVar y -> x = y
  | Base _ | Zero | One -> false
  | Plus(t1, t2) | Prod(t1, t2) | Arr(t1, t2)-> (contains t1 x) || (contains t2 x)
  end

let assign (s:subst) (x:uvar) (t:t) : subst =

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

let rec lookup (s : subst) (x:uvar) : t =
  begin match s with
  | [] -> UVar x
  | (y,u)::rest ->
     if x = y then u else
     if x < y then UVar x
     else lookup rest x
  end

let rec apply (s : subst) (t:t) : t =
  begin match t with
  | UVar x -> lookup s x
  | Base _ | Zero | One -> t
  | Plus(t1, t2) -> Plus(apply s t1, apply s t2)        
  | Prod(t1, t2) -> Prod(apply s t1, apply s t2)
  | Arr(t1, t2) -> Arr(apply s t1, apply s t2)        
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

let elim (x:uvar) (t:t) : (t * t) list -> (t * t) list  =
  List.map (fun (t1,t2) -> (apply [(x,t)] t1, apply [(x,t)] t2))

let elim_s (x:uvar) (t:t) : subst -> subst =
  List.map (fun (y,u) -> (y, apply [(x,t)] u))


let rec unify (eqns:(t * t) list) (so:subst option) : subst option =
  begin match so with
  | None -> None
  | Some s ->
     begin match eqns with
       | [] -> Some s
       | (t1,t2)::eqns' ->
          begin match t1 with
          | UVar x ->
             if t2 = UVar x then unify eqns' so else
             if contains t2 x then None else   (* occurs check *)
             unify (elim x t2 eqns') (Some (assign (elim_s x t2 s) x t2))             
          | Base n ->
             begin match t2 with
             | UVar y -> unify ((t2, t1)::eqns') so
             | Base m ->
                if n = m then unify eqns' so else None
             | _ -> None
             end
          | Zero ->
             begin match t2 with
             | UVar y -> unify ((t2, t1)::eqns') so
             | Zero -> unify eqns' so
             | _ -> None
             end
          | One ->
             begin match t2 with
             | UVar y -> unify ((t2, t1)::eqns') so
             | One -> unify eqns' so
             | _ -> None
             end

          | Plus(t11, t12) ->
             begin match t2 with
             | UVar y ->  unify ((t2, t1)::eqns') so
             | Plus(t21, t22) ->
                unify ((t11, t21)::(t12, t22)::eqns') so
             | _ -> None
             end
                
          | Prod(t11, t12) ->
             begin match t2 with
             | UVar y ->  unify ((t2, t1)::eqns') so
             | Prod(t21, t22) ->
                unify ((t11, t21)::(t12, t22)::eqns') so
             | _ -> None
             end

          | Arr(t11, t12) ->
             begin match t2 with
             | UVar y ->  unify ((t2, t1)::eqns') so
             | Arr(t21, t22) ->
                unify ((t11, t21)::(t12, t22)::eqns') so
             | _ -> None
             end
          end
     end
  end


end

module Infer = struct

  type ctx = (id * Unify.t) list

  let rec translate_ty (tc : ctx) (t:(unit, Ast.ty) node) : Unify.t =
    begin match t.elt with
      | TId t -> List.assoc t tc
      | TBase n -> Base n
      | TZero -> Zero
      | TSum(t, u) -> Plus(translate_ty tc t, (translate_ty tc u))
      | TUnit -> One
      | TProd(t, u) -> Prod(translate_ty tc t, (translate_ty tc u))
      | TArr(t, u) -> Arr(translate_ty tc t, (translate_ty tc u))        
    end

  type in_exp = (unit, unit Ast.exp) node
  type dec_exp = (Unify.t, Unify.t Ast.exp) node
  type eqns = (Unify.t * Unify.t) list

  let decorate elt loc d = { elt; loc; dec=Some d}

  let rec elaborate (tc:ctx) (g:ctx) (e:in_exp) : Unify.t * eqns * dec_exp =
    begin match e.elt with
      | Const(n, t) ->
        let tt = translate_ty tc t in
        tt, [], (decorate (Ast.Const(n,t)) e.loc tt)

      | Id x ->
        let tt = try List.assoc x g with
          | Not_found -> error e.loc (Printf.sprintf "Variable %s not in scope." x)
        in
        tt, [], (decorate (Ast.Id x) e.loc tt)

      | Abort | Fst | Snd -> error e.loc "This term must be applied"

      | Inl e' ->
        let (lt, eqns, de) = elaborate tc g e' in
        let rt = Unify.fresh_uvar () in
        let tt = Unify.Plus(lt, rt) in
        tt, eqns, (decorate (Ast.Inl de) e.loc tt)

      | Inr e' ->
        let (rt, eqns, de) = elaborate tc g e' in
        let lt = Unify.fresh_uvar () in
        let tt = Unify.Plus(lt, rt) in
        tt, eqns, (decorate (Ast.Inr de) e.loc tt)

      | Case(e1, x, e2, y, e3) ->
        let lt = Unify.fresh_uvar () in
        let rt = Unify.fresh_uvar () in
        let te1, eqns1, de1 = elaborate tc g e1 in
        let te2, eqns2, de2 = elaborate tc ((x, lt)::g) e2 in
        let te3, eqns3, de3 = elaborate tc ((y, rt)::g) e3 in
        te3, ([(te1, Unify.Plus(lt, rt)); (te2, te3)]@eqns3@eqns2@eqns1),
        (decorate (Ast.Case(de1, x, de2, y, de3)) e.loc te3)

      | Unit ->
        let tt = Unify.One in 
        tt, [], (decorate (Ast.Unit) e.loc tt)

      | Pair(e1, e2) ->
        let te1, eqns1, de1 = elaborate tc g e1 in
        let te2, eqns2, de2 = elaborate tc g e2 in
        let tt = Unify.Prod(te1, te2) in
        tt, (eqns2@eqns1), (decorate (Ast.Pair(de1, de2)) e.loc tt)

      | Let((x, t), e1, e2) ->
        let tx = translate_ty tc t in
        let te1, eqns1, de1 = elaborate tc g e1 in
        let te2, eqns2, de2 = elaborate tc ((x,tx)::g) e2 in
        te2, ([(tx, te1)]@eqns2@eqns1),
        decorate (Ast.Let((x, t), de1, de2)) e.loc te2

      | Lam(xs, e) ->
        if List.length xs = 0 then error e.loc (Printf.sprintf "Functions must take at least one argument") else
          let txs = List.map (fun (x, t) -> (x, translate_ty tc t)) xs in
          let te, eqns, de = elaborate tc (txs @ g) e in
          let tt = List.fold_right (fun (_, t) arr -> Unify.Arr(t, arr)) txs te in
          tt, eqns, decorate (Ast.Lam(xs, de)) e.loc tt

      | App(e1, e2) ->
        let te2, eqns2, de2 = elaborate tc g e2 in
        begin match e1.elt with
          | Abort ->
            let tt = Unify.fresh_uvar () in
            tt, ([(Unify.Zero, te2)]@eqns2),
            decorate (Ast.App(decorate Ast.Abort e1.loc Unify.Zero,
                              de2)) e.loc tt

          | Fst ->
            let tl = Unify.fresh_uvar () in
            let tr = Unify.fresh_uvar () in
            let tt = Unify.Prod(tl, tr) in
            tl, ([(tt, te2)]@eqns2),
            decorate (Ast.App(decorate Ast.Fst e1.loc Unify.Zero,
                              de2)) e.loc tl

          | Snd ->
            let tl = Unify.fresh_uvar () in
            let tr = Unify.fresh_uvar () in
            let tt = Unify.Prod(tl, tr) in
            tr, ([(tt, te2)]@eqns2),
            decorate (Ast.App(decorate Ast.Snd e1.loc Unify.Zero,
                              de2)) e.loc tr

          | _ ->
            let te1, eqns1, de1 = elaborate tc g e1 in
            let tl = Unify.fresh_uvar () in
            let tr = Unify.fresh_uvar () in
            let tt = Unify.Arr(tl, tr) in
            tr, ([(tt, te1); (tl, te2)]@eqns2@eqns1),
            decorate (Ast.App(de1, de2)) e.loc tr

        end
    end

  type in_ctx = (id * (unit, ty) node) list

  (* This isn't very efficient, but should be fine for small sets of type declarations *)    
  let elaborate_ctx (tc : in_ctx) : ctx =
    let rec loop (tc : in_ctx) (ttc : ctx) : ctx =
      begin match tc with
        | [] -> ttc
        | (x, t)::tc' ->
          let tt = translate_ty ttc t  in
          loop tc' (ttc @ [(x, tt)])
      end
    in
    loop tc []

  let rec apply_subst (s : Unify.subst) (e : dec_exp) : dec_exp =
    match e.dec with
    | None -> failwith "applying substitution to non-decorated expression"
    | Some d ->
      {elt = apply_subst_exp s e.elt; loc=e.loc; dec=Some (Unify.apply s d)}
      
  and apply_subst_exp (s : Unify.subst) e =
    let sub = apply_subst s in 
    begin match e with
      | Const(_,_) | Id _ | Abort | Unit | Fst | Snd -> e
      | Inl e -> Inl (sub e)
      | Inr e -> Inr (sub e)
      | Case(e1, x, e2, y, e3) -> Case(sub e1, x, sub e2, y, sub e3)
      | Pair(e1, e2) -> Pair(sub e1, sub e2)
      | Let(b, e1, e2) -> Let(b, sub e1, sub e2)
      | Lam(bs, e2) -> Lam(bs, sub e2)
      | App(e1, e2) -> App(sub e1, sub e2)
    end
      
  let elaborate_tm (tc : ctx) (e : in_exp) : dec_exp =
    let _, eqns, dt = elaborate tc [] e in
    begin match Unify.unify eqns (Some (Unify.empty)) with
      | None -> failwith "Program Ill-typed"
      | Some s -> apply_subst s dt
    end

end

  
module Translate = struct
    
  type ctx = (id * STLC.typ) list
    
  let rec translate_ty (t : Unify.t) : STLC.typ =
    begin match t with
      | UVar u -> failwith "translation error: found an unconstrained UVar"
      | Base n -> Base n
      | Zero -> Zero
      | Plus(t, u) -> Plus(translate_ty t, (translate_ty u))
      | One -> One
      | Prod(t, u) -> Prod(translate_ty t, (translate_ty u))
      | Arr(t, u) -> Arr(translate_ty t, (translate_ty u))        
    end

  let translate_ctx (g:Infer.ctx) : ctx =
    List.map (fun (x, t) -> (x, translate_ty t)) g
  
  let rec lookup_ctx (g:ctx) (x:id) : STLC.var =
    begin match g with
      | [] -> failwith (Printf.sprintf "var %s not in scope" x)
      | (y,u)::g' ->
        if x = y then Z else
          let v = lookup_ctx g' x in S v
    end

  let rec translate_tm (g:ctx) (e : Infer.dec_exp) : STLC.tm =
    begin match e.dec with
      | None -> failwith "translation error: trying to translate undecorated node"
      | Some d ->
        let t = translate_ty d in
        begin match e.elt  with
          | Ast.Const(x,_) -> Const(x,t)
          | Ast.Id x -> Var (lookup_ctx g x)
          | Ast.Abort | Ast.Fst | Ast.Snd -> error e.loc "INTERNAL: This term must be applied"
          | Ast.Inl e -> Inl(t, translate_tm g e)
          | Ast.Inr e -> Inr(t, translate_tm g e)
          | Ast.Case(e1, x, e2, y, e3) ->
            begin match e1.dec with
              | None -> error e.loc "trying to translate undecorated node"
              | Some (Plus(t1, t2)) ->
                let tt1 = translate_ty t1 in
                let tt2 = translate_ty t2 in
                let te1 = translate_tm g e1 in
                let te2 = translate_tm ((x,tt1)::g) e2 in
                let te3 = translate_tm ((y,tt2)::g) e3 in
                Case(Plus(tt1, tt2), t, te1, te2, te3)
              | _ -> error e.loc "INTERNAL: ill-typed case"
            end
          | Ast.Unit -> Unit
          | Ast.Pair(e1, e2) ->
                Pair(t, translate_tm g e1, translate_tm g e2)
          | Ast.Let((x,_), e1, e2) ->
            begin match e1.dec with
              | None -> error e.loc "trying to translate undecorated node"
              | Some te1 ->
                let tte1 = translate_ty te1 in
                let body = Abs(tte1, translate_tm ((x,tte1)::g) e2) in
                let arg = translate_tm g e1 in
                App(Arr(tte1, t), body, arg)
            end
              (* NOTE: the empty list here is a "hack" that acts as a base
                 case, the source language doesn't allow empty args *)

          | Ast.Lam(bs, e1) ->
            let rec loop bs t g =
              begin match bs, t  with
                | [], _ -> translate_tm g e1
                | ((x,_)::xs), Arr(tx, tl) ->
                  Abs(tx, loop xs tl ((x,tx)::g))
                | _ -> error e.loc "INTERNAL: ill-typed lambda"
              end
            in
            loop bs t g
          | Ast.App(e1, e2) ->
            let te2 = translate_tm g e2 in
            begin match e1.elt with
              | Abort -> Err(t, te2)
              | Fst ->
                begin match e2.dec with
                  | Some (Prod(t, u)) -> Fst(Prod(translate_ty t, translate_ty u), te2)
                  |  _ -> error e.loc "INTERNAL: ill-typed product fst"
                end
              | Snd ->
                begin match e2.dec with
                  | Some (Prod(t, u)) -> Snd(Prod(translate_ty t, translate_ty u), te2)
                  |  _ -> error e.loc "INTERNAL: ill-typed product snd"
                end
              | _ ->
                begin match e1.dec with
                  | Some (Arr(t, u)) ->
                    let te1 = translate_tm g e1 in 
                    App(Arr(translate_ty t, translate_ty u), te1, te2)
                  | _ -> error e.loc "INTERNAL: ill-typed application"
                end
            end
        end
    end
  
end


  
