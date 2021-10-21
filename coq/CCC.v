From Coq Require Import
     List
     Program.Equality
     Classes.RelationClasses.

From ITree Require Import
     Basics.Category
     CategoryOps
     CategoryTheory.

Import Carrier.

From CCC Require Import
     STLC.

Import CatNotations.
Local Open Scope cat_scope.

Open Scope list_scope.
Import ListNotations.

Module Denotation(BT : Base).

  Module L := STLC(BT).
  Import L.
  Import BT.
       
  Section Denote.

  Context {obj : Type} (C : Hom obj).
  Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
  Context (ONE : obj)
          {Term_C : Terminal C ONE}.
  Context (PROD : binop obj).
  Context {Pair_C : Pair C PROD}
          {Fst_C : Fst C PROD}
          {Snd_C : Snd C PROD}.
  Context (ZERO : obj)
          {Initial_C : Initial C ZERO}.
  Context (SUM : binop obj).
  Context {Case_C : Case C SUM}
          {Inl_C : Inl C SUM}
          {Inr_C : Inr C SUM}.
  Context (EXP : binop obj).
  Context {Apply_C : Apply C PROD EXP}
          {Curry_C : Curry C PROD EXP}.

  Context {Equivalence_Eq2 : forall a b, Equivalence (@eq2 obj C _ a b)}.
  
  Existing Instance Bimap_Product.
  Existing Instance Swap_Product.

  Context {CCC : CartesianClosed C ONE PROD EXP}.

  Context {denote_B : B -> obj}.
  Context {denote_Const : forall (c:BT.Const), C ONE (denote_B (base_type c))}.

  Fixpoint denote_typ (t:typ) : obj :=
    match t with
    | Base b => denote_B b
    | Zero => ZERO
    | Plus t1 t2 => SUM (denote_typ t1) (denote_typ t2)
    | One => ONE
    | Prod t1 t2 => PROD (denote_typ t1) (denote_typ t2)
    | Arr t1 t2  => EXP (denote_typ t1) (denote_typ t2)
    end.

  Fixpoint denote_ctx (G:ctx) : obj :=
    match G with
    | nil => ONE
    | t::G => PROD (denote_typ t) (denote_ctx G)
    end.

  Program Definition denote_var {G:ctx} {t:typ} (v : var G t) : C (denote_ctx G) (denote_typ t).
  induction v.
  - cbn. exact fst_.
  - eapply cat. exact snd_. apply IHv.
  Defined. 

  Program Definition denote_tm {G:ctx} {t:typ} (e : tm G t) : C (denote_ctx G) (denote_typ t).
  induction e.
  - eapply cat. exact one. exact (denote_Const c).
  - exact (denote_var v).
  - eapply cat. exact IHe. exact empty.
  - eapply cat. exact IHe. exact inl_.
  - eapply cat. exact IHe. exact inr_.
  - cbn in *.
    exact ((pair_ (IHe1 >>> case_ (curry_ IHe2) (curry_ IHe3))) (id_ _) >>> apply_).
  - exact one.
  - eapply cat. exact IHe. exact fst_.
  - eapply cat. exact IHe. exact snd_.
  - exact (pair_ IHe1 IHe2).
  - cbn in *.
    exact (curry_ (@swap _ _ PROD _ _ _ >>> IHe)).
  - exact (pair_ IHe1 IHe2 >>> apply_).
  Defined.    


  (* One might like to prove something like this, but it basically requires proving 
     termination of the step semantics. *)
  Lemma step_soundness1 :
    forall (t:typ) (e : tm [] t) ans
      (H: step t e = ans),
      (forall (e' : tm [] t), ans = inl e' ->  denote_tm e ⩯ denote_tm e') /\
      (forall v, ans = inr v -> denote_tm e ⩯ denote_tm (tm_of_val _ v)).
  Proof.
    intros t e ans H.
    dependent induction e; (split; [intros e' Hans | intros v' Hans]).
    - cbn in H. rewrite Hans in H; inversion H.
    - cbn in H. rewrite Hans in H; inversion H. subst. cbn. reflexivity.
  Abort.
      

  
  End Denote.
End Denotation.  
