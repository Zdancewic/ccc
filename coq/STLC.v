From Coq Require Import
     List.

Open Scope list_scope.
Import ListNotations.

Module Type Base.

  Parameter B : Set.

  Parameter Const : Set.

  Parameter base_type : Const -> B.
  
End Base.


Module STLC (BT: Base).

  Import BT.
  
  Inductive typ : Set :=
  | Base (b:B)
  | Zero
  | Plus (t1 t2:typ)
  | One
  | Prod (t1 t2:typ)
  | Arr  (t1 t2:typ).

  Definition ctx := list typ.

  Inductive var : ctx -> typ -> Set :=
  | VarZ  : forall (G:ctx) (t:typ), var (t::G) t
  | VarS  : forall (G:ctx) (u:typ) (t:typ),
      var G t -> var (u::G) t.
  
  Inductive tm : ctx -> typ -> Set :=
  | Const : forall (G:ctx) (c : BT.Const), tm G (Base (BT.base_type c))
  | Var  : forall G t, var G t -> tm G t
  | Err  : forall (G:ctx) (t:typ),
      tm G Zero -> tm G t
  | Inl : forall G (t1 t2:typ),
      tm G t1 -> tm G (Plus t1 t2)
  | Inr : forall G (t1 t2:typ),
      tm G t2 -> tm G (Plus t1 t2)
  | Case : forall G (t1 t2 t:typ),
      tm G (Plus t1 t2) -> tm (t1::G) t -> tm (t2::G) t -> tm G t
  | Unit : forall G, tm G One
  | Fst : forall G (t1 t2:typ),
      tm G (Prod t1 t2) -> tm G t1
  | Snd : forall G (t1 t2:typ),
      tm G (Prod t1 t2) -> tm G t2
  | Pair : forall G (t1 t2:typ),
      tm G t1 -> tm G t2 -> tm G (Prod t1 t2)
  | Abs : forall G (t1 t2:typ),
      tm (t1::G) t2 -> tm G (Arr t1 t2)
  | App : forall G (t1 t2:typ),
      tm G (Arr t1 t2) -> tm G t1 -> tm G t2
  .

  Program Definition weaken_var_l : forall G1 G2 t,
      var G2 t -> var (G1 ++ G2) t.
  induction G1; intros; cbn in *.
  - assumption.
  - apply VarS. apply IHG1. assumption.
  Defined.

  Program Definition weaken_var_r : forall G1 G2 t,
      var G1 t -> var (G1 ++ G2) t.
  intros. revert G2.
  induction H; intros; cbn in *.
  - apply VarZ.
  - apply VarS. auto.
  Defined.

  Program Definition swap_var : forall G (u1 u2 t:typ),
      var ([u1] ++ [u2] ++ G) t ->
      var ([u2] ++ [u1] ++ G) t.
  intros.
  cbn in *.
  inversion H; subst.
  - apply VarS. apply VarZ.
  - inversion H3; subst.
    * apply VarZ.
    * apply VarS. apply VarS. assumption.
  Defined.

  Program Definition exchange_var_r : forall G1 G2 (u1 u2 t:typ),
      var ([u1] ++ G1 ++ [u2] ++ G2) t ->
      var ([u2] ++ G1 ++ [u1] ++ G2) t.                                           
  induction G1; intros.
  - apply swap_var. apply H.
  - replace ([u2] ++ (a::G1) ++ [u1] ++ G2) with ([u2] ++ [a] ++ G1 ++ [u1] ++ G2) by reflexivity.
    replace ([u1] ++ (a::G1) ++ [u2] ++ G2) with ([u1] ++ [a] ++ G1 ++ [u2] ++ G2) in H by reflexivity.
    apply swap_var.
    apply swap_var in H.
    inversion H; subst.
    + apply VarZ.
    + apply VarS. apply IHG1. apply H3.
  Defined.

  Program Definition exchange_var : forall G1 G2 G3 (u1 u2 t:typ),
      var (G1 ++ [u1] ++ G2 ++ [u2] ++ G3) t ->
      var (G1 ++ [u2] ++ G2 ++ [u1] ++ G3) t.                                           
  induction G1; intros.
  - apply exchange_var_r. apply H.
  - inversion H; subst.
    + apply VarZ.
    + cbn. apply VarS. apply IHG1. assumption.
  Defined.

  Program Definition exchange_tm : forall G1 G2 G3 (u1 u2 t:typ),
      tm (G1 ++ [u1] ++ G2 ++ [u2] ++ G3) t ->
      tm (G1 ++ [u2] ++ G2 ++ [u1] ++ G3) t.                                           
  intros.
  remember (G1 ++ [u1] ++ G2 ++ [u2] ++ G3) as G.
  revert G1 G2 G3 u1 u2 HeqG.
  induction H; intros.
  - apply Const.
  - apply Var. apply exchange_var. subst. assumption.
  - apply Err. apply IHtm; assumption.
  - eapply Inl; eauto.
  - eapply Inr; eauto.
  - eapply Case with (t1:=t1) (t2:=t2).
    + apply IHtm1. assumption.
    + replace (t1 :: G1 ++ [u2] ++ G2 ++ [u1] ++ G3) with ((t1 :: G1) ++ [u2] ++ G2 ++ [u1] ++ G3) by reflexivity.
      apply IHtm2. subst. reflexivity.
    + replace (t2 :: G1 ++ [u2] ++ G2 ++ [u1] ++ G3) with ((t2 :: G1) ++ [u2] ++ G2 ++ [u1] ++ G3) by reflexivity.
      apply IHtm3. subst. reflexivity.
  - apply Unit; eauto.
  - eapply Fst; eauto.
  - eapply Snd; eauto.
  - eapply Pair; eauto.
  - eapply Abs.
    replace (t1 :: G1 ++ [u2] ++ G2 ++ [u1] ++ G3) with ((t1 :: G1) ++ [u2] ++ G2 ++ [u1] ++ G3) by reflexivity.
    apply IHtm. subst; reflexivity.
  - eapply App; eauto.
  Defined.

  Program Definition promote_var : forall G1 G2 u t,
      var (G1 ++ [u] ++ G2) t ->
      var ([u] ++ G1 ++ G2) t.
  induction G1; intros.
  - apply H.
  - inversion H; subst.
    + apply VarS. apply VarZ.
    + replace ([u] ++ (a :: G1) ++ G2) with ([u] ++ [a] ++ G1 ++ G2) by reflexivity.
      apply swap_var. apply VarS. apply IHG1. apply H3.
  Defined.
  
  Program Definition promote_tm : forall G1 G2 u t,
      tm (G1 ++ [u] ++ G2) t ->
      tm ([u] ++ G1 ++ G2) t.
  intros.
  remember (G1 ++ [u] ++ G2) as G.
  revert G1 G2 u HeqG.
  induction H; intros.
  - apply Const.
  - apply Var. apply promote_var. subst. assumption.
  - apply Err. apply IHtm; assumption.
  - eapply Inl; eauto.
  - eapply Inr; eauto.
  - eapply Case with (t1:=t1) (t2:=t2).
    + apply IHtm1. assumption.
    + subst.
      specialize (IHtm2 (t1 :: G1) G2 u eq_refl). 
      replace (t1 :: [u] ++ G1 ++ G2) with ([] ++ [t1] ++ [] ++ [u] ++ G1 ++ G2) by reflexivity.
      apply exchange_tm.
      apply IHtm2.
    + subst.
      specialize (IHtm3 (t2 :: G1) G2 u eq_refl). 
      replace (t2 :: [u] ++ G1 ++ G2) with ([] ++ [t2] ++ [] ++ [u] ++ G1 ++ G2) by reflexivity.
      apply exchange_tm.
      apply IHtm3.
  - apply Unit.
  - eapply Fst. eauto.
  - eapply Snd. eauto.
  - eapply Pair; eauto.
  - eapply Abs.
    replace (t1 :: [u] ++ G1 ++ G2) with ([] ++ [t1] ++ [] ++ [u] ++ G1 ++ G2) by reflexivity.
    apply exchange_tm.
    subst.
    apply (IHtm (t1::G1) G2 u eq_refl).
  - eapply App; eauto.
  Defined.

  
  Program Definition weaken_l : forall G1 G2 (t:typ), tm G2 t -> tm (G1 ++ G2)  t.
  intros G1 G2 t H.
  revert G1.
  induction H; intros.
  - apply Const.
  - apply Var. apply weaken_var_l. assumption.
  - apply Err. auto.
  - eapply Inl; eauto.
  - eapply Inr; eauto.
  - eapply Case with (t1:=t1) (t2:=t2).
    + apply IHtm1. 
    + apply promote_tm. apply IHtm2.
    + apply promote_tm. apply IHtm3.
  - apply Unit; eauto.
  - eapply Fst; eauto.
  - eapply Snd; eauto.
  - eapply Pair; eauto.
  - eapply Abs.
    apply promote_tm. auto.
  - eapply App; eauto.
  Defined.
  
  Program Definition weaken_r : forall G1 G2 (t:typ), tm G1 t -> tm (G1 ++ G2)  t.
  intros G1 G2 t H.
  revert G2.
  induction H; intros.
  - apply Const.
  - apply Var. apply weaken_var_r. assumption.
  - apply Err. auto.
  - eapply Inl; eauto.
  - eapply Inr; eauto.
  - eapply Case with (t1:=t1) (t2:=t2); eauto.
  - apply Unit; eauto.
  - eapply Fst; eauto.
  - eapply Snd; eauto.
  - eapply Pair; eauto.
  - eapply Abs. cbn in IHtm. auto.
  - eapply App; eauto.
 Defined.

  Program Definition weaken_var_mid : forall G1 G2 G3 (t:typ),
      var (G1 ++ G2) t -> var (G1 ++ G3 ++ G2) t.
  intros G1 G2 G3 t H.
  remember (G1 ++ G2) as G.
  revert G1 G2 G3 HeqG.
  induction H; intros.
  - destruct G1.
    + destruct G2; inversion HeqG; subst.
      cbn. eapply weaken_var_l. apply VarZ.
    + inversion HeqG; subst.
      apply VarZ.
  - destruct G1.
    + cbn. simpl in HeqG. subst.
      replace (G3 ++ (u :: G)) with (G3 ++ [u] ++ G) by reflexivity.
      rewrite app_assoc. apply weaken_var_l. assumption.
    + inversion HeqG; subst.
      specialize (IHvar G1 G2 G3 eq_refl).
      simpl. apply VarS. assumption.
  Defined.
    
  
  Program Definition weaken_mid : forall G1 G2 G3 (t:typ),
      tm (G1 ++ G2) t -> tm (G1 ++ G3 ++ G2) t.
  intros G1 G2 G3 t H.
  remember (G1 ++ G2) as G.
  revert G1 G2 G3 HeqG.
  induction H; intros.
  - apply Const.
  - subst. apply Var. apply weaken_var_mid. assumption.
  - apply Err; eauto.
  - eapply Inl; eauto.
  - eapply Inr; eauto.
  - eapply Case with (t1:=t1) (t2:=t2); eauto.
    + subst. specialize (IHtm2 (t1::G1) G2 G3 eq_refl). apply IHtm2.
    + subst. specialize (IHtm3 (t2::G1) G2 G3 eq_refl). apply IHtm3.      
  - apply Unit; eauto.
  - eapply Fst; eauto.
  - eapply Snd; eauto.
  - eapply Pair; eauto.
  - eapply Abs.
    subst.
    specialize (IHtm (t1::G1) G2 G3 eq_refl). apply IHtm.
  - eapply App; eauto.
 Defined.

  Program Definition subst_var : forall G1 G2 t u,
      tm G2 t -> var (G1 ++ [t] ++ G2) u -> tm (G1 ++ G2) u.
  intros.
  remember (G1 ++ [t] ++ G2) as G.
  revert G1 G2 t H HeqG.
  induction H0; intros.
  - destruct G1; inversion HeqG; subst.
    + assumption.
    + eapply Var. apply VarZ.
  - destruct G1; inversion HeqG; subst; clear HeqG.
    + cbn. eapply Var. assumption.
    + specialize (IHvar G1 G2 t0 H eq_refl).
      replace ((t1 :: G1) ++ G2) with ([t1] ++ (G1 ++ G2)) by reflexivity.
      apply (weaken_mid [] (G1 ++ G2) [t1]). assumption.
  Defined.
  
  Program Definition subst : forall G1 G2 t u,
      tm G2 t -> tm (G1 ++ [t] ++ G2) u -> tm (G1 ++ G2) u.
  intros.
  remember (G1 ++ [t] ++ G2) as G.
  revert G1 G2 t H HeqG.
  induction H0; intros.
  - apply Const.
  - eapply subst_var. apply H. subst. assumption.
  - eapply Err. eauto.
  - eapply Inl; eauto.
  - eapply Inr; eauto.
  - eapply Case.
    + eapply IHtm1; eauto.
    + replace (t1 :: G1 ++ G2) with ((t1 :: G1) ++ G2) by reflexivity. 
      eapply IHtm2; eauto. subst. reflexivity.
    + replace (t2 :: G1 ++ G2) with ((t2 :: G1) ++ G2) by reflexivity. 
      eapply IHtm3; eauto. subst. reflexivity.
  - eapply Unit.
  - eapply Fst; eauto.
  - eapply Snd; eauto.    
  - eapply Pair; eauto.
  - eapply Abs.
    replace (t1 :: G1 ++ G2) with ((t1 :: G1) ++ G2) by reflexivity.
    eapply IHtm. apply H.
    subst; auto.
  - eapply App; eauto.
  Defined.

  
End STLC.

Module BNone : Base.
  Inductive void := .
  Definition B := void.
  Definition Const := void.
  Definition base_type (c:Const) : B := match c with end.
End BNone.

Module STLC_None := STLC(BNone).




