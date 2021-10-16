From Coq Require Import
     Relations.Relation_Definitions
     Classes.RelationClasses.

Definition lub {A : Type} (lt : relation A) (a b c : A) : Prop :=
  lt a c /\ lt b c /\ (forall d, lt a d -> lt b d -> lt c d).

Definition LT {A : Type} (lt : relation A) (X : A -> Prop) (a : A) :=
  forall x, X x -> lt x a.

Definition LUB {A : Type} (lt : relation A) (X : A -> Prop) (c : A) :=
  LT lt X c /\ (forall d, LT lt X d -> lt c d).

Definition chain {A : Type} (lt : relation A) := {f : nat -> A | forall i, lt (f i) (f (S i))}.
Definition elts {A : Type} {lt : relation A} (c : chain lt) (a : A) : Prop :=
  exists i, proj1_sig c i = a.

Definition complete {A : Type} (lt : relation A) : Prop :=
  forall (c:chain lt), exists (a:A), LUB lt (elts c) a.

Section CPO.
  Context {A : Type}.
  Class CPO (lt : relation A) :=
    {
    po :> PreOrder lt;
    cmp : complete lt;
    }.
End CPO.

Instance CPO_nat : CPO (fun (x y:nat) => x = y).
constructor.
constructor.
constructor.
repeat intro. subst; reflexivity.
intro. destruct c. exists (x 0).
repeat red. unfold LT, elts. split; intros.
- destruct H. cbn in H. subst. induction x1. reflexivity.
  rewrite <- e. assumption.
- apply H. exists 0. cbn. reflexivity.
Qed.

Section PreOrderEQ.
  Context {A : Type}.
  Context {lt : relation A}.
  Context {PR : PreOrder lt}.

  Definition pre_eq : relation A :=
    fun a b => lt a b /\ lt b a.

  Global Instance pre_eq_refl : Reflexive(pre_eq).
  Proof.
    destruct PR.
    constructor; reflexivity.
  Qed.

  Global Instance pre_eq_trans : Transitive(pre_eq).
  Proof.
    destruct PR.
    constructor; destruct H, H0; eapply transitivity; eauto.
  Qed.

  Global Instance pre_eq_symm : Symmetric(pre_eq).
  Proof.
    destruct PR.
    constructor; destruct H; tauto.
  Qed.
End PreOrderEQ.
  
    
          

Section Continuous.

  


  

  


  
  
  
  



Definition set (A:Type) := A -> Prop.

Definition dual {A : Type} (v : set A) : set A -> Prop :=
  fun (f : A -> Prop) => forall (a:A), v a <-> f a.

Definition join {A : Type} (X : set A -> Prop) : set A :=
  fun (a:A) => exists (g : A -> Prop), X g /\ g a.

Definition meet {A : Type} (X : set A -> Prop) : set A :=
  fun (a:A) => forall (g : A -> Prop), X g -> g a.

Definition meet_closed {A : Type} (v : set A) :=
  forall (a:A), v a <-> (meet (dual v) a).

Lemma all_meet_closed : forall A (v : set A), meet_closed v.
Proof.
  unfold meet_closed, meet, dual.
  intros.
  split; intros.
  - apply H0. assumption.
  - specialize (H v). apply H. tauto.
Qed.


Definition join_closed {A : Type} (v : set A) :=
  forall (a:A), v a <-> (join (dual v) a).

Lemma all_join_closed : forall A (v : set A), join_closed v.
Proof.
  unfold join_closed, join, dual.
  intros.
  split; intros.
  - exists v. split; tauto.
  - repeat destruct H. apply H. assumption.
Qed.    

Definition HRelation (A B : Type) := A -> B -> Prop.

Definition T' {A B : Type} (R : HRelation A B) : HRelation (A -> Prop) (B -> Prop) :=
  fun f g =>
    (forall a, f a -> exists b, R a b /\ g b) /\ (forall b, g b -> exists a, R a b /\ f a).

Definition T {A B : Type} (R : HRelation A B) : HRelation (A -> Prop) (B -> Prop) :=
  fun f g => forall a b, R a b <-> (f a) <-> (g b).



Definition TT {A B : Type} (R : HRelation A B) : HRelation A B :=
  fun a b => forall f g, (T R f g) -> (f a) <-> (g b).

Lemma R_TT: forall {A B : Type} (R : HRelation A B) a b (H : R a b), (TT R a b).
Proof.
  intros A B R.
  unfold TT, T.
  intros.
  split; intros.
    + eapply H0. split; intros. apply H1. auto.
    + apply H0 in H. assumption. assumption.
Qed.      
  
Definition TT_closed {A B : Type} (R : HRelation A B) :=
  forall a b, (TT R a b) -> R a b.

Definition rel {A B : Type} (f : A -> B) : HRelation A B :=
  fun a b => (f a) = b.

Lemma TT_closed_rel : forall A B (R : HRelation A B), TT_closed R.
Proof.
  intros A B R.
  unfold TT_closed, TT, T.
  intros.
  split; intros.
  - split; intros.
    + eapply H0. split; intros. apply H1. auto.
    + apply H0 in H. assumption. assumption.
  - specialize (H (fun x => R x b) (fun y => y = b)). cbn in *.
    apply H. intros. split. intros.


Lemma TT_closed_rel : forall A B (f : A -> B), TT_closed (rel f).
Proof.
  intros A B f.
  unfold TT_closed, TT, T, rel.
  intros.
  split; intros.
  - split; intros.
    + eapply H0. split; intros. apply H1. auto.
    + apply H0 in H. assumption. assumption.
  - 

Definition TT' {A B : Type} (R : HRelation A B) : HRelation A B :=
  fun a b => forall f g, (T' R f g) -> (f a) <-> (g b).

Definition TT'' {A B : Type} (R : HRelation A B) : HRelation A B :=
  fun a b => 



Definition TT'_closed {A B : Type} (R : HRelation A B) :=
  forall a b, R a b <-> (TT' R a b).


Lemma TT'_closed_rel : forall A B (f : A -> B), TT'_closed (rel f).
Proof.
  intros A B f.
  unfold TT'_closed, TT', T', rel.
  intros.
  split; intros.
  - split; intros.
    + subst. destruct H0. apply H in H1. destruct H1 as [b [Ha Hb]]. subst. assumption.
    + subst. destruct H0. apply H0 in H1. destruct H1 as [b [Ha Hb]]. subst. 


Lemma TT_closed_rel : forall A B (f : A -> B), TT_closed (rel f).
Proof.
  intros A B f.
  unfold TT_closed, TT, T, rel.
  intros.
  split; intros.
  - split; intros.
    + subst. eapply H0. reflexivity. assumption.
    + subst. eapply H0. reflexivity. assumption.
  - specialize (H (fun a' => True) (fun b' => b = b' -> f a = b)). 
    cbn in H.
    apply H; auto.
    intros. split; auto. intros. subst. 
    intros. subst. reflexivity.
                                            
