From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Category
     Basics.Function
     Basics.FunctionFacts.

Import CatNotations.
Local Open Scope cat_scope.

Record graph : Type :=
  grp {
    vrt : Type       (* vertices *)
  ; elt : Type       (* elements: edges / arcs / self-loops *)
  ; src : elt -> vrt  (* source of an edge *)
  ; tgt : elt -> vrt  (* target of an edge *)
  ; inc : vrt -> elt  (* vertices are included in edges (!) *)
                     (* this is useful to allow a morphism to contract an edge [e : s --> t]
                        to just a vertex:  the mapping  that sends an edge [e] to [inc s]  is
                        allowed in a morphism *)

  ; src_ok : (inc >>> src) ⩯ (@id_ _ Fun _ vrt)
  ; tgt_ok : (@id_ _ Fun _ elt) ⩯ (tgt >>> inc) 
  }.

Record graph_morphism (A B : graph) : Type :=
  map {
    vrt_map : vrt A -> vrt B   (* maps vertices to vertices *)
  ; elt_map : elt A -> elt B   (* maps edges to edges, but note that vertices are included in edges *)
                            
  ; src_map : (src A >>> vrt_map) ⩯ (elt_map >>> src B)
  ; tgt_map : (tgt A >>> vrt_map) ⩯ (elt_map >>> tgt B)
  ; inc_src : (inc A >>> src A >>> vrt_map) ⩯ (inc A >>> elt_map >>> src B)
  ; inc_tgt : (inc A >>> tgt A >>> vrt_map) ⩯ (inc A >>> elt_map >>> tgt B)
  }.

Arguments vrt_map {A B}.
Arguments elt_map {A B}.

Definition DGPH (A B : graph) : Type := graph_morphism A B.

Instance eq2_graph_morphism : Eq2 DGPH :=
  fun A B f g => (vrt_map f ⩯ vrt_map g) /\ (elt_map f ⩯ elt_map g).

Instance Proper_vrt_map : forall A B, @Proper (graph_morphism A B -> _) (eq2 ==> eq2) vrt_map. 
Proof.
  repeat intro. inversion H. rewrite H0. reflexivity.
Qed.  

Instance Proper_elt_map : forall A B, @Proper (graph_morphism A B -> _) (eq2 ==> eq2) elt_map. 
Proof.
  repeat intro. inversion H. rewrite H1. reflexivity.
Qed.  

Program Instance id_graph : Id_ DGPH :=
  fun A => map A A (fun v => v) (fun e => e) _ _ _ _.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.


Program Definition cat_graph (A B C : graph)
        (f : graph_morphism A B)
        (g : graph_morphism B C) : graph_morphism A C :=
  map A C  (vrt_map f >>> vrt_map g)
           (elt_map f >>> elt_map g)
           _ _ _ _.
Next Obligation.
  destruct f, g; cbn.
  rewrite <- cat_assoc.
  rewrite src_map0.
  rewrite cat_assoc.
  rewrite src_map1.
  rewrite cat_assoc.
  reflexivity.
Qed.  
Next Obligation.
  destruct f, g; cbn.
  rewrite <- cat_assoc.
  rewrite tgt_map0.
  rewrite cat_assoc.
  rewrite tgt_map1.
  rewrite cat_assoc.
  reflexivity.
Qed.
Next Obligation.
  destruct f, g; cbn.
  rewrite <- cat_assoc.
  rewrite inc_src0.
  rewrite cat_assoc.
  rewrite src_map1.
  rewrite <- cat_assoc.
  rewrite <- cat_assoc.
  reflexivity.
Qed.  
Next Obligation.
  destruct f, g; cbn.
  rewrite <- cat_assoc.
  rewrite inc_tgt0.
  rewrite cat_assoc.
  rewrite tgt_map1.
  rewrite <- cat_assoc.
  rewrite <- cat_assoc.
  reflexivity.
Qed.

Instance Cat_DGPH : Cat DGPH := cat_graph.

Instance ProperCat_DGPH: forall A B C,
        @Proper (graph_morphism A B -> graph_morphism B C -> graph_morphism A C)
                (eq2 ==> eq2 ==> eq2) cat.
Proof.
  repeat intro.
  split; cbn; rewrite H; rewrite H0; reflexivity.
Qed.  


Program Definition ZERO : graph :=
  grp Empty_set
      Empty_set
      (fun x => x)
      (fun x => x)
      (fun x => x)
      _ _.
Next Obligation.
  intro a. inversion a.
Qed.
Next Obligation.
  intro a. inversion a.
Qed.

Program Instance Initial_DGPH : Initial DGPH ZERO := 
  fun A => map ZERO A
            (fun x => match x with end)
            (fun x => match x with end)
            _ _ _ _.
Next Obligation. 
  intro a. inversion a.
Qed.
Next Obligation.
  intro a. inversion a.
Qed.
Next Obligation.
  intro a. inversion a.
Qed.
Next Obligation.
  intro a. inversion a.
Qed.

Program Definition ONE : graph :=
  grp unit
      unit
      (fun x => tt)
      (fun x => tt)
      (fun x => tt)
      _ _.
Next Obligation.
  intros a. destruct a. reflexivity.
Qed.
Next Obligation.
  intros a. destruct a. reflexivity.
Qed.

Program Instance Terminal_DGPH : Terminal DGPH ONE :=
  fun A => map A ONE
            (fun x => tt)
            (fun x => tt)
            _ _ _ _.
Next Obligation.
  intro a. reflexivity.
Qed.
Next Obligation.
  intro a. reflexivity.
Qed.
Next Obligation.
  intro a. reflexivity.
Qed.
Next Obligation.
  intro a. reflexivity.
Qed.

Program Definition SUM (A:graph) (B:graph) : graph :=
  grp ((vrt A) + (vrt B))
      ((elt A) + (elt B))
      (case_ (src A >>> inl) (src B >>> inr))
      (case_ (tgt A >>> inl) (tgt B >>> inr))
      (case_ (inc A >>> inl) (inc B >>> inr))
      _ _.
Next Obligation.
  intro v. destruct v; cbn; unfold cat, Cat_Fun.
    - replace (src A (inc A v)) with ((inc A >>> src A) v) by reflexivity. rewrite (src_ok A).
      reflexivity.
    - replace (src B (inc B v)) with ((inc B >>> src B) v) by reflexivity. rewrite (src_ok B).
      reflexivity.
Qed.
Next Obligation.
  intro v. destruct v; cbn; unfold cat, Cat_Fun.
    - replace (inc A (tgt A e)) with ((tgt A >>> inc A) e) by reflexivity. rewrite <- (tgt_ok A).
      reflexivity.
    - replace (inc B (tgt B e)) with ((tgt B >>> inc B) e) by reflexivity. rewrite <- (tgt_ok B).
      reflexivity.
Qed.

Notation "A ⊕ B" := (SUM A B) (at level 85, right associativity).

Program Instance Case_DGPH : Case DGPH SUM :=
  fun A B C l r => map _ _
                    (case_ (vrt_map l) (vrt_map r))
                    (case_ (elt_map l) (elt_map r))
                    _ _ _ _.
Next Obligation.
  intro e. destruct e; cbn.
  - replace (vrt_map l (src A e)) with ((src A >>> vrt_map l) e) by reflexivity.
    rewrite (src_map A). reflexivity.
  - replace (vrt_map r (src B e)) with ((src B >>> vrt_map r) e) by reflexivity.
    rewrite (src_map B). reflexivity.
Qed.
Next Obligation.
  intro e. destruct e; cbn.
  - replace (vrt_map l (tgt A e)) with ((tgt A >>> vrt_map l) e) by reflexivity.
    rewrite (tgt_map A). reflexivity.
  - replace (vrt_map r (tgt B e)) with ((tgt B >>> vrt_map r) e) by reflexivity.
    rewrite (tgt_map B). reflexivity.
Qed.
Next Obligation.
  intro e. destruct e; cbn.
  - replace (vrt_map l (src A (inc A v))) with ((inc A >>> src A >>> vrt_map l) v) by reflexivity.
    rewrite (inc_src A). reflexivity.
  - replace (vrt_map r (src B (inc B v))) with ((inc B >>> src B >>> vrt_map r) v) by reflexivity.
    rewrite (inc_src B). reflexivity.
Qed.
Next Obligation.
  intro e. destruct e; cbn.
  - replace (vrt_map l (tgt A (inc A v))) with ((inc A >>> tgt A >>> vrt_map l) v) by reflexivity.
    rewrite (inc_tgt A). reflexivity.
  - replace (vrt_map r (tgt B (inc B v))) with ((inc B >>> tgt B >>> vrt_map r) v) by reflexivity.
    rewrite (inc_tgt B). reflexivity.
Qed.
  
Program Instance Inl_DGPH : Inl DGPH SUM :=
  fun A B => map _ _ inl_ inl_ _ _ _ _.
Solve All Obligations with reflexivity.

Program Instance Inr_DGPH : Inr DGPH SUM :=
  fun A B => map _ _ inr_ inr_ _ _ _ _.
Solve All Obligations with reflexivity.

Instance CaseInl_DGPH : CaseInl DGPH SUM.
Proof.
  intros A B C f g.
  split; cbn; rewrite case_inl; reflexivity.
Qed.

Instance CaseInr_DGPH : CaseInr DGPH SUM.
Proof.
  intros A B C f g.
  split; cbn; rewrite case_inr; reflexivity.
Qed.

Instance CaseUniversal_DGPH : CaseUniversal DGPH SUM.
Proof.
  intros A B C f g fg H1 H2.
  inversion H1. inversion H2.
  split; cbn in *; rewrite <- case_universal; try reflexivity; try assumption.
Qed.  

Instance Case_DGPH_Proper :
  forall (A B C : graph),
    @Proper ((graph_morphism A C) -> (graph_morphism B C) -> (graph_morphism (A ⊕ B) C))
            (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro.
  unfold eq2, eq2_graph_morphism in *.
  destruct x, y, x0, y0.   cbn in *.
  split.
  - destruct H, H0. rewrite H. rewrite H0. reflexivity.
  - destruct H, H0. rewrite H1. rewrite H2. reflexivity.
Qed.
    
Instance Coproduct_DGPH : Coproduct DGPH SUM.
Proof.
  constructor.
  - exact CaseInl_DGPH.
  - exact CaseInr_DGPH.
  - exact CaseUniversal_DGPH.
  - exact Case_DGPH_Proper.
Qed.    


Section Products.
  Existing Instance Bimap_Product.

  Global Program Definition PROD (A:graph) (B:graph) : graph :=
    grp ((vrt A) * (vrt B))
        ((elt A) * (elt B))
        (bimap (src A) (src B))
        (bimap (tgt A) (tgt B))
        (bimap (inc A) (inc B))
        _ _.
  Next Obligation.
    rewrite bimap_cat.
    destruct A, B; cbn.
    rewrite src_ok0.
    rewrite src_ok1.
    rewrite bimap_id.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite bimap_cat.
    destruct A, B; cbn.
    rewrite <- tgt_ok0.
    rewrite <- tgt_ok1.
    rewrite bimap_id.
    reflexivity.
  Qed.

  Notation "A ⊗ B" := (PROD A B) (at level 80, right associativity).

  Global Program Instance Pair_DGPH : Pair DGPH PROD :=
    fun A B C l r => map _ _
                    (pair_ (vrt_map l) (vrt_map r))
                    (pair_ (elt_map l) (elt_map r))
                    _ _ _ _.
  Next Obligation.
    destruct l, r. cbn.  rewrite pair_universal.
    2: { rewrite cat_assoc. rewrite pair_fst. apply src_map0. }
    2: { rewrite cat_assoc. rewrite pair_snd. apply src_map1. }
    rewrite pair_bimap. reflexivity.
  Qed.
  Next Obligation.
    destruct l, r. cbn.  rewrite pair_universal.
    2: { rewrite cat_assoc. rewrite pair_fst. apply tgt_map0. }
    2: { rewrite cat_assoc. rewrite pair_snd. apply tgt_map1. }
    rewrite pair_bimap. reflexivity.
  Qed.
  Next Obligation.
    destruct l, r. cbn.  rewrite pair_universal.
    2: { rewrite cat_assoc. rewrite pair_fst. apply inc_src0. }
    2: { rewrite cat_assoc. rewrite pair_snd. apply inc_src1. }
    do 3 rewrite cat_assoc.
    rewrite pair_bimap. reflexivity.
  Qed.
  Next Obligation.
    destruct l, r. cbn.  rewrite pair_universal.
    2: { rewrite cat_assoc. rewrite pair_fst. apply inc_tgt0. }
    2: { rewrite cat_assoc. rewrite pair_snd. apply inc_tgt1. }
    do 3 rewrite cat_assoc.
    rewrite pair_bimap. reflexivity.
  Qed.
  
  Global Program Instance Fst_DGPH : Fst DGPH PROD :=
    fun A B => map _ _ fst_ fst_ _ _ _ _.
  Solve All Obligations with reflexivity.

  Global Program Instance Snd_DGPH : Snd DGPH PROD :=
    fun A B => map _ _ snd_ snd_ _ _ _ _.
  Solve All Obligations with reflexivity.

  Global Instance PairFst_DGPH : PairFst DGPH PROD.
  Proof.
    intros a b c f g. split; cbn; rewrite pair_fst; reflexivity.
  Qed.

  Global Instance PairSnd_DGPH : PairSnd DGPH PROD.
  Proof.
    intros a b c f g. split; cbn; rewrite pair_snd; reflexivity.
  Qed.

  Global Instance PairUniversal_DGPH : PairUniversal DGPH PROD.
  Proof.
    intros a b c f g fg H G.
    inversion H as (Hv & He). inversion G as (Gv & Ge).
    destruct f, g, fg; cbn in *.
    split; cbn.
    - rewrite <- pair_universal.
      2 : { apply Hv. }
      reflexivity. apply Gv.
    - rewrite <- pair_universal.
      2 : { apply He. }
      reflexivity. apply Ge.
 Qed.

  Global Instance Pair_DGPH_Proper :
  forall (A B C : graph),
    @Proper ((graph_morphism A B) -> (graph_morphism A C) -> (graph_morphism A (B ⊗ C)))
            (eq2 ==> eq2 ==> eq2) pair_.
  Proof.
    repeat intro.
    unfold eq2, eq2_graph_morphism in *.
    destruct x, y, x0, y0.   cbn in *.
    split.
    - destruct H, H0. rewrite H. rewrite H0. reflexivity.
    - destruct H, H0. rewrite H1. rewrite H2. reflexivity.
  Qed.

  
  Program Global Instance Product_DGPH : Product DGPH PROD.

End Products.
    
  
Section CartesianClosed.

  Existing Instance Bimap_Product.

  (*
    Cartesian closure:  
      We can build a graph that represents DGPH A B
        vertices are graph morphisms from graph A to graph B
           given f, g : graph_morphism A B
        there is an edge from f to g
           (elt A) 



    f : A ---------> B
        vrt_map : vrt A -> vrt B
        elt_map : elt A -> elt B



    g : A ---------> B
        vrt_map : vrt A -> vrt B
        elt_map : elt A -> elt B

  *)

  
  Global Program Definition EXP (A:graph) (B:graph) : graph :=
    grp
      (graph_morphism A B)
      _
      _
      _
      _ _ _
  .
      
  
  (** ** Cartesian closure. *)
(** The [exponential] is just [_ -> _], which is a just another name for [Fun] *)
Instance Apply_Fun : Apply Fun PROD Fun :=
    fun {A B} '(f, b) => f b.
  
Instance Curry_Fun : Curry Fun prod Fun :=
  fun {A B C} f => fun c a => f (c, a).
