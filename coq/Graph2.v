From Coq Require Import
     Morphisms
     FunctionalExtensionality
     ProofIrrelevance.

From ITree Require Import
     Basics.Category
     Basics.Function
     Basics.FunctionFacts.

Import CatNotations.
Local Open Scope cat_scope.

(* A representation of _directed graphs_:
      - there is a set of vertices
      - there is a set of edges
      - each edge has a source and target vertex
*)
Record graph : Type :=
  grp {
    vert : Type       (* vertices *)
  ; edge : Type       (* edges *)
  ; src : Fun edge vert  (* source of an edge *)
  ; tgt : Fun edge vert  (* target of an edge *)
  }.


Record graph_morphism (A B : graph) : Type :=
  map {
    vert_map : Fun (vert A) (vert B)   (* maps vertices to vertices *)
  ; edge_map : Fun (edge A) (edge B)   (* maps edges to edges *)                 

  ; src_map : edge_map >>> (src B) ⩯ (src A) >>> vert_map (* (src B (edge_map e)) = vert_map (src A e) *)
  ; tgt_map : edge_map >>> (tgt B) ⩯ (tgt A) >>> vert_map
  }.

Arguments vert_map {A B}.
Arguments edge_map {A B}.

Definition DGPH (A B : graph) : Type := graph_morphism A B.

Instance eq2_graph_morphism : Eq2 DGPH :=
  fun A B f g => (vert_map f ⩯ vert_map g) /\ (edge_map f ⩯ edge_map g).

Instance Proper_vert_map : forall A B, @Proper (graph_morphism A B -> _) (eq2 ==> eq2) vert_map. 
Proof.
  repeat intro. destruct x, y; cbn in *. apply H. 
Qed.  

Instance Proper_edge_map : forall A B, @Proper (graph_morphism A B -> _) (eq2 ==> eq2) edge_map. 
Proof.
  repeat intro. destruct x, y; cbn in *. apply H. 
Qed.  


Program Instance id_graph : Id_ DGPH :=
  fun A => map A A (@id_ _ _ _ (vert A)) (@id_ _ _ _ (edge A)) _ _.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.

Program Definition cat_graph (A B C : graph)
        (f : graph_morphism A B)
        (g : graph_morphism B C) : graph_morphism A C :=
  map A C  (vert_map f >>> vert_map g) (edge_map f >>> edge_map g)
           _ _.
Next Obligation.
  destruct f, g; cbn.
  rewrite cat_assoc.
  rewrite src_map1.
  do 2 rewrite <- cat_assoc.
  rewrite src_map0.
  reflexivity.
Qed.  
Next Obligation.
  destruct f, g; cbn.
  rewrite cat_assoc.
  rewrite tgt_map1.
  do 2 rewrite <- cat_assoc.
  rewrite tgt_map0.
  reflexivity.
Qed.

Instance Cat_DGPH : Cat DGPH := cat_graph.

Instance ProperCat_DGPH: forall A B C,
        @Proper (graph_morphism A B -> graph_morphism B C -> graph_morphism A C)
                (eq2 ==> eq2 ==> eq2) cat.
Proof.
  repeat intro. unfold eq2, eq2_graph_morphism in *.
  destruct x, y, x0, y0; cbn in *.
  destruct H, H0. split.
  - rewrite H, H0. reflexivity.
  - rewrite H1, H2. reflexivity.
Qed.  

Instance DGPH_CatIdL : CatIdL DGPH.
Proof.
  red.
  unfold eq2, eq2_graph_morphism.
  repeat intro.
  destruct f.  cbn. split; reflexivity.
Qed.  

Instance DGPH_CatIdR : CatIdR DGPH.
Proof.
  red.
  unfold eq2, eq2_graph_morphism.
  repeat intro.
  destruct f.  cbn. split; reflexivity.
Qed.

Instance DGPH_CatAssoc : CatAssoc DGPH.
Proof.
  red.
  unfold eq2, eq2_graph_morphism.
  repeat intro.
  destruct f, g, h.  cbn. split; reflexivity.
Qed.

Program Definition ZERO : graph :=
  grp Empty_set
      Empty_set
      (fun x => x)
      (fun x => x).

Program Instance Initial_DGPH : Initial DGPH ZERO := 
  fun A => map ZERO A
            (fun x => match x with end)
            (fun x => match x with end)
            _ _.
Next Obligation. 
  intro a. inversion a.
Qed.
Next Obligation.
  intro a. inversion a.
Qed.

Instance DGPH_InitialObject : InitialObject DGPH ZERO.
Proof.
  repeat intro.
  destruct f.
  split; intro; destruct a0.
Qed.  

Program Definition ONE : graph :=
  grp unit
      unit                                                                    
      (fun x => tt)
      (fun x => tt).

Program Instance Terminal_DGPH : Terminal DGPH ONE :=
  fun A => map A ONE
            (fun v => tt)
            (fun e => tt)
            _ _.
Next Obligation.
  intro a. reflexivity.
Qed.
Next Obligation.
  intro a. reflexivity.
Qed.

Instance DGPH_TerminalObject : TerminalObject DGPH ONE.
Proof.
  repeat intro.
  destruct f.
  split; repeat intro; cbn in *.
  - destruct (vert_map0 a0). reflexivity.
  - destruct (edge_map0 a0). reflexivity.
Qed.    
  
Program Definition SUM (A:graph) (B:graph) : graph :=
  grp ((vert A) + (vert B))
      ((edge A) + (edge B))
      (case_ (src A >>> inl_) (src B >>> inr_))
      (case_ (tgt A >>> inl_) (tgt B >>> inr_)).

Notation "A ⊕ B" := (SUM A B) (at level 85, right associativity).

Program Instance Case_DGPH : Case DGPH SUM :=
  fun A B C l r => map _ _
                    (case_ (vert_map l) (vert_map r))
                    (case_ (edge_map l) (edge_map r))                    
                    _ _.
Next Obligation.
  destruct l, r; cbn in *.
  rewrite <- bimap_case_unfold.
  rewrite bimap_case.
  rewrite <- src_map0.
  rewrite <- src_map1.
  rewrite <- cat_case.
  reflexivity.
Qed.  
Next Obligation.
  destruct l, r; cbn in *.
  rewrite <- bimap_case_unfold.
  rewrite bimap_case.
  rewrite <- tgt_map0.
  rewrite <- tgt_map1.
  rewrite <- cat_case.
  reflexivity.
Qed.
  
Program Instance Inl_DGPH : Inl DGPH SUM :=
  fun A B => map _ _ inl_ inl_ _ _.
Solve All Obligations with reflexivity.

Program Instance Inr_DGPH : Inr DGPH SUM :=
  fun A B => map _ _ inr_ inr_ _ _.
Solve All Obligations with reflexivity.

Instance CaseInl_DGPH : CaseInl DGPH SUM.
Proof.
  intros A B C f g. split; reflexivity.
Qed.

Instance CaseInr_DGPH : CaseInr DGPH SUM.
Proof.
  intros A B C f g. split; reflexivity.
Qed.

Instance CaseUniversal_DGPH : CaseUniversal DGPH SUM.
Proof.
  intros A B C f g fg H1 H2. 
  split.
  - intro v. cbn. rewrite <- H1. rewrite <- H2. destruct v; reflexivity.
  - intro v. cbn. rewrite <- H1. rewrite <- H2. destruct v; reflexivity.
Qed.

Instance Case_DGPH_Proper :
  forall (A B C : graph),
    @Proper ((graph_morphism A C) -> (graph_morphism B C) -> (graph_morphism (A ⊕ B) C))
            (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro.
  unfold eq2, eq2_graph_morphism in *.
  destruct x, y, x0, y0.   cbn in *.
  destruct H, H0.
  split.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite H1. rewrite H2. reflexivity.
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
    grp ((vert A) * (vert B))
        ((edge A) * (edge B))
        (bimap (src A) (src B))
        (bimap (tgt A) (tgt B)).
  
  Global Program Instance Pair_DGPH : Pair DGPH PROD :=
    fun A B C l r => map _ _
                    (pair_ (vert_map l) (vert_map r))                      
                    (pair_ (edge_map l) (edge_map r))
                    _ _.
  Next Obligation.
    destruct l, r. cbn. rewrite pair_bimap.
    rewrite src_map0. rewrite src_map1.
    rewrite <- pair_cat. reflexivity.
  Qed.
  Next Obligation.
    destruct l, r. cbn. rewrite pair_bimap.
    rewrite tgt_map0. rewrite tgt_map1.
    rewrite <- pair_cat. reflexivity.
  Qed.
    
  Global Program Instance Fst_DGPH : Fst DGPH PROD :=
    fun A B => map _ _ fst_ fst_ _ _.
  Solve All Obligations with reflexivity.

  Global Program Instance Snd_DGPH : Snd DGPH PROD :=
    fun A B => map _ _ snd_ snd_ _ _.
  Solve All Obligations with reflexivity.

  Global Instance PairFst_DGPH : PairFst DGPH PROD.
  Proof.
    intros a b c f g. split; reflexivity.
  Qed.

  Global Instance PairSnd_DGPH : PairSnd DGPH PROD.
  Proof.
    intros a b c f g. split; reflexivity.
  Qed.

  Global Instance PairUniversal_DGPH : PairUniversal DGPH PROD.
  Proof.
    intros a b c f g fg H G.
    destruct f, g, fg; 
    unfold eq2, eq2_graph_morphism in *; cbn in *.
    destruct H, G.
    split.
    - apply pair_universal; auto.
    - apply pair_universal; auto.
 Qed.

  Notation "A ⊗ B" := (PROD A B) (at level 80, right associativity).
  
  Global Instance Pair_DGPH_Proper :
  forall (A B C : graph),
    @Proper ((graph_morphism A B) -> (graph_morphism A C) -> (graph_morphism A (B ⊗ C)))
            (eq2 ==> eq2 ==> eq2) pair_.
  Proof.
    repeat intro.
    unfold eq2, eq2_graph_morphism in *.
    destruct x, y, x0, y0.   cbn in *.
    destruct H, H0.
    split.
    - rewrite H, H0. reflexivity.
    - rewrite H1, H2. reflexivity.
  Qed.

  
  Program Global Instance Product_DGPH : Product DGPH PROD.

End Products.

  Definition const {A B:Type} (b:B) : Fun A B :=
    fun _ => b.

  Lemma f_const : forall {A C B} (b:B) (f : Fun A C),
      f >>> const b ⩯ const b.
  Proof.
    intros. intros x. reflexivity.
  Qed.

  Lemma const_f : forall {A C B} (b:B) (f : Fun B C),
      const b >>> f ⩯ fun (_:A) => f b.
  Proof.
    intros. intros x. reflexivity.
  Qed.


Inductive vert_I : Type :=
| ss_I
| tt_I
.

Definition I : graph :=
  grp
    vert_I
    unit
    (const ss_I)
    (const tt_I).

Section CartesianClosed.

  Existing Instance Bimap_Product.
  Existing Instance Product_DGPH.
  Notation "A ⊗ B" := (PROD A B) (at level 80, right associativity).

  Definition const_id {A B C} (b:B) : Fun (A * C) (B * C) :=
    @bimap _ Fun prod _ _ _ _ _ (const b) (@id_  _ Fun _ _).

  Lemma bimap_f_id_const_id : forall {A D B C} (f : Fun A D) (b:B),
      (bimap f (@id_ _ Fun _ _)) >>> (const_id b) ⩯ ((const_id b) : Fun (A * C) (B * C)).
  Proof.
    intros.
    pose proof bimap_cat. apply H.
  Qed.

  
  (*
    Cartesian closure:  
      We can build a graph that represents DGPH A B
        vertices are graph morphisms from graph A to graph B
           given f, g : graph_morphism A B
      each edge from f to g is given by 
      h : graph_morphism (I ⊗ A) B
        s.t. h (ss_I, a) = f a
             h (tt_I, a) = g a


    f : A ---------> B
        elt_map : elt A -> elt B

              h

    g : A ---------> B
        elt_map : elt A -> elt B


    ==================
    given f : graph_morphism A B
    there is a canonical inclusion 

      f' : graph_morphism (I ⊗ A) B
      f |->  snd_ >>> f


   elt (EXP A B) == graph_morphism (I ⊗ A) B

   src_I * id >>> f' ⩯  tgt_I * id >>> f' ->
   forall ii jj, const_id ii >>> f' ⩯ const_id jj >>> f'


   *)
  

  Global Program Definition EXP (A:graph) (B:graph) : graph :=
    grp
      (Fun (vert A) (vert B))
      (graph_morphism (I ⊗ A) B)
      (vert_map >>> curry_ >>> pair_ (id_ _) (const ss_I) >>> apply_)
      (vert_map >>> curry_ >>> pair_ (id_ _) (const tt_I) >>> apply_)
  .
  

  (** ** Cartesian closure. *)
  
   (*
     elt (EXP A B) = elt_EXP A B = (graph_morphism A B) + (graph_morphism (I ⊗ A) B)
   *)

  Program Instance Apply_DGPH : Apply DGPH PROD EXP :=
    fun A B => map ((EXP A B) ⊗ A) B
                apply_
                (bimap (edge_map >>> curry_ >>> pair_ (id_ _) (const tt) >>> apply_)  (id_ _)  >>> apply_)
                _ _.
  Next Obligation. 
    repeat rewrite pair_cat.
    repeat rewrite cat_id_r.
    destruct A, B; cbn in *.
    intro.
    destruct a.
    destruct g; cbn in *.
    unfold cat, Cat_Fun. cbn.
    specialize (src_map0 (const tt (curry_ edge_map0), e)).
    unfold cat, Cat_Fun in src_map0.
    rewrite src_map0.
    unfold bimap, Bimap_Product, pair_, Pair_Fun.
    rewrite f_const.
    reflexivity.
  Qed.
  Next Obligation.
    repeat rewrite pair_cat.
    repeat rewrite cat_id_r.
    destruct A, B; cbn in *.
    intro.
    destruct a.
    destruct g; cbn in *.
    unfold cat, Cat_Fun. cbn.
    specialize (tgt_map0 (const tt (curry_ edge_map0), e)).
    unfold cat, Cat_Fun in tgt_map0.
    rewrite tgt_map0.
    unfold bimap, Bimap_Product, pair_, Pair_Fun.
    rewrite f_const.
    reflexivity.
  Qed.

(*  
Instance Curry_Fun : Curry Fun prod Fun :=
  fun {A B C} f => fun c a => f (c, a).
*)

  Program Instance Curry_DGPH : Curry DGPH PROD EXP :=
    fun A B C (m : graph_morphism (C ⊗ A) B) =>
      map C (EXP A B)
          (curry_ (vert_map m))
          (fun (ec : edge C) =>
             (map (I ⊗ A) B
                  (@bimap _ Fun prod _ _ _ _ _ (fun i => match i with ss_I => src C ec | tt_I => tgt C ec end) (id_ (vert A)) >>> (vert_map m))
                  (@bimap _ Fun prod _ _ _ _ _ (const ec) (id_ (edge A)) >>> (edge_map m))
                  _ _)
          )
          _ _.
  Next Obligation.
    rewrite <- cat_assoc.
    rewrite bimap_cat.
    rewrite const_f.
    destruct m. cbn.
    rewrite cat_assoc.
    rewrite src_map0.
    rewrite cat_id_r. reflexivity.
  Qed.
  Next Obligation.
    rewrite <- cat_assoc.
    rewrite bimap_cat.
    rewrite const_f.
    destruct m. cbn.
    rewrite cat_assoc.
    rewrite tgt_map0.
    rewrite cat_id_r. reflexivity.
  Qed.
  Next Obligation.
    intro. cbn.
    unfold const, id_, Id_Fun, cat, Cat_Fun. 
    destruct m.  cbn.
    unfold curry_, Curry_Fun.
    apply functional_extensionality.
    reflexivity.
  Qed.
  Next Obligation.
    intro. cbn.
    unfold const, id_, Id_Fun, cat, Cat_Fun. 
    destruct m.  cbn.
    unfold curry_, Curry_Fun.
    apply functional_extensionality.
    reflexivity.
  Qed.

  Program Instance CurryApply_DGPH : CurryApply DGPH PROD EXP.
  Next Obligation.
    unfold curry_, Curry_DGPH, apply_, Apply_DGPH.
    unfold eq2, eq2_graph_morphism.
    split.
    - cbn. rewrite <- bimap_pair_unfold. rewrite <- curry_apply. reflexivity. typeclasses eauto.
    - cbn. rewrite <- bimap_pair_unfold. rewrite <- cat_assoc. rewrite bimap_cat.
      repeat rewrite <- cat_assoc. destruct f. cbn.
      rewrite cat_id_l. intro. destruct a0. reflexivity. 
 Qed.

  (* Unfortunately, the definition of eq2 for the Fun category doesn't
     allow any non-trivial equivalences on the underlying sets, so 
     we can't prove properness.  We could reformuate the graph definitions
     in terms of Typ instead of Fun, but that seems like a big hassle,
     so I just axiomatized the idea that extensional equality of the
     two component maps of a graph morphism implies equality.
  *) 
  Axiom graph_morphism_equality :
    forall (A B : graph)
      (vert_map0 vert_map1 : Fun (vert A) (vert B))
      (edge_map0 edge_map1 : Fun (edge A) (edge B))
      (src_map0 : edge_map0 >>> (src B) ⩯ (src A) >>> vert_map0)
      (src_map1 : edge_map1 >>> (src B) ⩯ (src A) >>> vert_map1)
      (tgt_map0 : edge_map0 >>> (tgt B) ⩯ (tgt A) >>> vert_map0)
      (tgt_map1 : edge_map1 >>> (tgt B) ⩯ (tgt A) >>> vert_map1)
      (H1: vert_map0 ⩯ vert_map1)
      (H2: edge_map0 ⩯ edge_map1),
      map A B vert_map0 edge_map0 src_map0 tgt_map0 =
      map A B vert_map1 edge_map1 src_map1 tgt_map1.       
      
  Program Global Instance CartesianCloased_DGPH : CartesianClosed DGPH ONE PROD EXP.
  Next Obligation.
    repeat red. intros.
    split.
    - destruct x, y. cbn in *. inversion H. cbn in *.
      rewrite H0. reflexivity.
    - inversion H.
      intro.  cbn.
      apply graph_morphism_equality.
      rewrite H0. reflexivity.
      rewrite H1. reflexivity.
  Qed.
      
      
End CartesianClosed.
