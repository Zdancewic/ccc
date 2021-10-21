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

(* A representation of _reflexive directed graphs_:
      - there is a set of elements that correspond to both nodes and edges
      - there is a map [src : elt -> elt] and [tgt : elt -> elt] that pick out the source and 
        target of an element 
      - an element e is a _node_ (a.k.a. a _vertex_) iff src e = tgt e = e
      - an element e is a _self loop_ if src e = tgt e
*)
Record graph : Type :=
  grp {
    elt : Type       (* elements: vertices / edges / arcs / self-loops *)
  ; src : Fun elt elt  (* source of an edge *)
  ; tgt : Fun elt elt  (* target of an edge *)

  ; src_src : src >>> src ⩯ src
  ; tgt_src : tgt >>> src ⩯ tgt
  ; src_tgt : src >>> tgt ⩯ src
  ; tgt_tgt : tgt >>> tgt ⩯ tgt
  }.

Definition vert (A:graph) (x : elt A) : Prop := (src A) x = x /\ (tgt A) x = x.


Record graph_morphism (A B : graph) : Type :=
  map {
    elt_map : Fun (elt A) (elt B)   (* maps edges to edges, but note that vertices are included in edges *)

  ; src_map : (src A >>> elt_map) ⩯ (elt_map >>> src B)
  ; tgt_map : (tgt A >>> elt_map) ⩯ (elt_map >>> tgt B)
  }.

Arguments elt_map {A B}.

Definition DGPH (A B : graph) : Type := graph_morphism A B.

Instance eq2_graph_morphism : Eq2 DGPH :=
  fun A B f g => (elt_map f ⩯ elt_map g).

Instance Proper_elt_map : forall A B, @Proper (graph_morphism A B -> _) (eq2 ==> eq2) elt_map. 
Proof.
  repeat intro. rewrite H. reflexivity.
Qed.  

Program Instance id_graph : Id_ DGPH :=
  fun A => map A A (fun e => e) _ _.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.
Next Obligation.
  intros e. unfold cat, Cat_Fun. reflexivity.
Qed.

Program Definition cat_graph (A B C : graph)
        (f : graph_morphism A B)
        (g : graph_morphism B C) : graph_morphism A C :=
  map A C  (elt_map f >>> elt_map g)
           _ _.
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

Instance Cat_DGPH : Cat DGPH := cat_graph.

Instance ProperCat_DGPH: forall A B C,
        @Proper (graph_morphism A B -> graph_morphism B C -> graph_morphism A C)
                (eq2 ==> eq2 ==> eq2) cat.
Proof.
  repeat intro.
  cbn; rewrite H; rewrite H0; reflexivity.
Qed.  


Program Definition ZERO : graph :=
  grp Empty_set
      (fun x => x)
      (fun x => x)      
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

Program Instance Initial_DGPH : Initial DGPH ZERO := 
  fun A => map ZERO A
            (fun x => match x with end)
            _ _.
Next Obligation. 
  intro a. inversion a.
Qed.
Next Obligation.
  intro a. inversion a.
Qed.

Program Definition ONE : graph :=
  grp unit
      (fun x => tt)
      (fun x => tt)
      _ _ _ _.
Next Obligation.
  intros a. destruct a. reflexivity.
Qed.
Next Obligation.
  intros a. destruct a. reflexivity.
Qed.
Next Obligation.
  intros a. destruct a. reflexivity.
Qed.
Next Obligation.
  intros a. destruct a. reflexivity.
Qed.

Program Instance Terminal_DGPH : Terminal DGPH ONE :=
  fun A => map A ONE
            (fun x => tt)
            _ _.
Next Obligation.
  intro a. reflexivity.
Qed.
Next Obligation.
  intro a. reflexivity.
Qed.

Variant elt_I : Type :=
| ss_I
| tt_I
| ee_I.

Definition src_I : Fun elt_I elt_I :=
      (fun x => match x with | ss_I => ss_I | tt_I => tt_I | ee_I => ss_I end).  

Definition tgt_I : Fun elt_I elt_I := 
  (fun x => match x with | ss_I => ss_I | tt_I => tt_I | ee_I => tt_I end).

Program Definition I : graph :=
  grp elt_I
      src_I
      tgt_I
      _ _ _ _.
Next Obligation.
  intro. destruct a; reflexivity.
Qed.
Next Obligation.
  intro. destruct a; reflexivity.
Qed.
Next Obligation.
  intro. destruct a; reflexivity.
Qed.
Next Obligation.
  intro. destruct a; reflexivity.
Qed.


Program Definition SUM (A:graph) (B:graph) : graph :=
  grp ((elt A) + (elt B))
      (case_ (src A >>> inl) (src B >>> inr))
      (case_ (tgt A >>> inl) (tgt B >>> inr))
      _ _ _ _.
Next Obligation.
  intro v. destruct v; cbn; unfold cat, Cat_Fun.
    - replace (src A (src A e)) with ((src A >>> src A) e) by reflexivity. rewrite (src_src A).
      reflexivity.
    - replace (src B (src B e)) with ((src B >>> src B) e) by reflexivity. rewrite (src_src B).
      reflexivity.
Qed.
Next Obligation.
  intro v. destruct v; cbn; unfold cat, Cat_Fun.
    - replace (src A (tgt A e)) with ((tgt A >>> src A) e) by reflexivity. rewrite (tgt_src A).
      reflexivity.
    - replace (src B (tgt B e)) with ((tgt B >>> src B) e) by reflexivity. rewrite (tgt_src B).
      reflexivity.
Qed.
Next Obligation.
  intro v. destruct v; cbn; unfold cat, Cat_Fun.
    - replace (tgt A (src A e)) with ((src A >>> tgt A) e) by reflexivity. rewrite (src_tgt A).
      reflexivity.
    - replace (tgt B (src B e)) with ((src B >>> tgt B) e) by reflexivity. rewrite (src_tgt B).
      reflexivity.
Qed.
Next Obligation.
  intro v. destruct v; cbn; unfold cat, Cat_Fun.
    - replace (tgt A (tgt A e)) with ((tgt A >>> tgt A) e) by reflexivity. rewrite (tgt_tgt A).
      reflexivity.
    - replace (tgt B (tgt B e)) with ((tgt B >>> tgt B) e) by reflexivity. rewrite (tgt_tgt B).
      reflexivity.
Qed.

Notation "A ⊕ B" := (SUM A B) (at level 85, right associativity).

Program Instance Case_DGPH : Case DGPH SUM :=
  fun A B C l r => map _ _
                    (case_ (elt_map l) (elt_map r))
                    _ _.
Next Obligation.
  intro e. destruct e; cbn.
  - replace (elt_map l (src A e)) with ((src A >>> elt_map l) e) by reflexivity.
    rewrite (src_map A). reflexivity.
  - replace (elt_map r (src B e)) with ((src B >>> elt_map r) e) by reflexivity.
    rewrite (src_map B). reflexivity.
Qed.
Next Obligation.
  intro e. destruct e; cbn.
  - replace (elt_map l (tgt A e)) with ((tgt A >>> elt_map l) e) by reflexivity.
    rewrite (tgt_map A). reflexivity.
  - replace (elt_map r (tgt B e)) with ((tgt B >>> elt_map r) e) by reflexivity.
    rewrite (tgt_map B). reflexivity.
Qed.
  
Program Instance Inl_DGPH : Inl DGPH SUM :=
  fun A B => map _ _ inl_ _ _.
Solve All Obligations with reflexivity.

Program Instance Inr_DGPH : Inr DGPH SUM :=
  fun A B => map _ _ inr_ _ _.
Solve All Obligations with reflexivity.

Instance CaseInl_DGPH : CaseInl DGPH SUM.
Proof.
  intros A B C f g. split.
Qed.

Instance CaseInr_DGPH : CaseInr DGPH SUM.
Proof.
  intros A B C f g. split.
Qed.

Instance CaseUniversal_DGPH : CaseUniversal DGPH SUM.
Proof.
  intros A B C f g fg H1 H2. 
  intro v. cbn. rewrite <- H1. rewrite <- H2. destruct v; reflexivity.
Qed.

Instance Case_DGPH_Proper :
  forall (A B C : graph),
    @Proper ((graph_morphism A C) -> (graph_morphism B C) -> (graph_morphism (A ⊕ B) C))
            (eq2 ==> eq2 ==> eq2) case_.
Proof.
  repeat intro.
  unfold eq2, eq2_graph_morphism in *.
  destruct x, y, x0, y0.   cbn in *.
  destruct a.
  - rewrite H. rewrite H0. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
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
    grp ((elt A) * (elt B))
        (bimap (src A) (src B))
        (bimap (tgt A) (tgt B))
        _ _ _ _.
  Next Obligation.
    rewrite bimap_cat.
    destruct A, B; cbn.
    rewrite src_src0.
    rewrite src_src1.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite bimap_cat.
    destruct A, B; cbn.
    rewrite tgt_src0.
    rewrite tgt_src1.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite bimap_cat.
    destruct A, B; cbn.
    rewrite src_tgt0.
    rewrite src_tgt1.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite bimap_cat.
    destruct A, B; cbn.
    rewrite tgt_tgt0.
    rewrite tgt_tgt1.
    reflexivity.
  Qed.
  
  Global Program Instance Pair_DGPH : Pair DGPH PROD :=
    fun A B C l r => map _ _
                    (pair_ (elt_map l) (elt_map r))
                    _ _.
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
  
  Global Program Instance Fst_DGPH : Fst DGPH PROD :=
    fun A B => map _ _ fst_ _ _.
  Solve All Obligations with reflexivity.

  Global Program Instance Snd_DGPH : Snd DGPH PROD :=
    fun A B => map _ _ snd_ _ _.
  Solve All Obligations with reflexivity.

  Global Instance PairFst_DGPH : PairFst DGPH PROD.
  Proof.
    intros a b c f g. split.
  Qed.

  Global Instance PairSnd_DGPH : PairSnd DGPH PROD.
  Proof.
    intros a b c f g. split.
  Qed.

  Global Instance PairUniversal_DGPH : PairUniversal DGPH PROD.
  Proof.
    intros a b c f g fg H G.
    destruct f, g, fg; 
    unfold eq2, eq2_graph_morphism in *; cbn in *.
    apply pair_universal; auto.
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
    rewrite H, H0. reflexivity.
  Qed.

  
  Program Global Instance Product_DGPH : Product DGPH PROD.

End Products.

Section CartesianClosed.

  Existing Instance Bimap_Product.
  Existing Instance Product_DGPH.
  Notation "A ⊗ B" := (PROD A B) (at level 80, right associativity).

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

  Definition const_id {A B C} (b:B) : Fun (A * C) (B * C) :=
    bimap (const b) (@id_  _ Fun _ _).

  Lemma bimap_f_id_const_id : forall {A D B C} (f : Fun A D) (b:B),
      (bimap f (@id_ _ Fun _ _)) >>> (const_id b) ⩯ ((const_id b) : Fun (A * C) (B * C)).
  Proof.
    intros.
    pose proof bimap_cat. apply H.
  Qed.

  Definition ss_map {A : graph} : Fun (elt (I ⊗ A)) (elt (I ⊗ A)) :=
    const_id ss_I.

  Definition tt_map {A : graph} : elt (I ⊗ A) -> elt (I ⊗ A) :=
    const_id tt_I.
  
  Definition ee_map {A : graph} : elt (I ⊗ A) -> elt (I ⊗ A) :=
    const_id ee_I.

  (* This lemma is almost certainly not true due to self-loops that aren't the identity. *)
  Lemma parametric : forall A B (f : graph_morphism (I ⊗ A) B),
      ss_map >>> (elt_map f) ⩯ tt_map >>> (elt_map f) ->
      ee_map >>> (elt_map f) ⩯ ss_map >>> (elt_map f).
  Proof.
  Abort.

  Definition elt_EXP (A B:graph) := 
    ((elt A -> elt B) + (graph_morphism (I ⊗ A) B))%type.

  Program Definition src_map_c {A B:graph} (f : graph_morphism (I ⊗ A) B) : graph_morphism A B :=
    map A B ((pair_ (const ss_I) (@id_ _ Fun _ _)) >>> elt_map f)
      _
      _.
  Next Obligation.
    destruct A, B, f. cbn in *.
    rewrite cat_assoc. rewrite <- src_map0.
    do 2 rewrite <- cat_assoc.
    rewrite pair_bimap.
    rewrite cat_id_l. reflexivity.
  Qed.    
  Next Obligation.
    destruct A, B, f. cbn in *.
    rewrite cat_assoc. rewrite <- tgt_map0.
    do 2 rewrite <- cat_assoc.
    rewrite pair_bimap.
    rewrite cat_id_l. reflexivity.
  Qed.

  Program Definition tgt_map_c {A B:graph} (f : graph_morphism (I ⊗ A) B) : graph_morphism A B :=
    map A B ((pair_ (const tt_I) (@id_ _ Fun _ _)) >>> elt_map f)
      _
      _.
  Next Obligation.
    destruct A, B, f. cbn in *.
    rewrite cat_assoc. rewrite <- src_map0.
    do 2 rewrite <- cat_assoc.
    rewrite pair_bimap.
    rewrite cat_id_l. reflexivity.
  Qed.    
  Next Obligation.
    destruct A, B, f. cbn in *.
    rewrite cat_assoc. rewrite <- tgt_map0.
    do 2 rewrite <- cat_assoc.
    rewrite pair_bimap.
    rewrite cat_id_l. reflexivity.
  Qed.

  Definition src_map_EXP {A B:graph} : Fun (elt_EXP A B) (elt_EXP A B) :=
    case_ inl_ (src_map_c >>> inl).

  Definition tgt_map_EXP {A B:graph} : Fun (elt_EXP A B) (elt_EXP A B) :=
    case_ inl_ (tgt_map_c >>> inl).

  Global Program Definition EXP (A:graph) (B:graph) : graph :=
    grp
      (elt_EXP A B)
      src_map_EXP
      tgt_map_EXP
      _ _ _ _
  .
  Next Obligation.
    repeat intro.
    destruct a; cbn; reflexivity.
  Qed.
  Next Obligation.
    repeat intro.
    destruct a; cbn; reflexivity.
  Qed.
  Next Obligation.
    repeat intro.
    destruct a; cbn; reflexivity.
  Qed.
  Next Obligation.
    repeat intro.
    destruct a; cbn; reflexivity.
  Qed.
  

  (** ** Cartesian closure. *)
  
   (*
     elt (EXP A B) = elt_EXP A B = (graph_morphism A B) + (graph_morphism (I ⊗ A) B)
   *)
  Definition apply_DGPH {A B : graph} : Fun (elt ((EXP A B) ⊗ A)) (elt B) := 
    (* elt ((EXP A B) ⊗ A) = (elt_EXP A B) * (elt A) = 
        ((graph_morphism A B) + (graph_morphism (I ⊗ A) B)) * (elt A) *)
    bimap (case_ elt_map (elt_map >>> pair_ curry_ (const ss_I) >>> apply_)) (id_ (elt A)) >>> apply_.

  Program Instance Apply_DGPH : Apply DGPH PROD EXP :=
    fun A B => map _ _
                (@apply_DGPH A B)
                _ _.
  Next Obligation. 
    unfold apply_DGPH, src_map_EXP.
    rewrite <- cat_assoc.
    rewrite bimap_cat. 
    rewrite pair_cat.
    rewrite f_const.
    rewrite cat_id_r.
    unfold src_map_c.
    intro.
    destruct a. destruct e; cbn.
    - unfold cat, Cat_Fun. cbn.
      destruct A, B, g; cbn in *. apply src_map0.
    - unfold cat, Cat_Fun. cbn.
      destruct A, B, g; cbn in *.
      unfold const, pair_, Pair_Fun, id_, Id_Fun.
      specialize (src_map0 (ss_I, e0)). apply src_map0.
 Qed.
  Next Obligation.
    unfold apply_DGPH, src_map_EXP.
    rewrite <- cat_assoc.
    rewrite bimap_cat. 
    rewrite pair_cat.
    rewrite f_const.
    rewrite cat_id_r.
    unfold tgt_map_c.
    intro.
    destruct a. destruct e; cbn.
    - unfold cat, Cat_Fun. cbn.
      destruct A, B, g; cbn in *. apply tgt_map0.
    - unfold cat, Cat_Fun. cbn.
      destruct A, B, g; cbn in *.
      unfold const, pair_, Pair_Fun, id_, Id_Fun.
      specialize (src_map0 (ss_I, e0)). apply src_map0.


    
    unfold tgt_map_c. unfold apply_DGPH.
    rewrite <- cat_assoc.
    rewrite bimap_cat. cbn.
    rewrite pair_cat.
    rewrite f_const.
    rewrite cat_id_r.
    unfold tt_map.
    intro. destruct a, g; cbn.
    unfold const_id, bimap, Bimap_Product, pair_, Pair_Fun, cat, Cat_Fun.  cbn.
    unfold const.
    replace (elt_map0 (tt_I, tgt A e)) with ((tgt (I ⊗ A) >>> elt_map0) (tt_I, e)) by reflexivity.
    rewrite tgt_map0.
    replace (tgt B (elt_map0 (ss_I, e))) with ((elt_map0 >>> tgt B) (ss_I, e)) by reflexivity.
