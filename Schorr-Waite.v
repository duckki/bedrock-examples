(* ============================================================================
  The Schorr-Waite algorithm verified with Bedrock library
  (the Bedrock library can be found at http://plv.csail.mit.edu/bedrock/)
  Authors: Duckki Oe and Adam Chlipala
  Date: 7/15/2013
 * ========================================================================= *)
Set Implicit Arguments.
Require Import AutoSep Bags Sets SepPure.

(* ============================================================================
 * definitions for abstract object graphs
 * ========================================================================= *)

Record obj := {
  Address : W;
  Mark : bool;
  FirstChild : W;
  SecondChild : W
}.

Definition mark (o : obj) : obj := {|
  Address := Address o;
  Mark := true;
  FirstChild := FirstChild o;
  SecondChild := SecondChild o
|}.

Module Obj_Key.
  Definition A := obj.

  Theorem eq_dec : forall x y : A, {x = y} + {x <> y}.
    decide equality; try apply weq; decide equality.
  Qed.
End Obj_Key.

Module Obj_Set := Make(Obj_Key).
Import Obj_Set.
Export Obj_Set.

Definition noNull g := forall o, Address o = 0 -> ~ o %in g.

Definition functional (g : set) :=
  forall o1 o2, o1 %in g -> o2 %in g -> Address o1 = Address o2 -> o1 = o2.

Definition inDom (p : W) g := exists o, o %in g /\ Address o = p.

Definition Ptr (p : W) (g : set) := p = 0 \/ inDom p g.

Definition closed (g : set) :=
  forall o, o %in g -> Ptr (FirstChild o) g /\ Ptr (SecondChild o) g.

Definition heapInv g := noNull g /\ functional g /\ closed g.


(* ============================================================================
 * graph data structure
 * ========================================================================= *)

Definition objTag (b : bool) : W := if b then 2 else 0.

Definition objP (o : obj) : HProp :=
  (Address o ==*> objTag (Mark o), FirstChild o, SecondChild o)%Sep.

Module Type GRAPH.
  Parameter graph : set -> HProp.
  Axiom graph_intro : forall g, heapInv g
                                -> starS objP g ===> graph g.
  Axiom graph_elim : forall g, graph g ===> [| heapInv g |] * starS objP g.
End GRAPH.

Module Graph : GRAPH.
  Open Scope Sep_scope.

  Definition graph (g : set) := [| heapInv g |] * starS objP g.

  Theorem graph_intro : forall g, heapInv g
                                  -> starS objP g ===> graph g.
    unfold graph; simpl; intros.
    eapply Himp_trans; [eapply Himp_star_Emp' | ].
    eapply Himp_star_frame; try apply Himp_refl; sepLemma.
  Qed.

  Theorem graph_elim : forall g, graph g ===> [| heapInv g |] * starS objP g.
    unfold graph; simpl; intros; apply Himp_refl.
  Qed.
End Graph.

Import Graph.
Export Graph.


(* ============================================================================
 * function specification
 * ========================================================================= *)

Section reachable.
  Variable g : set.

  Inductive reachable : W -> obj -> Prop :=
  | ReachEq : forall o, o %in g -> Mark o = false
                  -> reachable (Address o) o
  | ReachFirst : forall o o', o %in g -> Mark o = false
                     -> reachable (FirstChild o) o'
                     -> reachable (Address o) o'
  | ReachSecond : forall o o', o %in g -> Mark o = false
                      -> reachable (SecondChild o) o'
                      -> reachable (Address o) o'.

  Definition marked (root : W) (g' : set) :=
    forall o, reachable root o -> mark o %in g'.

End reachable.

Definition markS := SPEC("root") reserving 2
  Al g,
  PRE[V]  graph g * [| Ptr (V "root") g |]
  POST[_] Ex g', graph g' * [| marked g (V "root") g' |].


(* ============================================================================
 * Set lemmas
 * ========================================================================= *)

Lemma mem_add_set : forall p q s, p %in s -> p %in s %+ q.
  sets.
Qed.

Lemma neq_mem_del : forall p q s, p <> q -> p %in s -> p %in s %- q.
  sets.
Qed.

Lemma neq_mem_add : forall p q s, p <> q -> p %in s %+ q -> p %in s.
  sets.
Qed.

Hint Resolve mem_add_set neq_mem_del.


(* ============================================================================
 * graph lemmas
 * ========================================================================= *)

Lemma heapInv_noNull : forall g, heapInv g -> noNull g.
  inversion 1; tauto.
Qed.

Lemma heapInv_functional : forall g, heapInv g -> functional g.
  inversion 1; tauto.
Qed.

Lemma heapInv_closed : forall g, heapInv g -> closed g.
  inversion 1; tauto.
Qed.

Hint Immediate heapInv_noNull heapInv_functional heapInv_closed.

Lemma null_Ptr : forall (p : W) g, p = 0 -> Ptr p g.
  left; auto.
Qed.
Hint Immediate null_Ptr.

Lemma inDom_Ptr : forall (p : W) g, inDom p g -> Ptr p g.
  right; auto.
Qed.
Hint Resolve inDom_Ptr.

Lemma Ptr_FirstChild : forall g x, closed g -> x %in g -> Ptr (FirstChild x) g.
  intros; apply H; auto.
Qed.

Lemma Ptr_SecondChild : forall g x, closed g -> x %in g -> Ptr (SecondChild x) g.
  intros; apply H; auto.
Qed.

Local Hint Resolve Ptr_FirstChild Ptr_SecondChild.

Lemma mem_inDom : forall o p g, Address o = p -> o %in g -> inDom p g.
  red; intros; eauto 3.
Qed.
Local Hint Immediate mem_inDom.

Lemma noNull_contra : forall g o, Address o = 0 -> noNull g -> o %in g -> False.
  intros; contradict H1; auto.
Qed.

Ltac ptrs :=
  match goal with
    | _ => solve [auto]
    | H: _ /\ _ |- _ => destruct H
    | H: inDom _ _ |- _ => destruct H as [? [] ]
    | H: ?o %in ?g, H1: forall _, _ |- _ => specialize (H1 _ H eq_refl)
    | |- _ => progress subst
    | H: Address ?x = Address ?x |- _ => clear H
    | H: Address ?x = Address ?y |- _ => assert (x = y) by auto
  end.

Lemma mark_not_in_del : forall g o,  o %in g -> functional g
                              -> ~ mark o %in (g %- o).
  intros; intro.
  assert (Address o = Address (mark o)) by auto; ptrs.
  rewrite <- H3 in *; destruct H1; congruence.
Qed.
Local Hint Resolve mark_not_in_del.


(*=============================================================================
 * updMark operator
 *===========================================================================*)

Definition updMark g o := (g %- o) %+ mark o.
Infix "%^" := updMark (at level 71, no associativity).

Lemma updMark_neq_mem : forall g o x, x %in g -> o <> x
                                      -> x %in (g %^ o).
  unfold "%^"; auto.
Qed.

Lemma updMark_neq_addr_mem : forall g o x, x %in g -> Address o <> Address x
                                      -> x %in (g %^ o).
  unfold "%^"; auto.
Qed.

Local Hint Resolve updMark_neq_mem updMark_neq_addr_mem.

Lemma updMark_mark_mem : forall g o, mark o %in (g %^ o).
  unfold "%^" in *; intros; sets.
Qed. 
Local Hint Resolve updMark_mark_mem.

Lemma updMark_neq_mem' : forall g o x, x %in (g %^ o) -> x <> mark o -> x %in g .
  intros; apply neq_mem_add in H; auto.
Qed.
Local Hint Resolve updMark_neq_mem'.

Lemma updMark_noNull : forall g o, noNull g -> Address o <> natToW 0
                                      -> noNull (g %^ o).
  red; intros; intro.
  destruct (Obj_Key.eq_dec o0 (mark o)); subst; auto.
  assert (o0 %in g) by eauto; eapply noNull_contra; eauto.
Qed.
Local Hint Resolve updMark_noNull.

Lemma updMark_functional : forall g o, o %in g -> functional g
                               -> functional (g %^ o).
  unfold functional; intros.
  destruct (Obj_Key.eq_dec o1 (mark o)); subst.
  destruct (Obj_Key.eq_dec o2 (mark o)); subst; auto.
  {
    exfalso; simpl in *.
    assert (o2 %in g) by eauto 3; repeat ptrs.
    apply neq_mem_add in H2; auto; sets.
  }
  {
    destruct (Obj_Key.eq_dec o2 (mark o)); subst.
    {
      exfalso; simpl in *.
      assert (o1 %in g) by eauto 3; repeat ptrs.
      apply neq_mem_add in H1; auto; sets.
    }
    apply neq_mem_add in H1; apply neq_mem_add in H2; auto.
  }
Qed.
Local Hint Resolve updMark_functional.

Lemma updMark_inDom : forall w g o, inDom w g -> inDom w (g %^ o).
  intros; repeat ptrs.
  destruct (Obj_Key.eq_dec x o); subst.
  exists (mark o); eauto.
  exists x; eauto.
Qed.
Local Hint Resolve updMark_inDom.

Lemma updMark_Ptr : forall w g o, Ptr w g -> Ptr w (g %^ o).
  destruct 1; auto.
Qed.
Local Hint Resolve updMark_Ptr.

Lemma updMark_closed : forall g o, o %in g -> closed g -> closed (g %^ o).
  red; intros.
  destruct (Obj_Key.eq_dec o0 (mark o)); subst; simpl; auto.
  apply neq_mem_add in H1; auto.
Qed.
Local Hint Resolve updMark_closed.


(* ============================================================================
 * [loop invariant] graph data structure
 * ========================================================================= *)

Module Type GRAPH'.
  Parameter objects : list W -> set -> HProp.
  Parameter graph' : list W -> set -> HProp.

  Axiom graph_fwd : forall g, graph g ===> graph' nil g.
  Axiom graph_bwd : forall g, graph' nil g ===> graph g.

  Axiom graph'_fwd : forall s g,
           graph' s g ===> [| heapInv g |] * objects s g.
  Axiom graph'_bwd : forall s g,
           [| heapInv g |] * objects s g ===> graph' s g.

  Definition objects_pick (_ : W) := objects.

  Axiom objects_reveal : forall (p : W) s g, p <> 0 -> Ptr p g -> ~ In p s
      -> objects_pick p s g
         ===> Ex o, [| o %in g |] * [| Address o = p |]
               * (p ==*> objTag (Mark o), FirstChild o, SecondChild o)
               * objects s (g %- o).

  Definition objects_filled (_:obj) (_:W) := objects.

  Axiom objects_fill : forall o p s g, Address o = p -> o %in g -> ~ In p s
          -> objects s (g %- o)
              * (Address o ==*> objTag (Mark o), FirstChild o, SecondChild o)
             ===> objects_filled o p s g.

  Definition objects_pushed (o : obj) := objects.

  Axiom objects_push : forall o p s g, Address o = p -> o %in g -> heapInv g
                    -> objects s (g %- o) ===> objects_pushed o (p :: s) g.

  Definition objects_popped (_:obj) (_:W) := objects.

  Axiom objects_pop : forall o p s g, heapInv g
      -> Address o = p -> o %in g -> NoDup (p :: s)
      -> objects (p :: s) g
           * (Address o ==*> objTag (Mark o), FirstChild o, SecondChild o)
          ===> objects_popped o p s g.

  Axiom objects_mark : forall p s g o, Address o = p -> o %in g -> heapInv g
             -> objects (p :: s) g ===> objects (p :: s) (g %^ o).
End GRAPH'.

Module Graph' : GRAPH'.
  Open Scope Sep_scope.

  Definition object (s : list W) (o : obj) : HProp :=
    if In_dec (@weq _) (Address o) s
      then Emp
      else Address o ==*> objTag (Mark o), FirstChild o, SecondChild o.

  Definition objects s := starS (object s).

  Definition graph' (s : list W) (g : set) := [| heapInv g |] * objects s g.

  Local Hint Resolve Himp_refl.

  Theorem graph_fwd : forall g, graph g ===> graph' nil g.
    unfold graph'; intros; eapply Himp_trans; [apply graph_elim | ]; auto.
  Qed.

  Theorem graph_bwd : forall g, graph' nil g ===> graph g.
    unfold graph'; sepLemma; eapply Himp_trans; [ | apply graph_intro; auto]; auto.
  Qed.

  Theorem graph'_fwd : forall s g, graph' s g ===> [| heapInv g |] * objects s g.
    unfold graph'; sepLemma.
  Qed.

  Theorem graph'_bwd : forall s g, [| heapInv g |] * objects s g ===> graph' s g.
    unfold graph'; sepLemma.
  Qed.

  (* --------------------------------------------------------------------------
   * accessing a pointer that is not in the stack
   * ----------------------------------------------------------------------- *)

  Lemma objects_reveal_h : forall o s g, o %in g
    -> objects s g ===> object s o * objects s (g %- o).
    intros; apply starS_del_fwd; auto.
  Qed.

  Definition objects_pick (_ : W) := objects.

  Theorem objects_reveal : forall (p : W) s g, p <> 0 -> Ptr p g -> ~ In p s
      -> objects_pick p s g
         ===> Ex o, [| o %in g |] * [| Address o = p |]
               * (p ==*> objTag (Mark o), FirstChild o, SecondChild o)
               * objects s (g %- o).
    unfold objects_pick; intros.
    destruct H0 as [ | [? [] ] ]; try congruence; subst.
    eapply Himp_trans; [apply objects_reveal_h; eauto | ].
    unfold object; destruct (In_dec (@weq _) (Address x) s); sepLemma.
  Qed.

  Lemma object_not_in_stack_bwd : forall o s, ~ In (Address o) s
    -> (Address o ==*> objTag (Mark o), FirstChild o, SecondChild o)
       ===> object s o.
    unfold object; intros.
    destruct (in_dec (@weq _) (Address o) s); try tauto; auto.
  Qed.
  Local Hint Resolve object_not_in_stack_bwd.

  Definition objects_filled (_:obj) (_:W) := objects.

  Local Hint Resolve Himp_star_comm Himp_star_frame.
  Local Hint Resolve Himp_trans starS_del_bwd.

  Theorem objects_fill : forall o p s g, Address o = p -> o %in g -> ~ In p s
          -> objects s (g %- o)
              * (Address o ==*> objTag (Mark o), FirstChild o, SecondChild o)
             ===> objects_filled o p s g.
    unfold objects; intros; subst.
    eapply Himp_trans; [ | eapply starS_del_bwd]; eauto.
  Qed.

  (* --------------------------------------------------------------------------
   * pushing an object into the stack
   * ----------------------------------------------------------------------- *)
  Lemma object_head : forall o s, object (Address o :: s) o = Emp.
    unfold object; simpl; intros.
    destruct (weq (Address o) (Address o)); intuition.
  Qed.

  Lemma objects_push_h : forall o p s g,
          Address o = p -> o %in g -> heapInv g
          -> objects s (g %- o) ===> objects (p :: s) g.
    intros; subst.
    eapply Himp_trans; [ | eapply starS_del_bwd ]; eauto.
    rewrite object_head.
    eapply Himp_trans; [ | apply Himp_star_Emp' ].
    apply starS_weaken; intros.
    assert (functional g) by auto.
    unfold object; simpl.
    destruct (weq (Address o) (Address x)).
    solve [repeat ptrs; sets].
    destruct (in_dec (@weq _) (Address x) s); auto.
  Qed.

  Definition objects_pushed (o : obj) := objects.

  Theorem objects_push : forall o p s g, Address o = p -> o %in g -> heapInv g
                    -> objects s (g %- o) ===> objects_pushed o (p :: s) g.
    intros; eapply Himp_trans; [ | apply objects_push_h; auto]; sepLemma.
  Qed.


  (* --------------------------------------------------------------------------
   * popping an object out of the stack
   * ----------------------------------------------------------------------- *)
  Lemma objects_pop_h : forall o p s g, heapInv g
    -> o %in g -> Address o = p -> ~ In p s
    -> objects (p :: s) g ===> objects s (g %- o).
    intros; subst.
    eapply Himp_trans; [ eapply starS_del_fwd; eauto| ].
    eapply Himp_trans; [apply Himp_star_frame | ].
    rewrite object_head; apply Himp_refl.
    2: apply Himp_star_Emp.
    apply starS_weaken; intros.
    assert (functional g) by auto.
    unfold object.
    destruct (in_dec (@weq _) (Address x) (Address o :: s)),
             (in_dec (@weq _) (Address x) s); try solve [sepLemma].
    solve [exfalso; inversion_clear i; try tauto; repeat ptrs; sets].
    destruct n; try tauto; simpl; auto.
  Qed.

  Definition objects_popped (_:obj) (_:W) := objects.

  Theorem objects_pop : forall o p s g, heapInv g
      -> Address o = p -> o %in g -> NoDup (p :: s)
      -> objects (p :: s) g
           * (Address o ==*> objTag (Mark o), FirstChild o, SecondChild o)
          ===> objects_popped o p s g.
    unfold objects_popped; inversion_clear 4; intros; subst.
    eapply Himp_trans; [ | eapply starS_del_bwd; eauto].
    eapply Himp_trans; [apply Himp_star_comm | ].
    apply Himp_star_frame, objects_pop_h; auto.
  Qed.


  (* --------------------------------------------------------------------------
   * marking an object in the stack
   * ----------------------------------------------------------------------- *)
  Lemma mark_object_in_stack : forall o s, In (Address o) s
    -> object s o = object s (mark o).
    unfold object; intros.
    destruct (in_dec (@weq _) (Address o) s),
             (in_dec (@weq _) (Address (mark o)) s); tauto.
  Qed.

  Lemma objects_mark_h : forall s g o, heapInv g
                     -> o %in g -> In (Address o) s
                     -> objects s g ===> objects s (g %^ o).
    intros.
    eapply Himp_trans; [apply objects_reveal_h; eauto | ].
    eapply Himp_trans; [apply Himp_star_frame; [ | apply Himp_refl] | ].
    rewrite mark_object_in_stack by auto; auto.
    eapply Himp_trans; [ | apply starS_add_bwd; auto]; auto.
  Qed.

  Theorem objects_mark : forall p s g o, Address o = p -> o %in g -> heapInv g
             -> objects (p :: s) g ===> objects (p :: s) (g %^ o).
    intros; apply objects_mark_h; auto; simpl; auto.
  Qed.

End Graph'.

Import Graph'.
Export Graph'.


(* ============================================================================
 * stack data structure
 * ========================================================================= *)

Definition stackInGraph (s : list W) (g : set) :=
  List.Forall (fun x => inDom x g) s.

Module Type STACK.
  Definition stackTag (b : bool) : W := if b then 2 else 1.

  Parameter stack : W -> list W -> set -> W -> HProp.
  Parameter stack' : W -> list W -> set -> W -> obj -> W -> W -> HProp.

  Axiom stack_pure : forall g s last p,
           stack last s g p ===> [| stackInGraph s g |] * stack last s g p.

  Axiom stack_nil_fwd : forall last s g (p : W), p = 0
    -> stack last s g p ===> [| s = nil |].
  
  Axiom stack_nil_bwd : forall last s g (p : W), p = 0
    -> [| s = nil |] ===> stack last s g p.

  Axiom stack_cons_fwd : forall last s g (p : W), p <> 0
    -> stack last s g p
       ===> (Ex s', [| s = p :: s' |] * [| p <> 0 |]
              * Ex o, [| o %in g |] * [| Address o = p |]
                 * Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
                                 * stack' last s' g p o p1 p2).

  Axiom stack_cons_bwd : forall last s g (p : W), p <> 0
      -> (Ex s', [| s = p :: s' |] * [| p <> 0 |]
           * Ex o, [| o %in g |] * [| Address o = p |]
              * Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
                              * stack' last s' g p o p1 p2)
         ===> stack last s g p.

  Axiom stack'_true_fwd : forall last p o p1 p2 s g, Mark o = true
      -> stack' last s g p o p1 p2
         ===> [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2.

  Axiom stack'_false_fwd : forall last p o p1 p2 s g, Mark o = false
      -> stack' last s g p o p1 p2
         ===> [| last = FirstChild o |] * [| p2 = SecondChild o |] * stack p s g p1.

  Axiom stack'_true_bwd : forall last p o p1 p2 s g, Mark o = true
      -> [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2
         ===> stack' last s g p o p1 p2.

  Axiom stack'_false_bwd : forall last p o p1 p2 s g, Mark o = false
      -> [| last = FirstChild o |] * [| p2 = SecondChild o |] * stack p s g p1
         ===> stack' last s g p o p1 p2.

  Axiom stack'_mark_bwd : forall last p o p1 p2 s g,
        [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2
        ===> stack' last s g p (mark o) p1 p2.

  Axiom stack_mark : forall s q g p o, NoDup (q :: s) -> Address o = q
                       -> stack q s g p ===> stack q s (g %^ o) p.

End STACK.

Module Stack : STACK.
  Open Scope Sep_scope.

  Definition stackTag (b : bool) : W := if b then 2 else 1.

  Fixpoint stack (last : W) (s : list W) (g : set) (p : W) : HProp :=
    match s with
      | nil => [| p = 0 |]
      | p' :: s => [| p' = p |] * [| p <> 0 |]
        * Ex o, [| o %in g |] * [| Address o = p |]
           * Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
              * if Mark o
                then [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2
                else [| last = FirstChild o |] * [| p2 = SecondChild o |] * stack p s g p1
    end.

  Definition stack' (last : W) s g p (o : obj) (p1 p2 : W) :=
    if Mark o
      then [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2
      else [| last = FirstChild o |] * [| p2 = SecondChild o |] * stack p s g p1.

  Ltac stack' := match goal with
                   | [ |- context C[ (Ex o, [| o %in ?g |] * [| Address o = ?p |]
                     * Ex p1, Ex p2, ?p =*> stackTag (Mark o) * ((?p ^+ $4) =*> p1 * (?p ^+ $8) =*> p2)
                     * if Mark o then [| p1 = FirstChild o |] * [| ?last = SecondChild o |] * stack ?p ?s ?g p2
                       else [| ?last = FirstChild o |] * [| p2 = SecondChild o |] * stack ?p ?s ?g p1)%Sep ] ] =>
                   let E := context C[(Ex o, [| o %in g |] * [| Address o = p |]
                     * Ex p1, Ex p2, p =*> stackTag (Mark o) * ((p ^+ $4) =*> p1 * (p ^+ $8) =*> p2)
                     * stack' last s g p o p1 p2)%Sep] in
                   change E
                 end.

  Local Hint Resolve Himp_refl.

  Theorem stack_pure : forall g s last p,
           stack last s g p ===> [| stackInGraph s g |] * stack last s g p.
    induction s; simpl; intros.
    solve [sepLemma; constructor].
    sepPure.
    destruct (Mark x) eqn:?; simpl; sepPure.
    {
      eapply Himp_trans.
      instantiate (1:=stack p s g x1 * (p ==*> natToW 2, x0, x1)); sepLemma.
      eapply Himp_trans; [apply Himp_star_frame; [apply IHs | ] | ]; auto.
      stack'; sepLemma; eauto; try apply Forall_cons; eauto.
      unfold stack'; rewrite Heqb; sepLemma.
    }
    {
      eapply Himp_trans.
      instantiate (1:=stack p s g x0 * (p ==*> natToW 1, x0, x1)); sepLemma.
      eapply Himp_trans; [apply Himp_star_frame; [apply IHs | ] | ]; auto.
      stack'; sepLemma; eauto; try apply Forall_cons; eauto.
      unfold stack'; rewrite Heqb; sepLemma.
    }
  Qed.

  Theorem stack_nil_fwd : forall last s g (p : W), p = 0
                            -> stack last s g p ===> [| s = nil |].
    destruct s; try (simpl; intros; stack'); sepLemma.
  Qed.

  Theorem stack_nil_bwd : forall last s g (p : W), p = 0
                            -> [| s = nil |] ===> stack last s g p.
    do 2 sepLemma.
  Qed.

  Theorem stack_cons_fwd : forall last s g (p : W), p <> 0
    -> stack last s g p
        ===> (Ex s', [| s = p :: s' |] * [| p <> 0 |]
               * Ex o, [| o %in g |] * [| Address o = p |]
                  * Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
                     * stack' last s' g p o p1 p2).
    destruct s; try (simpl; intros; stack'); sepLemma.
  Qed.

  Theorem stack_cons_bwd : forall last s g (p : W), p <> 0
    -> (Ex s', [| s = p :: s' |] * [| p <> 0 |]
         * Ex o, [| o %in g |] * [| Address o = p |]
            * Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
                * stack' last s' g p o p1 p2)
         ===> stack last s g p.
    destruct s; try (simpl; intros; stack'); sepLemma; eauto;
      match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; subst; sepLemma
      end.
  Qed.

  Theorem stack'_true_fwd : forall last p o p1 p2 s g, Mark o = true
      -> stack' last s g p o p1 p2
         ===> [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2.
    unfold stack'; intros; destruct (Mark o) eqn:?; sepLemma.
  Qed.

  Theorem stack'_false_fwd : forall last p o p1 p2 s g, Mark o = false
      -> stack' last s g p o p1 p2
         ===> [| last = FirstChild o |] * [| p2 = SecondChild o |] * stack p s g p1.
    unfold stack'; intros; destruct (Mark o) eqn:?; sepLemma.
  Qed.

  Theorem stack'_true_bwd : forall last p o p1 p2 s g, Mark o = true
      -> [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2
         ===> stack' last s g p o p1 p2.
    unfold stack'; intros; destruct (Mark o) eqn:?; sepLemma.
  Qed.

  Theorem stack'_false_bwd : forall last p o p1 p2 s g, Mark o = false
      -> [| last = FirstChild o |] * [| p2 = SecondChild o |] * stack p s g p1
         ===> stack' last s g p o p1 p2.
    unfold stack'; intros; destruct (Mark o) eqn:?; sepLemma.
  Qed.

  Theorem stack'_mark_bwd : forall last p o p1 p2 s g,
        [| p1 = FirstChild o |] * [| last = SecondChild o |] * stack p s g p2
        ===> stack' last s g p (mark o) p1 p2.
    unfold stack'; intros; destruct (Mark o) eqn:?; sepLemma.
  Qed.

  Lemma stack_mark_h : forall s q g p o, ~ In (Address o) s
                           -> stack q s g p ===> stack q s (g %^ o) p.
    induction s; simpl; try tauto; intros; auto.
    repeat stack'; sepLemma.
    unfold stack'; destruct (Mark x1) eqn:?; sepLemma.
  Qed.

  Theorem stack_mark : forall s q g p o, NoDup (q :: s) -> Address o = q
                       -> stack q s g p ===> stack q s (g %^ o) p.
    inversion_clear 1; intros; subst; apply stack_mark_h; auto.
  Qed.

End Stack.

Import Stack.


(*=============================================================================
 * stack with a hole
 *===========================================================================*)

Definition hints_stack : TacPackage.
  prepare (stack_nil_fwd, stack_cons_fwd, stack'_true_fwd, stack'_false_fwd)
          (stack_nil_bwd, stack_cons_bwd, stack'_false_bwd, stack'_true_bwd).
Defined.

Fixpoint stackH (q : W) (last : W) (s : list W) (g : set) (p : W) : HProp :=
  match s with
    | nil => [| False |]
    | p' :: s
      => [| p' = p |] * [| p <> 0 |]
         * Ex o, [| o %in g |] * [| Address o = p |]
            * if weq q p then
                Ex p1, Ex p2, (p ^+ $4) =*> p1 * (p ^+ $8) =*> p2
                 * stack' last s g p o p1 p2
             else
               Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
                * if Mark o
                  then [| p1 = FirstChild o |] * [| last = SecondChild o |]
                       * stackH q p s g p2
                  else [| last = FirstChild o |] * [| p2 = SecondChild o |]
                       * stackH q p s g p1
  end%Sep.

Definition stackH' q last s g p o p1 p2 : HProp := 
  (if Mark o
   then [| p1 = FirstChild o |] * [| last = SecondChild o |]
        * stackH q p s g p2
   else [| last = FirstChild o |] * [| p2 = SecondChild o |]
        * stackH q p s g p1)%Sep.

Lemma stackH_eq_bwd : forall q last s g p, q = p
            -> (Ex s' : list W, [| s = p :: s' |] * [| p <> 0 |]
                 * Ex o, [| o %in g |] * [| Address o = p |]
                    * Ex p1, Ex p2, (p ^+ $4) =*> p1 * (p ^+ $8) =*> p2
                       * stack' last s' g p o p1 p2)
               ===> stackH q last s g p.
  destruct s; intros; subst; simpl; [sepLemma | ].
  destruct (weq p p); try congruence; sepLemma; eauto 2.
  inversion H; clear H; subst; sepLemma.
Qed.

Ltac fold_stackH' :=
    match goal with
                   | [ |- context C[((Ex o : Obj_Key.A,
    [|o %in ?g|] * [|Address o = ?p|] *
    ((Ex p1 : W,
      (Ex p2 : W,
       ?p =*> stackTag (Mark o) * ((?p ^+ $ (4)) =*> p1 * (?p ^+ $ (8)) =*> p2) *
       (if Mark o
        then
         [|p1 = FirstChild o|] * [|?last = SecondChild o|] *
         stackH ?q ?p ?s ?g p2
        else
         [|?last = FirstChild o|] * [|p2 = SecondChild o|] *
         stackH ?q ?p ?s ?g p1))))))%Sep] ] =>
                   let E := context C[((Ex o : Obj_Key.A,
    [|o %in g|] * [|Address o = p|] *
    ((Ex p1 : W,
      (Ex p2 : W,
       p =*> stackTag (Mark o) * ((p ^+ $ (4)) =*> p1 * (p ^+ $ (8)) =*> p2) *
       stackH' q last s g p o p1 p2)))))%Sep] in
                   change E
                 end.

Lemma stackH_neq_fwd : forall q last s g p, q <> p -> In q s
            -> stackH q last s g p
               ===> Ex s', [| s = p :: s' |] * [| p <> 0 |]
                     * Ex o, [| o %in g |] * [| Address o = p |]
                        * Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
                           * stackH' q last s' g p o p1 p2.
  induction s; intros; subst; simpl; [sepLemma | ].
  destruct (weq q p); try congruence; fold_stackH'; sepLemma; eauto.
Qed.

Lemma stackH_neq_bwd : forall q last s g p, q <> p -> In q s
            -> (Ex s' : list W, [| s = p :: s' |] * [| p <> 0 |]
                     * Ex o, [| o %in g |] * [| Address o = p |]
                        * Ex p1, Ex p2, (p ==*> stackTag (Mark o), p1, p2)
                           * stackH' q last s' g p o p1 p2)
               ===> stackH q last s g p.
  induction s; intros; subst; simpl; [sepLemma | ].
  destruct (weq q p); try congruence; fold_stackH'; sepLemma; eauto.
  inversion H1; clear H1; subst; sepLemma.
Qed.

Theorem stackH'_true_fwd : forall q last p o p1 p2 s g, Mark o = true
    -> stackH' q last s g p o p1 p2
       ===> [| p1 = FirstChild o |] * [| last = SecondChild o |]
             * stackH q p s g p2.
  unfold stackH'; intros; destruct (Mark o) eqn:?; sepLemma.
Qed.

Theorem stackH'_false_fwd : forall q last p o p1 p2 s g, Mark o = false
    -> stackH' q last s g p o p1 p2
       ===> [| last = FirstChild o |] * [| p2 = SecondChild o |]
             * stackH q p s g p1.
  unfold stackH'; intros; destruct (Mark o) eqn:?; sepLemma.
Qed.

Theorem stackH'_true_bwd : forall q last p o p1 p2 s g, Mark o = true
    -> [| p1 = FirstChild o |] * [| last = SecondChild o |] * stackH q p s g p2
       ===> stackH' q last s g p o p1 p2.
  unfold stackH'; intros; destruct (Mark o) eqn:?; sepLemma.
Qed.

Theorem stackH'_false_bwd : forall q last p o p1 p2 s g, Mark o = false
    -> [| last = FirstChild o |] * [| p2 = SecondChild o |] * stackH q p s g p1
       ===> stackH' q last s g p o p1 p2.
  unfold stackH'; intros; destruct (Mark o) eqn:?; sepLemma.
Qed.

Ltac stack :=
  match goal with
    | _ => reflexivity
    | _ => congruence
    | _ => solve [auto]

    | H: _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
    | H: functional _, H': Address _ = Address _ |- _
      => progress (apply H in H'; auto)
    | H: In _ nil |- _ => solve [inversion H]
    | H: In _ (_ :: _) |- _ => inversion H; clear H; subst
  end.

Local Hint Resolve Himp_refl.

Lemma stack_reveal_h : forall g o s (p last : W), In (Address o) s
                           -> o %in g -> Address o <> 0 -> functional g
                           -> stack last s g p
                         ===> stackH (Address o) last s g p
                              * Address o =*> stackTag (Mark o).
  induction s; [sepLemma | intros].
  destruct (weq p (natToW 0)); red; intros; step hints_stack; repeat stack.
  {
    subst; eapply Himp_trans; [ | apply Himp_star_frame; [ | apply Himp_refl] ].
    2: apply stackH_eq_bwd; simpl; auto.
    sepLemma.
  }
  destruct (weq (Address x1) (Address o)); subst; repeat ptrs.
  {
    eapply Himp_trans.
    2: apply Himp_star_frame; [apply stackH_eq_bwd; auto | apply Himp_refl ].
    red; intro; step hints_stack; repeat stack.
  }
  {
    eapply Himp_trans; [ | apply Himp_star_frame; [ | apply Himp_refl] ].
    2: apply stackH_neq_bwd; simpl; auto.
    sepLemma.
    (* case split on (Mark x1) to open up stack' *)
    destruct (Mark x1) eqn:Hmark; subst; unfold stackH'; step hints_stack;
    rewrite Hmark; sepLemma; inversion_clear H;
    eapply Himp_trans; try (red; apply IHs); auto.
  }
Qed.

Lemma in_stack_inDom : forall s g q, stackInGraph s g -> In q s -> inDom q g.
  induction 1; intros; subst; repeat stack.
Qed.

Definition stack_pick (_:W) := stack.

Theorem stack_reveal : forall g s (p last q : W), q <> 0 -> In q s -> heapInv g
                           -> stack_pick q last s g p
                         ===> Ex o, [| o %in g |] * [| Address o = q |]
                               * [| In q s |] * q =*> stackTag (Mark o)
                               * stackH q last s g p.
  unfold stack_pick; intros.
  eapply Himp_trans; [apply stack_pure | ]; sepPure.
  edestruct in_stack_inDom as [? [] ]; eauto 2.
  subst; eapply Himp_trans; [apply stack_reveal_h; eauto | ]; sepLemma.
Qed.

Definition stack_filled (_:obj) := stack.

Theorem stack_fill : forall o g s (p last : W), o %in g -> heapInv g
     -> stackH (Address o) last s g p * Address o =*> stackTag (Mark o)
        ===> stack_filled o last s g p.
  induction s; unfold stack_filled; simpl; intros; [ solve [sepLemma] | ].
  assert (functional g) by auto.
  destruct (weq (Address o) p); subst; autorewrite with N.
  {
    sepLemma; repeat ptrs.
    destruct (Mark o) eqn:Heq; repeat step hints_stack; rewrite Heq; sepLemma.
  }
  {
    fold_stackH'; sepLemma.
    unfold stackH'; destruct (Mark x1) eqn:Heq; repeat step hints_stack;
    rewrite Heq; sepLemma.
  }
Qed.

Definition hints : TacPackage.
  prepare (graph_fwd, graph'_fwd, objects_reveal,
           stack_nil_fwd, stack_cons_fwd, stack'_true_fwd, stack'_false_fwd,
           stackH_neq_fwd, stackH'_true_fwd, stackH'_false_fwd,
           stack_reveal)
          (graph_bwd, graph'_bwd,
           objects_fill, objects_push, objects_pop, objects_mark, stack_mark,
           stack_nil_bwd, stack_cons_bwd, stack'_false_bwd, stack'_true_bwd,
           stack'_mark_bwd,
           stackH'_true_bwd, stackH'_false_bwd,
           stack_fill).
Defined.


(* ============================================================================
 * implementation
 * ========================================================================= *)

Definition markedS g s g' := List.Forall (fun p => marked g p g') s.
Definition stayMarked g g' := forall o, o %in g -> Mark o = true -> o %in g'.

Inductive sharing := sharingI.
Inductive pushCase := pushCaseI.

Definition m := bmodule "mark" {{
  bfunction "mark"("root", "prev", "tmp") [markS]
    "prev" <- 0;;
    [ Al g, Al s,
      PRE[V]  graph' s g * stack (V "root") s g (V "prev")
               * [| Ptr (V "root") g |] * [| NoDup s |]
      POST[_] Ex g', graph g' * [| stayMarked g g' |]
               * [| markedS g (V "root" :: s) g' |] ]
    While (0 = 0) {
      If ("root" = 0) { "tmp" <- 2 } else { Note [sharing];; "tmp" <-* "root" };;

      If ("tmp" = 0) { Note [pushCase];;
        "root" *<- 1;;
        "tmp" <-* "root"+4;; "root"+4 *<- "prev";;
        "prev" <- "root";; "root" <- "tmp"
      } else {
        If ("prev" = 0) {
          Return 0
        } else {
          "tmp" <-* "prev";;
          If ("tmp" <> 2) {
            "prev" *<- 2;;
            "tmp" <-* "prev"+4;; "prev"+4 *<- "root";;
            "root" <-* "prev"+8;; "prev"+8 *<- "tmp"
          } else {
            "tmp" <-* "prev"+8;; "prev"+8 *<- "root";;
            "root" <- "prev";; "prev" <- "tmp"
          }
        }
      }
    }
  end
}}.


(* ===========================================================================
 * list lemmas
 * ========================================================================= *)

Section ListLemmas.
  Variable A : Type.
  Variable eq_dec : forall x y : A, { x = y } + { x <> y }.

  Lemma In_split_last : forall (p : A) l, In p l
                            -> exists x y, l = x ++ p :: y /\ ~ In p y.
    induction l; simpl; intros; try tauto.
    destruct (In_dec eq_dec p l); eauto.
    {
      destruct IHl as [? [? [] ] ]; auto; subst.
      exists (a :: x), x0; split; simpl; auto.
    }
    {
      destruct H; try tauto; subst.
      exists nil, l; simpl; auto.
    }
  Qed.
End ListLemmas.


(*=============================================================================
 * reachable/marked lemmas
 *===========================================================================*)

Local Hint Resolve Forall_cons.

Section reachableNoLoops.
  Variable g : set.

  Inductive pathOf : list W -> W -> obj -> Prop :=
  | pathBase o : o %in g -> Mark o = false
                       -> pathOf (Address o :: nil) (Address o) o
  | pathFirst  x o l : x %in g -> Mark x = false -> pathOf l (FirstChild x) o
                             -> pathOf (Address x :: l) (Address x) o
  | pathSecond x o l : x %in g -> Mark x = false -> pathOf l (SecondChild x) o
                             -> pathOf (Address x :: l) (Address x) o.

  Local Hint Constructors pathOf reachable.

  Lemma pathOf_ex : forall p o, reachable g p o -> exists l, pathOf l p o.
    induction 1; eauto; destruct IHreachable; eauto.
  Qed.

  Lemma pathOf_reachable : forall l p o, pathOf l p o -> reachable g p o.
    induction 1; eauto.
  Qed.

  Lemma path_app : forall x p q l o, pathOf (x ++ p :: l) q o
                                   -> pathOf (p :: l) p o.
    induction x; simpl; intros; inversion H; clear H; subst; eauto.
    solve [destruct x; simpl in *; congruence].
  Qed.


  (* removes loops at p (by removing the longest prefix ending with p) *)
  Fixpoint removeLoop (p : W) (def l : list W) :=
    match l with
      | nil => def
      | x :: l' => if weq p x then removeLoop p l' l'
                              else removeLoop p def l'
    end.

  Fixpoint noLoopPath (l : list W) :=
    match l with
      | nil => nil
      | x :: l' => let m := noLoopPath l' in x :: (removeLoop x m m)
    end.

  Lemma not_In_removeLoop : forall p l m, ~ In p l -> removeLoop p m l = m.
    induction l; simpl; auto; intros.
    destruct (weq p a); subst; auto; tauto.
  Qed.

  Lemma removeLoop_suffix : forall p x y d, ~ In p y
                            -> removeLoop p d (x ++ p :: y) = removeLoop p y y.
    induction x; simpl; intros.
    solve [destruct (weq p p); try congruence; eauto].
    destruct (weq p a); subst; auto.
  Qed.

  Theorem removeLoop_split : forall p l,
                              exists l', p :: l = l' ++ p :: removeLoop p l l.
    intros; destruct (In_dec (@weq _) p l).
    {
      edestruct (In_split_last (@weq _) p l) as [? [? [] ] ]; eauto; subst.
      rewrite removeLoop_suffix, not_In_removeLoop by auto.
      exists (p :: x); simpl; auto.
    }
    {
      rewrite not_In_removeLoop in * by auto.
      exists nil; auto.
    }
  Qed.

  Lemma removeLoop_sound : forall o p l, pathOf (p :: l) p o
                                         -> pathOf (p :: removeLoop p l l) p o.
    intros; destruct (removeLoop_split p l) as [? Heq]; rewrite Heq in *.
    eapply path_app; eauto 3.
  Qed.
  Local Hint Resolve removeLoop_sound.

  Theorem noLoopPath_sound : forall l p o, pathOf l p o
                                           -> pathOf (noLoopPath l) p o.
    induction l; simpl; auto; inversion 1; subst; simpl; auto.
  Qed.


  Lemma removeLoop_not_In : forall x l, ~ In x (removeLoop x l l).
    intros; destruct (In_dec (@weq _) x l).
    {
      edestruct (In_split_last (@weq _) x l) as [? [? [] ] ]; eauto; subst.
      rewrite removeLoop_suffix, not_In_removeLoop by auto; auto.
    }
    rewrite not_In_removeLoop; auto.
  Qed.
  Local Hint Resolve removeLoop_not_In.

  Lemma removeLoop_In_NoDup : forall p l m, In p l -> NoDup l
                        -> exists l', ~ In p l' /\ NoDup l'
                                      /\ removeLoop p m l = removeLoop p l' l'.
    induction l; simpl; auto; intros; try tauto.
    inversion H0; clear H0; subst; eauto.
    destruct H; subst.
    solve [destruct (weq p p); try congruence; eauto].
    solve [destruct (weq p a); try congruence; eauto].
  Qed.

  Lemma removeLoop_NoDup : forall p l m, In p l -> NoDup l
                           -> NoDup (removeLoop p m l).    
    intros.
    edestruct removeLoop_In_NoDup as [? [? [? eq] ] ]; eauto; rewrite eq.
    rewrite not_In_removeLoop by auto; auto.
  Qed.

  Theorem noLoopPath_NoDup : forall l, NoDup (noLoopPath l).
    induction l; simpl; auto.
    apply NoDup_cons; auto.
    destruct (In_dec (@weq _) a (noLoopPath l)); subst.
    solve [apply removeLoop_NoDup; auto].
    solve [rewrite not_In_removeLoop by auto; auto].
  Qed.

  Lemma pathOf_ex' : forall p o, reachable g p o
                       -> exists l, pathOf (p :: l) p o /\ NoDup (p :: l).
    intros; destruct (pathOf_ex H) as [l].
    apply noLoopPath_sound in H0.
    assert (NoDup (noLoopPath l)) by (apply noLoopPath_NoDup).
    inversion H0; subst; rewrite <- H2 in *; eauto.
  Qed.


  Lemma pathOf_In_reachable : forall l p x z, pathOf l p z -> In x l
                                          -> reachable g x z.
    intros; edestruct in_split as [? [] ]; eauto.
    subst; eapply pathOf_reachable, path_app; eauto.
  Qed.

  Lemma pathOf_not_In_reachable : forall z l p, pathOf l p z
                                  -> forall o, o %in g -> ~ In (Address o) l
                                       -> reachable (g %^ o) p z.
    induction 1; subst; simpl; intros; auto.
    destruct (weq (Address o) (Address o0)); repeat ptrs; tauto.
    constructor; auto.
    constructor 3; auto.
  Qed.

End reachableNoLoops.


Section reachableLemmas.
  Variable g : set.
  Variable g_functional : functional g.
  Variable g_closed : closed g.

  Local Hint Constructors reachable.
  Local Hint Resolve pathOf_In_reachable pathOf_not_In_reachable.

  Ltac reach := ptrs || congruence || tauto.

  Lemma updMark_reachable_inv : forall x z o, reachable g x z -> o %in g
                                -> reachable g (Address o) z
                                   \/ reachable (g %^ o) x z.
    intros; destruct (pathOf_ex H) as [l].
    destruct (In_dec (@weq _) (Address o) l); eauto.
  Qed.

  Lemma updMark_reachable_inv' : forall o x, reachable g (Address o) x
                          -> Address o <> Address x -> o %in g
                          -> reachable (g %^ o) (FirstChild o) x
                             \/ reachable (g %^ o) (SecondChild o) x.
    intros; edestruct pathOf_ex' as [? [] ]; eauto.
    inversion_clear H3; inversion H2; subst; try congruence; repeat ptrs; eauto.
  Qed.

  Lemma stack_swing : forall g' s o, marked g (Address o) g' -> o %in g
                        -> markedS (g %^ o) s g' -> markedS g s g'.
    induction 3; try solve [red; auto]; intros; constructor; auto.
    red; intros; edestruct updMark_reachable_inv; eauto.
  Qed.

  Ltac invert_reachable :=
    match goal with
      | H: reachable _ _ _ |- _ => inversion H; clear H; subst
    end.

  Lemma reachable_mem : forall x y, reachable g x y -> y %in g.
    induction 1; auto.
  Qed.
  Local Hint Resolve reachable_mem.

  Lemma Mark_true_marked : forall o p g', Address o = p -> Mark o = true
                                -> o %in g -> marked g p g'.
    unfold marked; intros; invert_reachable; repeat reach.
  Qed.
  Local Hint Resolve Mark_true_marked.

  Lemma Mark_mark_contra : forall x, Mark (mark x) = false -> False.
    unfold mark; intros; simpl in *; congruence.
  Qed.
  Local Hint Resolve Mark_mark_contra.

  Lemma updMark_unmarked_mem : forall o x, x %in (g %^ o) -> Mark x = false
                                        -> o %in g -> x %in g.
    intros; eapply updMark_neq_mem'; eauto 3; intro; subst; eauto 3.
  Qed.
  Local Hint Resolve updMark_unmarked_mem.

  Lemma updMark_reachable : forall o p x, reachable (g %^ o) p x
                                -> o %in g -> reachable g p x.
    induction 1; eauto 4.
  Qed.
  Local Hint Resolve updMark_reachable.

  Lemma updMark_marked_intro : forall g' o, o %in g -> mark o %in g'
                 -> marked g (FirstChild o) g'
                 -> marked (g %^ o) (SecondChild o) g'
                 -> marked g (Address o) g'.
    intros; destruct (Mark o) eqn:?; eauto 3; red; intros.
    assert (o0 %in g) by eauto.
    destruct (weq (Address o) (Address o0)); repeat reach.
    edestruct updMark_reachable_inv'; eauto 3.
  Qed.

  Lemma updMark_marked_intro' : forall g' o, o %in g -> mark o %in g'
                 -> marked (g %^ o) (FirstChild o) g'
                 -> marked (g %^ o) (SecondChild o) g'
                 -> marked g (Address o) g'.
    intros; destruct (Mark o) eqn:?; eauto 3; red; intros.
    assert (o0 %in g) by eauto.
    destruct (weq (Address o) (Address o0)); repeat reach.
    edestruct updMark_reachable_inv'; eauto 3.
  Qed.

End reachableLemmas.

Local Hint Resolve Mark_true_marked.

Lemma In_markedS : forall g g' s p, In p s -> markedS g s g'
                                       -> marked g p g'.
  induction s; simpl; try tauto.
  destruct 1; subst; inversion 1; subst; auto.
Qed.
Local Hint Resolve In_markedS.

Lemma null_not_reachable : forall g (p : W) y, p = 0
                                -> noNull g -> ~ reachable g p y.
   intros; red; inversion 1; repeat ptrs; eapply noNull_contra; eauto 2.
Qed.

Lemma updMark_marked_self : forall g g' o p, o %in g -> Address o = p
                             -> functional g -> marked (g %^ o) p g'.
  intros; assert (Address (mark o) = p) by auto; eauto 3.
Qed.
Local Hint Resolve updMark_marked_self.


(*=============================================================================
 * more lemmas
 *===========================================================================*)

Local Hint Resolve Forall_cons updMark_marked_intro updMark_marked_intro'.

Lemma markedS_swing_marked : forall o g g' s p p',
                markedS (g %^ o) (SecondChild o :: p :: s) g'
                -> marked g (FirstChild o) g' -> stayMarked (g %^ o) g'
                -> o %in g -> Mark o = false -> p = Address o -> heapInv g
                -> p' = FirstChild o -> markedS g (p' :: p :: s) g'.
  inversion_clear 1; intros; subst; apply Forall_cons; auto.
  eapply stack_swing; eauto 3; red; auto.
Qed.
Local Hint Resolve markedS_swing_marked.

Lemma markedS_swing_in_stack : forall o g g' q p s,
                markedS (g %^ o) (SecondChild o :: p :: s) g'
                -> stayMarked (g %^ o) g' -> In q (p :: s) -> q = FirstChild o
                -> Address o = p -> o %in g -> Mark o = false
                -> heapInv g -> markedS g (q :: p :: s) g'.
  inversion_clear 1; intros; subst.
  apply stack_swing with o; eauto 4; red; eauto 3.
Qed.
Local Hint Immediate markedS_swing_in_stack.

Lemma markedS_pre : forall g r g', markedS g (r :: nil) g'
                                      -> marked g r g'.
  inversion_clear 1; auto.
Qed.
Local Hint Immediate markedS_pre.

Lemma markedS_push : forall o g p s g',
                       markedS g (FirstChild o :: p :: s) g'
                       -> Address o = p -> markedS g (p :: s) g'.
  inversion_clear 1; intros; subst; auto.
Qed.
Local Hint Immediate markedS_push.

Lemma markedS_pop : forall g g' p s, marked g p g' -> markedS g s g'
                                        -> markedS g (p :: s) g'.
  red; auto 3.
Qed.
Local Hint Resolve markedS_pop.

Lemma null_marked : forall (p : W) g g' p', p = p' -> p = 0
                       -> heapInv g -> marked g p' g'.
  red; intros; subst; contradict H2; apply null_not_reachable; auto.
Qed.
Local Hint Immediate null_marked.

Lemma Mark_true_marked' : forall x p p' g g', p = p' -> Address x = p
                    -> Mark x = true -> x %in g -> heapInv g
                    -> marked g p' g'.
  intros; subst; eapply Mark_true_marked; eauto.
Qed.
Local Hint Immediate Mark_true_marked'.

Lemma Ptr_FirstChild_marked : forall g o, o %in g -> heapInv g
                                 -> Ptr (SecondChild o) (g %^ o).
  destruct 2 as [? [] ]; auto.
Qed.
Local Hint Immediate Ptr_FirstChild_marked.

Lemma heapInv_marked : forall g o, o %in g -> heapInv g
                                 -> heapInv (g %^ o).
  destruct 2 as [? [] ]; auto.
  split; auto.
  apply updMark_noNull; auto; intro; eapply noNull_contra; eauto.
Qed.
Local Hint Immediate heapInv_marked.

Lemma NoDup_pop : forall (p : W) s, NoDup (p :: s) -> NoDup s.
  inversion_clear 1; auto.
Qed.
Local Hint Immediate NoDup_pop.

Lemma stayMarked_updMark : forall g g' o, stayMarked (g %^ o) g' -> o %in g
                               -> Mark o = false -> stayMarked g g'.
  red; intros; destruct (Obj_Key.eq_dec o o0); subst; try congruence; auto.
Qed.
Local Hint Resolve stayMarked_updMark.

Lemma stayMarked_refl : forall g, stayMarked g g.
  red; auto.
Qed.
Local Hint Resolve stayMarked_refl.


(*=============================================================================
 * Proof
 *===========================================================================*)

Ltac tags :=
  match goal with
    | H: objTag (Mark ?o) = _ |- _ => destruct (Mark o) eqn:?
    | H: not (objTag (Mark ?o) = natToW 0) |- _ => destruct (Mark o) eqn:?
    | H: not (objTag (Mark ?o) = natToW 2) |- _ => destruct (Mark o) eqn:?
    | H: stackTag (Mark ?o) = _ |- _ => destruct (Mark o) eqn:?
    | H: not (stackTag (Mark ?o) = natToW 1) |- _ => destruct (Mark o) eqn:?
    | H: not (stackTag (Mark ?o) = natToW 2) |- _ => destruct (Mark o) eqn:?
    | H: context[stackTag ?b = _] |- _ => progress simpl in H
    | H: context[objTag ?b = _] |- _ => progress simpl in H
    | _ => congruence || discriminate
  end.

Ltac evaler := evaluate hints; repeat tags.

Ltac pick :=
  match goal with
    | _: In ?p ?s, H: context[stack ?p ?s ?g ?q], _: not (?p = ?q) |- _
      => change (stack p s g q) with (stack_pick p p s g q) in H
    | _: ~ In ?p ?s, H: context[objects ?s ?g] |- _
      => change (objects s g) with (objects_pick p s g) in H
  end.

Ltac splitter :=
  match goal with
    | [ H : context[Assign] |- _ ] => generalize dependent H; evaler
  end; intros;
  match goal with
    | _: context[stack ?p ?s ?g ?q] |- _
      => destruct (In_dec (@weq _) p s); [ destruct (weq p q) | ]
  end.

Ltac deadPath :=
  match goal with
    | [ H : context[Assign] |- _ ] => generalize dependent H; solve [evaler]
  end.

Ltac instVars :=
  match goal with
    | _: context[stack ?p ?s ?g ?q], _: Address ?o = ?p, _: Mark ?o = false |- _
      => exists g, (p :: s)
    | _: ?s = ?q :: _, _: Address ?o = ?q, _: ?o %in ?g, _: Mark ?o = false |- _
      => exists (g %^ o), s
    | _: ?s = ?q :: ?s', _: Address ?o = ?q, _: ?o %in ?g, _: Mark ?o = true |- _
      => exists g, s'
  end.

Ltac evalSafe :=
  try match goal with
        | _: sharing |- _ => splitter; try pick
      end;
  try match goal with
        | _: pushCase, _: ~ In _ _ |- _ => idtac
        | _: pushCase |- _ => deadPath
      end; evaler; try instVars.

Ltac himp_finish_h :=
  repeat match goal with
           | H: Mark _ = _ |- _ => rewrite H
           | H: Address _ = _ |- _ => rewrite H
         end; sepLemma.

Ltac himp_finish :=
  match goal with
    | _: Address ?o = ?p |- context[objects ?s (?g %- ?o)]
      => progress change (objects (p :: s) g) with (objects_pushed o (p :: s) g)
    | _: Address ?o = ?p |- context[objects (?p :: ?s) _]
      => progress change (objects s) with (objects_popped o p s)
    | _: Address ?o = ?q |- context[objects ?s (?g %- ?o)]
      => progress change (objects s g) with (objects_filled o q s g)
    | _: Address ?o = ?t |- context[stackH ?t ?q ?s ?g ?p]
      => progress change (stack q s g p) with (stack_filled o q s g p)
    | _ => step hints
    | _ => solve [himp_finish_h]
  end.

Ltac finish := solve [eauto 4 | repeat himp_finish].

Local Hint Unfold markedS.

Theorem ok : moduleOk m.
  vcgen; abstract (try enterFunction; post; evalSafe; sep hints; finish).
Qed.
