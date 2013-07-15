Require Import AutoSep.
Set Implicit Arguments.
Open Scope Sep.

Section ExtractPure.

  (* ============================================================================
   * HProp lemmas and tactic
   * ========================================================================= *)

  Lemma intro_pure_l : forall (P : Prop) Q R, (P -> Q ===> R) -> [| P |] * Q ===> R.
    sepLemma.
  Qed.

  Lemma intro_pure_r : forall (P : Prop) Q R, (P -> Q ===> R) -> Q * [| P |] ===> R.
    sepLemma.
  Qed.

  Lemma intro_pure_cl : forall (P : Prop) Q R, P -> (Q ===> R) -> Q ===> [| P |] * R.
    sepLemma.
  Qed.

  Lemma intro_pure_cr : forall (P : Prop) Q R, P -> (Q ===> R) -> Q ===> R * [| P |].
    sepLemma.
  Qed.

  Lemma intro_Ex : forall T (Q : T -> HProp) R, (forall x : T, Q x ===> R) -> (Ex x, Q x ===> R).
    sepLemma.
  Qed.
  Lemma intro_Ex_hyp : forall T (Q : T -> HProp) R, (forall x : T, (Q x ===> R)) ->
                                                    (Ex x, Q x) ===> R.
    sepLemma.
  Qed.

  Lemma intro_star_Ex_hyp : forall T (Q : T -> HProp) P R, (forall x : T, P * Q x ===> R) ->
                                                           (Ex x, Q x) * P ===> R.
    sepLemma.
  Qed.


  Ltac hprop :=
    repeat match goal with
             | _ => red; intros; reflexivity
             | _ => solve [auto]
             | |- Himp (@starB _ (injB _ _) _) _ => apply intro_pure_l; intro
             | |- Himp (@starB _ _ (injB _ _)) _ => apply intro_pure_r; intro
             | |- Himp _ (@starB _ (injB _ _) _) => apply intro_pure_cl
             | |- Himp _ (@starB _ _ (injB _ _)) => apply intro_pure_cr
             | |- Himp (@exB _ _ _) _ => apply intro_Ex; intro
             | |- Himp (@starB _ (@exB _ _ _) _) _ => apply intro_star_Ex_hyp; intro
           end.


  (* ============================================================================
   * encoding and basic interpretation
   * ========================================================================= *)

  Inductive exp : Type :=
  | inj : HProp -> exp
  | ex : HProp -> exp
  | other : HProp -> exp
  | star : exp -> exp -> exp.

  Fixpoint interpE (e : exp) : HProp :=
    match e with
      | inj p => p
      | ex p => p
      | other p => p
      | star e1 e2 => interpE e1 * interpE e2
    end.

  Fixpoint interpL (l : list exp) : HProp :=
    match l with
      | nil => [| True |]
      | e :: l' => interpE e * interpL l'
    end.

  Lemma interpL_appendI : forall e f, interpL e * interpL f ===> interpL (e ++ f).
    induction e; simpl; intros; hprop.
    eapply Himp_trans.
    apply Himp_star_assoc.
    apply Himp_star_frame; hprop.
  Qed.

  Lemma interpL_app_cons_comm : forall e m n, interpL (m ++ (e :: n)) ===> interpL (e :: (m ++ n)).
    induction m; simpl; hprop.
    intros.
    eapply Himp_trans.
    apply Himp_star_frame.
    apply Himp_refl.
    apply IHm.
    simpl.
    eapply Himp_trans.
    2: apply Himp_star_assoc; auto.
    eapply Himp_trans.
    apply Himp_star_assoc'.
    apply Himp_star_frame. 
    apply Himp_star_comm.
    apply Himp_refl.
  Qed.

  Lemma interpL_app_cons_comm' : forall e m n, interpL (e :: (m ++ n)) ===> interpL (m ++ (e :: n)).
    simpl; induction m; simpl; hprop; intros.
    eapply Himp_trans.
    apply Himp_star_assoc'.
    eapply Himp_trans.
    apply Himp_star_frame.
    apply Himp_star_comm.
    apply Himp_refl.
    eapply Himp_trans; [apply Himp_star_assoc | ].
    apply Himp_star_frame.
    apply Himp_refl.
    apply IHm.
  Qed.


  (* ============================================================================
   * flatten and its soundness
   * ========================================================================= *)

  Fixpoint flatten (e : exp) :=
    match e with
      | star e1 e2 => (flatten e1) ++ (flatten e2)
      | _ => e :: nil
    end.

  Theorem flatten_sound : forall e R, interpL (flatten e) ===> R -> interpE e ===> R.
    induction e; simpl; intros; try (eapply Himp_trans; [ | apply H]; hprop).
    eapply Himp_trans; [ |apply interpL_appendI].
    apply Himp_star_frame.
    apply IHe1; hprop.
    apply IHe2; hprop.
  Qed.


  (* ============================================================================
   * sort and its soundness
   * ========================================================================= *)

  Fixpoint filter_pure (l : list exp) :=
    match l with
      | nil => nil
      | inj p :: l' => (inj p) :: filter_pure l'
      | ex p :: l' => (ex p) :: filter_pure l'
      | _ :: l' => filter_pure l'
    end.

  Fixpoint filter_other (l : list exp) :=
    match l with
      | nil => nil
      | other p :: l' => (other p) :: filter_other l'
      | star p1 p2 :: l' => (star p1 p2) :: filter_other l'
      | _ :: l' => filter_other l'
    end.

  Definition sortExp (l : list exp) := filter_pure l ++ filter_other l.

  Lemma interpL_sortExp_app : forall a b, interpL (sortExp a) * interpL (sortExp b)
                                            ===> interpL (sortExp (a ++ b)).
    unfold sortExp; induction a; intros; try solve [simpl; hprop].
    destruct a; simpl.
    eapply Himp_trans; [apply Himp_star_assoc| ]; apply Himp_star_frame; hprop.
    eapply Himp_trans; [apply Himp_star_assoc| ]; apply Himp_star_frame; hprop.

    eapply Himp_trans; [ |apply interpL_app_cons_comm']; simpl.
    eapply Himp_trans; [apply Himp_star_frame | ].
    apply interpL_app_cons_comm.
    apply Himp_refl.
    simpl.
    eapply Himp_trans; [apply Himp_star_assoc| ].
    apply Himp_star_frame.
    apply Himp_refl.
    apply IHa.

    eapply Himp_trans; [ |apply interpL_app_cons_comm']; simpl.
    eapply Himp_trans; [apply Himp_star_frame | ].
    apply interpL_app_cons_comm.
    apply Himp_refl.
    simpl.
    eapply Himp_trans; [apply Himp_star_assoc| ].
    apply Himp_star_frame.
    apply Himp_refl.
    apply IHa.
  Qed.

  Theorem sortExp_sound : forall e R, interpL (sortExp (flatten e)) ===> R -> interpE e ===> R.
    induction e; simpl; intros; try (eapply Himp_trans; [ | apply H]; hprop).
    eapply Himp_trans; [apply Himp_star_frame | ].
    apply IHe1; hprop.
    apply IHe2; hprop.
    apply interpL_sortExp_app.
  Qed.


  (* ============================================================================
   * alternative interpretation without the trailing "[| True |]"
   * ========================================================================= *)

  Fixpoint interpL' (l : list exp) : HProp :=
    match l with
      | nil => [| True |]
      | e :: nil => interpE e
      | e :: l' => interpE e * interpL' l'
    end.

  Lemma interpL'_sound : forall l, interpL l ===> interpL' l.
    induction l; try hprop.
    simpl.
    destruct l.
    simpl; hprop.
    apply Himp_star_frame; auto.
    apply Himp_refl.
  Qed.

  Theorem sortExp_sound' : forall e R, interpL' (sortExp (flatten e)) ===> R -> interpE e ===> R.
    intros.
    apply sortExp_sound.
    eapply Himp_trans.
    apply interpL'_sound; auto.
    auto.
  Qed.

End ExtractPure.


(* ============================================================================
 * sepPure : a reflective tactic for extracting pure propositions
 * ========================================================================= *)

Ltac _reifyExp P :=
  match P with
    | injB _ _ => constr:(inj P)
    | exB _ => constr:(ex P)
    | ?P * ?Q =>
      let s := _reifyExp P in
      let t := _reifyExp Q in
      constr:(star s t)
    | ST.star ?P ?Q =>
      let s := _reifyExp P in
      let t := _reifyExp Q in
      constr:(star s t)
    | ?P => constr:(other P)
  end.

Ltac _intro_pure :=
  match goal with
    | |- Himp (@starB _ (injB _ _) _) _ => apply intro_pure_l; intro
    | |- Himp (@starB _ _ (injB _ _)) _ => apply intro_pure_r; intro
    | |- Himp (@exB _ _ _) _ => apply intro_Ex; intro
    | |- Himp (@starB _ (@exB _ _ _) _) _ => apply intro_star_Ex_hyp; intro
  end.

Ltac _sortHyp :=
  match goal with
    | |- Himp ?P ?Q => let t := _reifyExp P in
                       change (interpE t ===> Q)
  end; apply sortExp_sound'; simpl; repeat _intro_pure.

Ltac sepPure := repeat progress _sortHyp.

(* a test case
Goal forall (q : Prop) (p r R : HProp) (s : bool -> HProp),
       (p * [| q |]) * ((Ex b, s b * (Ex c, s c)) * r) ===> R.
  intros.
  hprop_pure.
Abort.*)


(* ==================================================================================
 * Deducing contradiction in Sepration Logic
 * =============================================================================== *)

Section SepContradiction.

  Lemma split_disjoint : forall m m1 m2, split m m1 m2 -> disjoint m1 m2.
    unfold split; intros; tauto.
  Qed.
  Hint Resolve split_disjoint.

  Ltac disjoint :=
    match goal with
      | _ => solve [eauto]
      | _ => solve [eapply split_split_disjoint; eauto]
      | _ => solve [apply disjoint_comm; eapply split_split_disjoint; eauto]
    end.

  (* The basic contradiction rule of separation logic *)
  Lemma sep_contra : forall p a b, p =*> a * p =*> b ===> [| False |].
    intros.
    red; intros.
    red; intros.
    unfold "*", ST.star; intros.
    repeat match goal with
             | _ => progress intro
             | _ => apply Imply_and_assoc
             | _ => apply Imply_nestedEx
             | _ => apply Imply_easyEx
             | _ => apply Imply_easyL
           end.
    apply simplify_Imply; intro.
    exfalso.
    subst; simpl in *.

    repeat match goal with
             | H: _ /\ _ |- _ => destruct H
             | H: disjoint ?m ?m',
                  H1: smem_get_word _ _ ?m = Some _, H2: smem_get_word _ _ ?m' = Some _ |- _
               => solve [elimtype False; apply (smem_get_word_disjoint _ _ _ _ H H1 H2)]
             | H1: smem_get_word ?s ?p ?m1 = Some ?x1, H2: smem_get_word ?s ?p ?m2 = Some ?x2
               |- _ => assert (disjoint m1 m2) by disjoint
           end.
  Qed.

End SepContradiction.
