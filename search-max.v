(* ============================================================================
 * Kaldewaij’ search by elimination
 * Bedrock implementtaion/proof by Duckki Oe (4/9/2013)
 * paper: http://link.springer.com/chapter/10.1007%2F3-540-51305-1_17#page-1
 * Defny version: http://rise4fun.com/dafny/Chqv
 * ========================================================================= *)
Set Implicit Arguments.
Require Import AutoSep WordLemmas.

(* ============================================================================
 * specification
 * ========================================================================= *)

Definition gtAll (x : W) ls := List.Forall (fun y => y <= x) ls.

Definition maxS : spec := SPEC("a", "n") reserving 10
  Al ls,
  PRE[V]  array ls (V "a") * [| wordToNat(V "n") = length ls |]
          * [| ls <> nil |]
  POST[R] array ls (V "a") * [| (wordToNat R < length ls)%nat |]
          * [| gtAll (selN ls (wordToNat R)) ls |].


(* ============================================================================
 * implementation
 * ========================================================================= *)

Definition gtAll' (x y : W) ls := List.Forall (fun z => z <= x \/ z <= y) ls.

Definition maxInv (x y : nat) ls :=
  let a_x := selN ls x in
  let a_y := selN ls y in
  gtAll' a_x a_y (firstn x ls) /\ gtAll' a_x a_y (skipn y ls).

Definition maxM := bmodule "max" {{
  bfunction "max"("a", "n", "x", "y", "a_x", "a_y", "offset") [maxS]
    "x" <- 0;;
    "y" <- "n" - 1;;
    [ Al ls,
      PRE[V]  array ls (V "a")
              * [| (V "x" <= V "y")%word |]
              * [| (wordToNat (V "y") < length ls)%nat |]
              * [| maxInv (wordToNat (V "x")) (wordToNat (V "y")) ls |]
      POST[R] array ls (V "a") * [| (wordToNat R < length ls)%nat |]
              * [| gtAll (selN ls (wordToNat R)) ls |] ]
    While ("x" <> "y") {
      "offset" <- 4 * "x";;
      "a_x" <-* "a" + "offset";;
      "offset" <- 4 * "y";;
      "a_y" <-* "a" + "offset";;
      If ("a_x" <= "a_y") {
        "x" <- "x" + 1
      }
      else {
        "y" <- "y" - 1
      }
    };;
    Return "x"
  end
}}.


(* ============================================================================
 * Lemmas
 * ========================================================================= *)

Lemma max_lem1 : forall A (ls : list A) n, wordToNat n = length ls -> ls <> nil
                     -> (wordToNat (n ^- natToW 1) < length ls)%nat.
  destruct ls; try congruence; simpl; intros.
  roundtrip; autorewrite with N; auto.
Qed.
Hint Resolve max_lem1.

Lemma max_lem2 : forall x y : W, x <> y -> x <= y -> x ^+ natToW 1 <= y.
  intros; destruct_words; roundtrip; omega.
Qed.
Hint Resolve max_lem2.

Lemma max_lem3 : forall x y : W, x <> y -> x <= y -> x <= y ^- natToW 1.
  intros; destruct_words; roundtrip; omega.
Qed.
Hint Resolve max_lem3.

Lemma max_lem4 : forall n (x y : W), x <> y -> x <= y -> (wordToNat y < n)%nat
                                   -> (wordToNat (y ^- natToW 1) < n)%nat.
  intros.
  assert (x < y) by (apply wle_wneq_wlt; auto).
  destruct_words; roundtrip; omega.
Qed.


Lemma selN_last : forall ls : list W, selN ls (pred (Datatypes.length ls))
                                     = List.last ls $0.
  induction ls; simpl; auto.
  destruct ls; simpl; auto.
Qed.

Lemma skipn_last : forall ls : list W, ls <> nil
                                       -> skipn (pred (Datatypes.length ls)) ls
                                          = (List.last ls $0 :: nil).
  induction ls; simpl; try congruence; intros.
  destruct ls; simpl in *; auto.
  rewrite IHls; auto; congruence.
Qed.

Lemma firstn_S : forall n ls, ls <> nil -> (S n < length ls)%nat
                              -> firstn (S n) ls
                                 = firstn n ls ++ selN ls n :: nil.
  induction n; try congruence; simpl; intros.
  destruct ls; try congruence; simpl; auto.
  destruct ls; try congruence; simpl; auto.
  rewrite <- IHn; auto.
  destruct ls; simpl in *; try congruence; try omega.
  simpl in *; omega.
Qed.

Lemma skipn_pred : forall n ls, ls <> nil -> (n < length ls)%nat -> (0 < n)%nat
                              -> skipn (pred n) ls
                                 = selN ls (pred n) :: skipn n ls.
  induction n; simpl; intros; try omega.
  destruct ls; try congruence; simpl; auto.
  destruct n; simpl; auto.
  rewrite <- IHn; simpl in *; auto.
  destruct ls; simpl in *; try omega.
  congruence.
Qed.

Lemma Forall_firstn_skipn : forall A P n (ls : list A),
                              List.Forall P (firstn n ls)
                              -> List.Forall P (skipn n ls)
                              -> List.Forall P ls.
  intros; rewrite <- (firstn_skipn n); apply Forall_app; auto.
Qed.


Lemma maxInv_init : forall n ls, ls <> nil -> wordToNat n = length ls
                                 -> maxInv 0 (wordToNat (n ^- natToW 1)) ls.
  unfold maxInv, gtAll'; split; simpl; auto.
  assert (wordToNat (n ^- natToW 1) = pred (length ls)).
    destruct ls; try congruence; simpl in *.
    roundtrip; autorewrite with N; auto.
    rewrite H0; omega.
  rewrite H1.
  rewrite selN_last, skipn_last by auto.
  apply List.Forall_cons; auto.
Qed.
Hint Resolve maxInv_init.

Lemma maxInv_plus' : forall x y ls, (x < y)%nat
                               -> (y < length ls)%nat
                               -> selN ls x <= selN ls y
                               -> maxInv x y ls
                               -> maxInv (S x) y ls.
  unfold maxInv; unfold gtAll'; intros.
  assert (ls <> nil).
    destruct ls; try congruence; simpl in *.
    exfalso; omega.
  destruct H2; split.
  rewrite firstn_S by auto.
  apply Forall_app; auto.
  eapply Forall_impl, H2; simpl; intros.
  destruct H5; auto.
  right; nomega.

  eapply Forall_impl, H4; simpl; intros.
  destruct H5; auto.
  right; nomega.
Qed.

Lemma maxInv_plus : forall (x y : W) ls, x <> y -> x <= y
                        -> (wordToNat y < length ls)%nat
                        -> selN ls (wordToNat x) <= selN ls (wordToNat y)
                        -> maxInv (wordToNat x) (wordToNat y) ls
                        -> maxInv (wordToNat (x ^+ natToW 1)) (wordToNat y) ls.
  intros; destruct_words; roundtrip.
  replace (w + 1) with (S w) by omega.
  apply maxInv_plus'; auto.
  nomega.
Qed.
Hint Resolve maxInv_plus.

Lemma maxInv_minus' : forall x y ls, (x < y)%nat -> (y < length ls)%nat
                               -> selN ls y < selN ls x
                               -> maxInv x y ls
                               -> maxInv x (pred y) ls.
  unfold maxInv; unfold gtAll'; intros.
  assert (ls <> nil).
    destruct ls; try congruence; simpl in *.
    exfalso; omega.
  destruct H2; split.
  eapply Forall_impl, H2; simpl; intros.
  destruct H5; auto.
  left; nomega.

  rewrite skipn_pred by auto.
  eapply Forall_cons.
  right; auto.
  eapply Forall_impl, H4; simpl; intros.
  destruct H5; auto.
  left; nomega.
Qed.

Lemma maxInv_minus : forall (x y : W) ls, x <> y -> x <= y
                         -> (wordToNat y < length ls)%nat
                         -> selN ls (wordToNat y) < selN ls (wordToNat x)
                         -> maxInv (wordToNat x) (wordToNat y) ls
                         -> maxInv (wordToNat x) (wordToNat (y ^- natToW 1)) ls.
  intros; destruct_words; roundtrip.
  replace (w0 - 1) with (pred w0) by omega.
  apply maxInv_minus'; auto.
  nomega.
Qed.
Hint Resolve maxInv_minus.

Lemma maxInv_gtAll : forall x ls, maxInv x x ls -> gtAll (selN ls x) ls.
  unfold maxInv, gtAll, gtAll'; intros; subst.
  destruct H.
  eapply Forall_impl, Forall_firstn_skipn; try eassumption.
  simpl; intros.
  destruct H1; auto.
Qed.
Hint Resolve maxInv_gtAll.

Lemma maxInv_eq : forall (x y : W) ls, x = y
                      -> maxInv (wordToNat x) (wordToNat y) ls
                      -> maxInv (wordToNat x) (wordToNat x) ls.
  intros; subst; auto.
Qed.


(* ============================================================================
 * Proof
 * ========================================================================= *)
    
Hint Extern 1 (_ <= _) => nomega.
Hint Extern 1 (wordToNat (_ ^- _) < _)%nat => solve [eapply max_lem4; eauto].
Hint Extern 1 (maxInv _ _ _) => solve [eapply maxInv_eq; eauto].

Ltac unstuck :=
  match goal with
    | H: context[Assign] |- _ => generalize dependent H; evaluate auto_ext
  end; intro;
  match goal with
    | _: ?x <= ?y, _: (wordToNat ?y < length ?ls)%nat |- _
      => assert (x < natToW (length ls)) by nomega;
        assert (y < natToW (length ls)) by nomega
  end.

Ltac finish :=
  match goal with
    | _ => solve [auto]
    | H: Regs ?st Rv = _ |- _ => rewrite H
  end.

Theorem maxM_correct : moduleOk maxM.
  vcgen; solve [ enterFunction
               | post; try unstuck; sep_auto; repeat finish].
Qed.
