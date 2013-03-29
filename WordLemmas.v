Require Import AutoSep.
Set Implicit Arguments.

(* usuful and safe hints *)
Hint Rewrite Npow2_nat : N.
Hint Resolve bound_N_nat : N.
Hint Rewrite natToWord_wordToNat : N.

(* ============================================================================
 * word to nat
 * ========================================================================= *)

Theorem wordToNat_inj : forall sz (x y:word sz),
                          wordToNat x = wordToNat y -> x = y.
  intros.
  apply (f_equal (natToWord sz)) in H.
  autorewrite with N in *.
  assumption.
Qed.
  
Theorem wordToNat_inj' : forall sz (x y:word sz), x <> y ->
                                                      wordToNat x <> wordToNat y.
  intros.
  contradict H.
  apply wordToNat_inj; assumption.
Qed.


(* ============================================================================
 * nat to word
 * ========================================================================= *)

Lemma natToWord_pow2' : forall(sz k:nat)(w:word sz),
                          natToWord sz (k * pow2 sz) ^+ w = w.
  induction k; intros; simpl.

  apply wplus_unit.

  rewrite natToWord_plus.
  rewrite <- wplus_assoc.
  rewrite natToWord_pow2.
  rewrite wplus_unit.
  apply IHk.
Qed.

Lemma natToWord_pow2_zero: forall sz n, $ (n * pow2 sz) = natToWord sz 0.
  intros.
  rewrite <- (wplus_unit $(n * pow2 sz)).
  rewrite wplus_comm.
  apply natToWord_pow2'.
Qed.

Lemma natToWord_pow2_factor : forall (sz:nat)(w:word sz), exists n, forall k,
                    (n < pow2 sz)%nat /\ w = natToWord sz (k * pow2 sz + n).
  intros.
  exists (wordToNat w).
  intro.
  split.
  apply (wordToNat_bound w).
  rewrite natToWord_plus.
  rewrite natToWord_pow2'.
  rewrite natToWord_wordToNat.
  reflexivity.
Qed.

Corollary word_eq_natToWord : forall (sz:nat)(w:word sz), exists n,
                                     (n < pow2 sz)%nat /\ w = natToWord sz n.
  intros.
  generalize natToWord_pow2_factor; intro.
  specialize (H sz w).
  destruct H.
  specialize (H 0).
  destruct H.
  simpl in H0.
  exists x; auto.
Qed.

Lemma natToWord_inj' : forall sz a b, goodSize a -> goodSize b
                                      -> natToWord sz a <> $ b
                                      -> a <> b.
  intros; intro; subst; congruence.
Qed.


(* ============================================================================
 * nat to W
 * ========================================================================= *)

Transparent goodSize.

Lemma goodSize_natToW_wlt_lt : forall n m:nat, goodSize n -> goodSize m ->
                                     natToW n < natToW m -> (n < m)%nat.
  unfold goodSize, natToW.
  generalize dependent 32; intros; nomega.
Qed.

Corollary W_eq_natToW : forall(w:W), exists n, goodSize n /\ w = natToW n.
  intros.
  generalize word_eq_natToWord; intro.
  specialize (H 32 w).
  destruct H.
  destruct H.
  exists x.
  unfold goodSize.
  split; auto.
Qed.

Opaque goodSize.

Lemma wneg_natToW_pow2_minus : forall n:nat, goodSize n ->
                                      ^~ (natToW n) = natToW (pow2 32 - n).
  unfold wneg; intros.
  rewrite NToWord_nat.
  autorewrite with N; reflexivity.
Qed.

Lemma natToW_plus_pow2 : forall n : nat, natToW (pow2 32 + n) = $ n.
  unfold natToW; intros.
  rewrite natToWord_plus.
  rewrite natToWord_pow2.
  words.
Qed.


(* ============================================================================
 * destruct_word
   Turn word arithmetic into nat arithmetic.
 * ========================================================================= *)

Ltac destruct_word sz w n :=
  let H := fresh "W" in
  let Hub := fresh "Wub" in
  let Heq := fresh "Weq" in
  assert (H:exists w', (w' < pow2 sz)%nat /\ w = natToWord sz w') by
      apply word_eq_natToWord;
  elim H; clear H; intros n H; elim H; intros Hub Heq; rewrite Heq in *; clear H Heq w.

Ltac destruct_W w n :=
  let H := fresh "W" in
  let Hub := fresh "Wub" in
  let Heq := fresh "Weq" in
  assert (H:exists w', goodSize w' /\ w = natToW w') by
      apply W_eq_natToW;
  elim H; clear H; intros n H; elim H; intros Hub Heq; rewrite Heq in *; clear H Heq w.

Ltac destruct_words := repeat
  match goal with
    | w : W |- context[?w] =>
      is_var w; let w' := fresh "w" in destruct_W w w'
    | w : word 32 |- context[?w] =>
      is_var w; let w' := fresh "w" in destruct_W w w'
    | w : word ?sz |- context[?w] =>
      is_var w; let w' := fresh "w" in destruct_word sz w w'
  end.


(* ============================================================================
 * goodsize tactic
 * ========================================================================= *)

Ltac goodsize :=
  match goal with
    | [ |- (_ < pow2 32)%nat ] => apply goodSize_danger
    | _ => idtac
  end;
  match goal with
    | [ H: goodSize ?n |- goodSize _ ] => solve [apply goodSize_weaken with n; eauto]
    | _ => eauto
  end.


(* ============================================================================
 * roundTrip-related lemmas and roundtrip tactic
 * ========================================================================= *)

Corollary wordToNat_natToWord_idempotent_W : forall n,
                                             goodSize n ->
                                             wordToNat (natToW n) = n.
  intros; apply wordToNat_natToWord_idempotent; auto.
Qed.
Hint Rewrite wordToNat_natToWord_idempotent_W using solve [goodsize] : N.

Corollary roundTrip : forall sz n : nat,
                        (n < pow2 sz)%nat -> wordToNat (natToWord sz n) = n.
  intros; apply wordToNat_natToWord_idempotent; nomega.
Qed.
Hint Rewrite roundTrip using solve [eauto] : N.

Lemma natToW_wordToNat : forall w:W, natToW (wordToNat w) = w.
  intros; rewrite <- natToWord_wordToNat; auto.
Qed.
Hint Rewrite natToW_wordToNat : N.


(* ============================================================================
 * word equalities with operators
 * ========================================================================= *)

Definition eq_W_dec : forall x y : W, { x = y } + { x <> y }.
  intros.
  destruct (Word.weqb x y) eqn:Heq; [apply weqb_sound in Heq | ]; auto.
  right; intro.
  apply weqb_true_iff in H; congruence.
Qed.

Lemma weqb_false_iff : forall sz (x y : word sz), Word.weqb x y = false <-> x <> y.
  intros.
  split; intros.
  intro Eq; apply weqb_true_iff in Eq; congruence.
  case_eq (Word.weqb x y); intro; auto.
  apply weqb_sound in H0; congruence.
Qed.

Lemma weqb_refl : forall w, weqb w w = true.
  intros; apply weqb_true_iff; auto.
Qed.
Hint Rewrite weqb_refl : N.

Lemma weqb_diff : forall w1 w2, w1 <> w2 -> weqb w1 w2 = false.
  intros; apply weqb_false_iff; auto.
Qed.
Hint Rewrite weqb_diff using solve [auto; discriminate] : N.

Lemma wordToNat_wplus : forall sz x y:nat, (x + y < pow2 sz)%nat ->
                        wordToNat (natToWord sz x ^+ natToWord sz y) = x + y.
  intros.
  rewrite <- natToWord_plus.
  rewrite roundTrip; auto.
Qed.

Lemma natToW_S_wminus_1 : forall n, $ (S n) ^- $1 = natToW n.
  unfold natToW; intros.
  replace (S n) with (n + 1) by omega; rewrite natToWord_plus.
  words.
Qed.
Hint Rewrite natToW_S_wminus_1 : N.


(* ============================================================================
 * simplification tactic
 * ========================================================================= *)

Ltac roundtrip :=
  pre_nomega; unfold natToW in *;
  repeat match goal with
           | _ => rewrite wordToNat_natToWord_idempotent_W in * by goodsize
           | _ => rewrite wordToNat_wminus in * by (goodsize; nomega)
           | _ => rewrite wordToNat_wplus in * by (goodsize; nomega)

           | H: _ |- _ => rewrite <- natToWord_plus in H by omega
           | H: natToWord ?sz _ = natToWord ?sz _ |- _
             => apply natToWord_inj with sz _ _ in H; goodsize
           | H: not (natToWord ?sz _ = natToWord ?sz _) |- _
             => apply natToWord_inj' with sz _ _ in H; goodsize
         end.


(* ============================================================================
 * word inequalities
 * ========================================================================= *)

Lemma wle_wneq_wlt : forall i j:W, i <= j -> i <> j -> i < j.
  intros.
  destruct_words.
  apply wordToNat_inj' in H0.
  autorewrite with N in *.
  nomega.
Qed.

Lemma wle_wle_antisym : forall n m:W, n <= m -> m <= n -> n = m.
  intros.
  destruct_words.
  f_equal.
  nomega.
Qed.
