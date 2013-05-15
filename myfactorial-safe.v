Require Import AutoSep WordLemmas.

(* ============================================================================
 * specification with overflow safeguard
 * - the result is correct and not overflowing if the input is 12 or less
 * ========================================================================= *)

Fixpoint fact (n : nat) :=
  match n with
    | 0 => 1
    | S n' => n * fact n'
  end.

Definition factS : spec := SPEC("n") reserving 1
  PRE[V]  [| (wordToNat (V "n") <= 12)%nat |]
  POST[R] [| wordToNat R = fact (wordToNat (V "n")) |].


(* ============================================================================
 * implementation
 * ========================================================================= *)

Definition m := bmodule "factorial" {{
  bfunction "fact" ("n", "r" ) [factS]
    "r" <- 1;;
    [ PRE[V]  [| goodSize (wordToNat (V "r") * fact (wordToNat (V "n"))) |]
      POST[R] [| wordToNat R
                 = (wordToNat (V "r") * fact (wordToNat (V "n")))%nat |] ]
    While ("n" > 1) {
      "r" <- "r" * "n";;
      "n" <- "n" - 1
    };;
    Return "r"
  end
  }}.


(* ============================================================================
 * factorial up to 12 is not overflowing
 * - fact12 is too big to calculate, instead we calcuate factN 12 and deduce
 * ========================================================================= *)

Require Import NArith.

Fixpoint factN (n : nat) :=
  match n with
    | 0 => N.of_nat 1
    | S n' => Nmult (N.of_nat n) (factN n')
  end.

Lemma factN_12_lt_pow2_32 : (factN 12 < Npow2 32)%N.
  red; simpl; unfold Pos.compare; simpl; auto.
Qed.

Theorem factN_fact : forall n, N.to_nat (factN n) = fact n.
  induction n; simpl; auto.
  destruct (factN n) eqn:?; simpl in *.
  rewrite <- IHn; simpl; auto.
  rewrite <- IHn.
  rewrite Pnat.Pos2Nat.inj_mul, Pnat.SuccNat2Pos.id_succ; simpl; auto.
Qed.

Lemma fact_non_decreasing : forall x y, (x <= y)%nat -> (fact x <= fact y)%nat.
  induction 1; auto; simpl.
  destruct m0, x; simpl in *; auto;
  eapply Le.le_trans; try eassumption; apply Plus.le_plus_l.
Qed.
Local Hint Resolve fact_non_decreasing.
  
Lemma goodSize_def : forall x, (N.of_nat x < Npow2 32)%N -> goodSize x.
  auto.
Qed.

Lemma fact_bound : forall n, (n <= 12)%nat -> goodSize (fact n).
  intros.
  assert (goodSize (fact 12)).
  {
    apply goodSize_def.
    rewrite <- factN_fact, N2Nat.id.
    apply factN_12_lt_pow2_32.
  }
  eapply goodSize_weaken; eassumption || auto.
Qed.


(* ============================================================================
 * lemmas
 * ========================================================================= *)

Lemma fact_le_1 : forall r n : W, n <= natToW 1
          -> wordToNat r = (wordToNat r * fact (wordToNat n))%nat.
  intros; destruct_words; roundtrip.
  repeat (destruct w0; simpl; try omega).
Qed.
Hint Resolve fact_le_1.

Lemma fact_gt_0 : forall x, (0 < fact x)%nat.
  induction x; simpl; auto.
  rewrite Mult.mult_comm; simpl.
  generalize (fact x * x); intros; omega.
Qed.

Lemma fact_ge_1 : forall x, (1 <= fact x)%nat.
  induction x; simpl; auto.
  rewrite Mult.mult_comm; simpl.
  generalize (fact x * x); intros; omega.
Qed.
Local Hint Resolve fact_ge_1.

Lemma fact_ge : forall x, (x <= fact x)%nat.
  destruct x; simpl; auto.
  change (S x <= S x * fact x)%nat.
  rewrite <- Mult.mult_1_l at 1.
  rewrite Mult.mult_comm at 1.
  apply Mult.mult_le_compat_l; auto.
Qed.
Local Hint Resolve fact_ge.

Lemma rw1 : forall r n, natToW 1 < n
                 -> goodSize (wordToNat r * fact (wordToNat n))
                 -> wordToNat (r ^* n) * fact (wordToNat (n ^- natToW 1))
                    = wordToNat r * fact (wordToNat n).
  intros; destruct_words; roundtrip.
  destruct w0; simpl; try omega.
  replace (w0 - 0) with w0 by omega.
  assert (w * S w0 <= w * fact (S w0))%nat by (apply Mult.mult_le_compat_l; auto).
  rewrite wordToNat_wmult by (roundtrip; goodsize).
  roundtrip.
  rewrite <- Mult.mult_assoc; f_equal.
Qed.

Lemma rw2 : forall n : W, wordToNat (natToW 1) * fact (wordToNat n)
                          = fact (wordToNat n).
  intros; roundtrip; omega.
Qed.


(* ===========================================================================
 * Proof
 * ========================================================================= *)

Ltac finish :=
  match goal with
    | _ => solve [auto]
    | H: Regs _ Rv = _ |- _ => rewrite H
  end.

Hint Rewrite rw1 : sepFormula.
Hint Rewrite rw2 : sepFormula.
Hint Resolve fact_bound.

Theorem ok : moduleOk m.
  vcgen; sep_auto; repeat finish.
Qed.
