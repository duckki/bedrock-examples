Require Import AutoSep WordLemmas.

(* ============================================================================
 * specification
 * ========================================================================= *)

Fixpoint fact (n : nat) :=
  match n with
    | 0 => 1
    | S n' => fact n' * n
  end.

Definition factS : spec := SPEC("n") reserving 1
  PRE[V]  Emp
  POST[R] [| R = natToW (fact (wordToNat (V "n"))) |].


(* ============================================================================
 * implementation
 * ========================================================================= *)

Definition m := bmodule "factorial" {{
  bfunction "fact" ("n", "r" ) [factS]
    "r" <- 1;;
    [ PRE[V]  Emp
      POST[R] [| R = (wordToNat (V "r")
                      * fact (wordToNat (V "n")))%nat |] ]
    While ("n" > 1) {
      "r" <- "r" * "n";;
      "n" <- "n" - 1
    };;
    Return "r"
  end
  }}.


(* ============================================================================
 * lemmas
 * ========================================================================= *)

Lemma fact_gt_1 : forall (r n : W), natToW 1 < n
             -> natToW (wordToNat (r ^* n)
                        * fact (wordToNat (n ^- natToW 1)))
                = natToW (wordToNat r * fact (wordToNat n)).
  intros; destruct_words; roundtrip.
  destruct w0; simpl; try omega.
  replace (w0 - 0) with w0 by omega.
  rewrite Mult.mult_succ_r.

  rewrite ! natToWord_mult.
  roundtrip.
  rewrite <- wmult_assoc.
  f_equal.
  replace (S w0) with (1 + w0) by omega.
  rewrite ! natToWord_plus.
  rewrite ! natToWord_mult.
  words.
Qed.
Hint Resolve fact_gt_1.

Lemma fact_le_1 : forall r n : W, n <= natToW 1
          -> r = natToW (wordToNat r * fact (wordToNat n)).
  intros; destruct_words; roundtrip.
  f_equal.
  repeat (destruct w0; simpl; try omega).
Qed.
Hint Resolve fact_le_1.


(* ===========================================================================
 * Proof
 * ========================================================================= *)

Ltac finish :=
  match goal with
    | _ => solve [auto]
    | H: Regs _ Rv = _ |- _ => rewrite H
  end.

Hint Extern 1 (natToW _ = natToW _) => roundtrip; auto.

Theorem ok : moduleOk m.
  vcgen; sep_auto; repeat finish.
Qed.

Print Assumptions ok.
