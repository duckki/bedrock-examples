Require Import AutoSep.

(* ============================================================================
 * singly linked list : data structure definition
 * -- Bedrock way of defining data structure
 * ========================================================================= *)

Module Type SINGLY_LINKED_LIST.
  Parameter sll : list W -> W -> HProp.

  Axiom sll_extensional : forall ls p, HProp_extensional (sll ls p).

  Axiom nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].

  Axiom nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.

  Axiom cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.

  Axiom cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
End SINGLY_LINKED_LIST.

Module SinglyLinkedList : SINGLY_LINKED_LIST.
  Open Scope Sep_scope.

  Fixpoint sll (ls : list W) (p : W) : HProp :=
    match ls with
      | nil => [| p = 0 |]
      | x :: ls' => [| p <> 0 |] * Ex p', (p ==*> x, p') * sll ls' p'
    end.

  Theorem sll_extensional : forall ls (p : W), HProp_extensional (sll ls p).
    destruct ls; reflexivity.
  Qed.

  Theorem nil_fwd : forall ls (p : W), p = 0
    -> sll ls p ===> [| ls = nil |].
    destruct ls; sepLemma.
  Qed.

  Theorem nil_bwd : forall ls (p : W), p = 0
    -> [| ls = nil |] ===> sll ls p.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_fwd : forall ls (p : W), p <> 0
    -> sll ls p ===> Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p'.
    destruct ls; sepLemma.
  Qed.

  Theorem cons_bwd : forall ls (p : W), p <> 0
    -> (Ex x, Ex ls', [| ls = x :: ls' |] * Ex p', (p ==*> x, p') * sll ls' p') ===> sll ls p.
    destruct ls; sepLemma;
      match goal with
        | [ H : _ :: _ = _ :: _ |- _ ] => injection H; sepLemma
      end.
  Qed.
End SinglyLinkedList.

Import SinglyLinkedList.
Hint Immediate sll_extensional.

Definition hints : TacPackage.
  prepare (nil_fwd, cons_fwd) (nil_bwd, cons_bwd).
Defined.


(* ============================================================================
 * specification
 * -- we trust up to this section
 * -- PRE/POST lines specifies how the machine state (including the heap)
 *    changes by calling the function
 * ========================================================================= *)
Require Import Arith.Div2. (* for div2 from the Coq standard library *)

Fixpoint merge (l1 l2 : list W) :=
  match l1, l2 with
    | w1 :: l1', w2 :: l2' => w1 :: w2 :: merge l1' l2'
    | _, _ => l1 ++ l2 (* one of them is nil -> just append them *)
  end.

Definition transformS := SPEC("l") reserving 20
  Al l,
  PRE[V]  sll l (V "l") * [| l <> nil |] * [| goodSize (length l + 1) |]
  POST[_] Ex l1, Ex l2, [| l = l1 ++ l2 |]
           * [| length l2 = div2 (length l) |]
           * sll (merge l1 (rev l2)) (V "l").
  (* we require the input is not empty, because it leads to a simpler
     implementation. To support the empty list, one could first check the input
     and just return it if it is empty. *)


(* ============================================================================
 * specifications for helper functions
 * -- not trusted, just represent immediate steps
 * ========================================================================= *)

(* division-by-2 for machine words *)
Definition div2S := SPEC("n") reserving 1 
  PRE[V]  Emp
  POST[R] [| R = div2 (wordToNat (V "n")) |].
  (* The "div2" functional is for (ideal) natural numbers. In the definition here,
     we translate the machine word n to a natural number, divide it, and
     translate back to a machine word (the last translation is implicit).
     R stands for the return value. *)

Definition lengthS := SPEC("l") reserving 1
  Al l,
  PRE[V]  sll l (V "l") * [| goodSize (length l) |]
  POST[R] sll l (V "l") * [| R = length l |].
  (* The goodSize predicate means the (natural) number is no greater than UINT_MAX.
     So, the 32-bit counter (will be the return value) won't overflow. *)

Definition reverseS : spec := SPEC("x") reserving 3
  Al ls,
  PRE[V]  sll ls (V "x")
  POST[R] sll (rev ls) R.

Definition cutS := SPEC("l", "n") reserving 1 (* cuts the list into 2 lists *)
  Al l,
  PRE[V]  sll l (V "l") * [| (wordToNat (V "n") <= length l)%nat |]
           * [| wordToNat (V "n") <> 0 |]
  POST[R] Ex l1, Ex l2, sll l1 (V "l") * sll l2 R
           * [| l1 ++ l2 = l |] * [| length l1 = wordToNat (V "n") |].

Definition cutHalfS := SPEC("l") reserving 10 (* cuts in half *)
  Al l,
  PRE[V]  sll l (V "l") * [| l <> nil |] * [| goodSize (length l + 1) |]
  POST[R] Ex l1, Ex l2, sll l1 (V "l") * sll l2 R
           * [| l1 ++ l2 = l |] * [| length l2 = div2 (length l) |].
  (* We enforce some precondition that is the input list is not empty, and
     the length won't be too great so that the length function and the
     computation of ceiling won't overflow.
     -- Here, we define the half as the length of the second part is
        ``length l / 2'' *)

Definition mergeS : spec := SPEC("x", "y") reserving 2
  Al lx, Al ly,
  PRE[V]  sll lx (V "x") * sll ly (V "y") * [| (length lx >= length ly)%nat |]
  POST[_] sll (merge lx ly) (V "x").
  (* for convenience, we require the first list is not shorter than the second. *)


(* ============================================================================
 * implementation (including helper functions)
 * -- not trusted, will be verified against the specification above
 * ========================================================================= *)

Definition listM := bmodule "list" {{
  bfunction "div2"("n", "i") [div2S]
    (* emulate division-by-2 with repeated subtraction
       -- Bedrock lacks division/bit-wise operator, just yet *)
    "i" <- 0;;
    [ Al n,
      PRE[V]  [| (wordToNat (V "i") * 2 + wordToNat (V "n"))%nat = n |]
               * [| goodSize n |]
      POST[R] [| R = div2 n |] ]
    While ("n" >= 2) {
      "i" <- "i" + 1;;
      "n" <- "n" - 2  
    };;
    Return "i"
  end
  with
  bfunction "length"("l", "n") [lengthS]
    "n" <- 0;;
    [ Al l,
      PRE[V]  sll l (V "l") * [| goodSize (wordToNat (V "n") + length l) |]
      POST[R] sll l (V "l") * [| R = V "n" ^+ natToW (length l) |] ]
    While ("l" <> 0) {
      "n" <- "n" + 1;;
      "l" <-* "l" + 4
    };;
    Return "n"
  end
  with
  bfunction "cut"("l", "n", "next") [cutS]
    [ Al l,
      PRE[V]  sll l (V "l") * [| (wordToNat (V "n") <= length l)%nat |]
               * [| wordToNat (V "n") <> 0 |]
      POST[R] Ex l1, Ex l2, sll l1 (V "l") * sll l2 R
               * [| l1 ++ l2 = l |] * [| length l1 = wordToNat (V "n") |] ]
    While ("n" > 1) { (* find the last node of the first part *)
      "l" <-* "l" + 4;;
      "n" <- "n" - 1
    };;
    "next" <-* "l" + 4;;
    "l" + 4 *<- 0;; (* terminate the first part *)
    Return "next"
  end
  with
  bfunction "cutHalf"("l", "n", "tmp") [cutHalfS]
    "n" <-- Call "list"!"length"( "l" )
    [ Al l,
      PRE[V,Q] sll l (V "l") * [| Q = length l |] * [| Q <> 0 |]
                * [| goodSize (length l + 1) |]
      POST[R]  Ex l1, Ex l2, sll l1 (V "l") * sll l2 R
                * [| l1 ++ l2 = l |] * [| length l2 = div2 (length l) |] ];;

    (* when the length of the second part is n / 2, the length of
       the first part is ``ceiling (n / 2)''.
       ceiling (n / 2) is achieved by computing (n + 1) / 2 *)
    "n" <- "n" + 1;;
    "n" <-- Call "list"!"div2"( "n" )
    [ Al l,
      PRE[V,Q] sll l (V "l") * [| Q = div2 (length l + 1)%nat |] * [| Q <> 0 |]
                * [| goodSize (length l + 1) |]
      POST[R]  Ex l1, Ex l2, sll l1 (V "l") * sll l2 R
                * [| l1 ++ l2 = l |] * [| length l2 = div2 (length l) |] ];;

    "tmp" <-- Call "list"!"cut"( "l", "n" )
    [ PRE[_,Q] Emp
      POST[R]  [| R = Q |] ];;

    Return "tmp"
  end
  with
  bfunction "reverse"("x", "acc", "tmp1", "tmp2") [reverseS]
    "acc" <- 0;;
    [ Al ls', Al ls,
      PRE[V]  sll ls' (V "acc") * sll ls (V "x")
      POST[R] sll (rev ls ++ ls') R ]
    While ("x" <> 0) {
      "tmp2" <- "x";;
      "tmp1" <- "x" + 4;;
      "x" <-* "tmp1";;
      "tmp1" *<- "acc";;
      "acc" <- "tmp2"
    };;
    Return "acc"
  end
  with
  bfunction "merge"("x", "y", "p", "tmp") [mergeS]
    "p" <- "x";;
    [ Al lx, Al ly,
      PRE[V] sll lx (V "p") * sll ly (V "y")
               * [| (length ly <= length lx)%nat |]
      POST[_] sll (merge lx ly) (V "p") ]
    While ( "y" <> 0 ) {
      "tmp" <-* "p" + 4;;
      "p" + 4 *<- "y";; (* p points to y & y cannot be null *)
      "p" <- "tmp";; (* p advances *)

      "tmp" <-* "y" + 4;;
      "y" + 4 *<- "p";; (* y points to the new p *)
      "y" <- "tmp" (* y advances *)
    };;
    Return 0
  end
  with
  bfunction "transform"("l", "m") [transformS]
    "m" <-- Call "list"!"cutHalf"( "l" ) (* m will be the second half *)
    [ Al l1, Al l2,
      PRE[V,Q] sll l1 (V "l") * sll l2 Q * [| (length l1 >= length l2)%nat |]
      POST[_]  sll (merge l1 (rev l2)) (V "l") ];;

    "m" <-- Call "list"!"reverse"( "m" ) (* reverse m *)
    [ Al l1, Al l2,
      PRE[V,Q] sll l1 (V "l") * sll l2 Q * [| (length l1 >= length l2)%nat |]
      POST[_]  sll (merge l1 l2) (V "l") ];;

    Call "list"!"merge"( "l", "m" ) (* merge l and m *)
    [ PRE[_]  Emp
      POST[_] Emp ];;

    Return 0
  end
}}.


(* ============================================================================
 * Lemmas
 * ========================================================================= *)
Require Import WordLemmas.
  
Lemma div2_lem1 : forall (i n : W), natToW 2 <= n
                                           -> goodSize (wordToNat i * 2 + wordToNat n)
                                           -> goodSize (wordToNat (i ^+ natToW 1) * 2
                                                        + (wordToNat n - 2)).
  intros; destruct_words; roundtrip; goodsize.
Qed.
Hint Resolve div2_lem1.

Lemma div2_lem2 : forall (i n : W), natToW 2 <= n
                      -> goodSize (wordToNat i * 2 + wordToNat n)
                      -> wordToNat (i ^+ natToW 1) * 2 + (wordToNat n - 2)
                         = wordToNat i * 2 + wordToNat n.
  intros; destruct_words; roundtrip; omega.
Qed.
Hint Resolve div2_lem2.

Lemma div2_lem3 : forall (i n : W), n < natToW 2
                                           -> i = div2 (wordToNat i * 2 + wordToNat n).
  intros; destruct_words; roundtrip; goodsize.
  f_equal.
  rewrite Plus.plus_comm.
  destruct w0.
  simpl; rewrite Mult.mult_comm, div2_double; auto.

  destruct w0; try omega.
  rewrite Mult.mult_comm, div2_double_plus_one; auto.
Qed.
Hint Resolve div2_lem3.

Lemma length_rw1 : forall A n (l : list A), goodSize (wordToNat n + S (length l))
                       -> wordToNat (n ^+ natToW 1) + length l = wordToNat n + S (length l).
  intros; destruct_words; roundtrip; omega.
Qed.
Hint Rewrite length_rw1 : sepFormula.

Lemma length_lem1 : forall A n (l : list A), goodSize (wordToNat n + S (length l))
               -> n ^+ natToW 1 ^+ natToW (length l) = n ^+ natToW (S (length l)).
  intros; destruct_words; roundtrip.
  replace (S (length l)) with (1 + length l) by auto.
  rewrite natToWord_plus; words.
Qed.
Hint Resolve length_lem1.

Lemma cut_lem1 : forall A (l : list A) n, natToW 1 < n
                                          -> (wordToNat n <=  S (length l))%nat
                                          -> (wordToNat (n ^- natToW 1) <= length l)%nat.
  intros; destruct_words; roundtrip; auto.
Qed.
Lemma cut_lem2 : forall A (l : list A) n, natToW 1 < n
                                          -> length l = wordToNat (n ^- natToW 1)
                                          -> S (length l) = wordToNat n.
  intros; destruct_words; roundtrip; omega.
Qed.
Hint Resolve cut_lem1 cut_lem2.

Lemma div2_le : forall n, (div2 (n + 1) <= n)%nat.
  intros.
  assert (0 < n + 1)%nat by auto.
  apply lt_div2 in H.
  auto.
Qed.

Lemma div2_goodSize : forall n, goodSize n -> goodSize (div2 n).
  destruct n; auto; intros.
  assert (0 < (S n))%nat by auto.
  apply lt_div2 in H0.
  goodsize.
Qed.
Hint Resolve div2_le div2_goodSize.
  
Lemma cutHalf_lem1 : forall A (l : list A), l <> nil
                                            -> goodSize (length l + 1)
                                            -> natToW (length l) <> natToW 0.
  destruct l; simpl; auto; intros.
  intro; apply H; clear H; roundtrip; congruence.
Qed.
Hint Resolve cutHalf_lem1.

Lemma cutHalf_lem2 : forall A (l : list A), length l <> 0 -> goodSize (length l + 1)
                         -> natToW (div2 (wordToNat (natToW (length l) ^+ natToW 1)))
                            <> natToW 0.
  intros; roundtrip.
  assert (goodSize (div2 (length l + 1))) by goodsize.
  destruct l; auto; simpl in *.
  replace (length l + 1) with (1 + length l) in * by omega; simpl in *.
  intro; roundtrip; congruence.
Qed.
Hint Resolve cutHalf_lem2.

Lemma div2_plus_1 : forall x y, goodSize (x + y + 1)
                                  -> x = div2 (x + y + 1)
                                  -> y = div2 (x + y).
  intros; destruct (Even.even_odd_dec (x + y)).
  replace (x + y + 1) with (S (x + y)) in * by omega.
  rewrite <- even_div2 in * by auto.
  generalize (even_double _ e); unfold double; omega.

  replace (x + y + 1) with (S (x + y)) in * by omega.
  rewrite <- odd_div2 in * by auto.
  generalize (odd_double _ o); unfold double; omega.
Qed.

Lemma cutHalf_lem3 : forall x y z, goodSize (x + y + 1)
                                  -> z = natToW (div2 (x + y + 1))
                                  -> x = wordToNat z
                                  -> y = div2 (x + y).
  intros; apply div2_plus_1; auto.
  rewrite H0 in *.
  destruct_words; roundtrip; auto.
Qed.

Lemma transform_lem1 : forall x y, y = div2 (x + y) -> (x >= y)%nat.
  intros; destruct (Even.even_odd_dec (x + y)).
  generalize (even_double _ e); unfold double; omega.
  generalize (odd_double _ o); unfold double; omega.
Qed.
Hint Resolve transform_lem1.


(* ============================================================================
 * Proof
 * -- Hint and Ltac are the automation facility of the underling tool, Coq.
 * -- The correctness theorem is at the bottom.
 * ========================================================================= *)

Hint Rewrite app_nil_r : sepFormula.
Hint Rewrite <- app_assoc : sepFormula.

Hint Extern 1 (_ = _) => words.
Hint Extern 1 (_ :: _ = _ :: _ ) => f_equal.

Ltac wrongCase :=
  match goal with
    | H : context[Assign] |- _ => generalize dependent H; evaluate hints
  end; intros; subst; simpl in *; omega.

Ltac splitter :=
  match goal with
    | H : context[Assign] |- _ => generalize dependent H; evaluate hints
  end; intros;
  match goal with
    | _: (_ <= length ?l)%nat, _: context[sll ?l ?p] |- _
      => destruct (eq_W_dec p 0)
  end; try wrongCase.

Ltac finish :=
  match goal with
    | H: Regs ?st Rv = _ |- _ => rewrite H
    | _ => solve [auto]
    | _ => solve [simpl in *; roundtrip; auto; omega]
    | _ => solve [goodsize]
    | _ => rewrite app_length in *; eapply cutHalf_lem3; eassumption
    | _ => rewrite app_length in *; solve [auto]
    | _ => autorewrite with list; assumption
  end.

Theorem listM_correct : moduleOk listM.
  vcgen; try enterFunction; post; try splitter; try solve [sep hints; repeat finish].
  (* - vcgen generates mathematical proof obligations from the (annotated) code above.
     - The other names are automation scripts. Some of them are defined right above,
       and some are provided by the Bedrock library.
     - proofs are hightly automated using Bedrock automation and the simple scripts above *)

  (* Here we have 2 left-over subgoals, where my automation failed above.
     This could be resolved by adding some more annotations in the code, and
     make my automation script more sophisticated. For now, I just manually
     guided the automation towards the right direction below. *)
  Focus.
  evaluate hints.
  exists x9, x6.
  solve [sep hints; repeat finish].

  Focus.
  evaluate hints.
  exists x1, x2.
  solve [sep hints; repeat finish].
Qed.
