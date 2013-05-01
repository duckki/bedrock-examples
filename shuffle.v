Set Implicit Arguments.
Require Import AutoSep WordLemmas.

(* ============================================================================
 * specification
 * - The "shuffle" function arbitrarily modifies the input array.
 * - The "test" function modifies the input array so that
     the array contains a zero.
 * ========================================================================= *)

Definition shuffleS : spec := SPEC("a", "sz") reserving 0  
  Al l,
  PRE[V]  array l (V "a") * [| length l = wordToNat (V "sz") |]
  POST[_] Ex l', array l' (V "a") * [| length l = length l' |].

Definition testS : spec := SPEC("a", "sz") reserving 10
  Al l,
  PRE[V]  array l (V "a") * [| length l = wordToNat (V "sz") |]
  POST[_] Ex l', array l' (V "a") * [| length l = length l' |]
           * [| In $0 l' |].


(* ============================================================================
 * implementation
 * - "shuffle" is a black box function
 * - "test" repeatedly called shuffle and check if the modified array has
     a zero in it.
 * ========================================================================= *)

Definition m := bmodule "shuffle" {{
  bfunction "shuffle"("a", "sz") [shuffleS]
    Diverge
  end
  with
  bfunction "test"("a", "sz", "i", "p") [testS]
    [
      Al l,
      PRE[V]  array l (V "a") * [| length l = wordToNat (V "sz") |]
      POST[_] Ex l', array l' (V "a") * [| length l = length l' |]
               * [| In $0 l' |]
    ]
    While (0 = 0) {
      "i" <- 0;;
      [
        Al l', Al l,
        PRE[V]  array (l' ++ l) (V "a")
                 * [| (length l' + length l)%nat = wordToNat (V "sz") |]
                 * [| length l' = wordToNat (V "i") |]
        POST[_] Ex l'', array l'' (V "a")
                 * [| (length l' + length l)%nat = length l'' |]
                 * [| In $0 l'' |]
      ]
      While ( "i" < "sz" ) {
        "p" <- 4 * "i";;   (* offset *)
        "p" <- "a" + "p";; (* base + offset *)
        "p" <-* "p";;      (* the value at the offset *)
        If ("p" = 0) {
          Return 0
        } else {
          Skip
        };;
        "i" <- "i" + 1
      };;

      Call "shuffle"!"shuffle"( "a", "sz" )
      [
        Al l,
        PRE[V]  array l (V "a") * [| length l = wordToNat (V "sz") |]
        POST[_] Ex l', array l' (V "a") * [| length l = length l' |]
                 * [| In $0 l' |]
      ]
    }
  end
  }}.


(* ============================================================================
 * lemmas
 * ========================================================================= *)

Lemma unstuck1 : forall (l l' : list W) (sz i : W),
                     length l + length l' = wordToNat sz
                     -> i < sz -> i < natToW (length (l ++ l')).
  intros.
  autorewrite with list.
  rewrite H.
  unfold natToW.
  rewrite natToWord_wordToNat; auto.
Qed.

Lemma unstuck1' : forall (l : list W) (sz i : W),
                     length l + length (@nil W) = wordToNat sz
                     -> length l = wordToNat i
                     -> i < sz -> False.
  intros.
  contradict H1.
  pre_nomega.
  rewrite <- H, <- H0.
  simpl; omega.
Qed.

Lemma lem1 : forall len (i sz : W), i < sz
                    -> len = wordToNat i
                    -> len + 1 = wordToNat (i ^+ natToW 1).
  intros; subst.
  eapply next; eassumption.
Qed.

Lemma split_list: forall A (i: nat) (ls:list A),
                    (i <= length ls)%nat
                    -> exists ls1 ls2, length ls1 = i /\ ls = ls1 ++ ls2.
  induction i.
  destruct ls; intros; simpl in *.
  do 2 exists nil; simpl; auto.
  exists nil; exists (a :: ls); simpl; auto.

  intros.
  assert (i <= length ls)%nat by omega.
  specialize (IHi ls H0).
  destruct IHi.
  destruct H1.
  destruct H1.
  destruct x0; simpl in *; subst; autorewrite with list in *; [omega | ].
  exists (x ++ a::nil).
  exists x0.
  rewrite <- app_assoc; autorewrite with list; simpl; intuition.
Qed.

Lemma selN_app_hd : forall ls1 ls2 n,
                  length ls1 = n ->  Array.selN (ls1 ++ ls2) n = hd $0 ls2.
  induction ls1; simpl; intuition.
  destruct ls2; subst; simpl; intuition.
  destruct n; simpl; auto; discriminate.
Qed.

Lemma selN_In : forall i x l, (i < length l)%nat -> selN l i = x
                           -> In x l.
  intros.
  assert (i <= length l)%nat by omega.
  edestruct split_list as [? [? [] ] ]; try eassumption.
  subst.
  rewrite selN_app_hd by auto.
  destruct x1; autorewrite with list in *; try omega; simpl.
  apply in_or_app; simpl; auto.
Qed.      
      
Lemma Array_sel_In : forall (i : W) l, i < natToW (length l) -> Array.sel l i = 0
                           -> In $0 l.
  unfold Array.sel; intros.
  eapply selN_In; try eassumption.
  apply lt_natToW; eassumption.
Qed.


(* ============================================================================
 * proof
 * ========================================================================= *)

Ltac unstuck :=
    match goal with
      | H : context[Assign] |- _ => generalize dependent H; evaluate auto_ext
    end; intros;
    match goal with
      | _: ?i < ?sz, _: context[array (?l' ++ ?l) _] |- _
        => assert (i < natToW (length (l' ++ l))) by (eapply unstuck1; eassumption)
    end.

Hint Extern 3 (@eq W _ _) => words.

Theorem ok : moduleOk m.
  vcgen.

  Ltac t := solve [sep_auto; auto].

  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  t.
  {
    sep_auto; auto.
    instantiate (2:=nil).
    simpl; eassumption.
    simpl; auto.
    sepLemma.
    simpl in *; auto.
  }
  t.
  {
    post; unstuck.
    destruct x2.
    exfalso; eapply unstuck1'; eassumption.
    exists (x1 ++ w :: nil), x2.
    sep_auto; auto.
    {
      autorewrite with list; simpl; omega.
    }
    {
      autorewrite with list; simpl.
      eapply lem1; eassumption.
    }
    {
      rewrite <- app_assoc; sepLemma.
    }
    {
      rewrite <- H15; simpl; autorewrite with list; simpl; omega.
    }
  }
  solve [post; unstuck; sep_auto].
  solve [post; unstuck; sep_auto].
  solve [post; unstuck; sep_auto].
  {
    (* found 0 in the inner loop *)
    post; unstuck; sep_auto; auto.
    autorewrite with list; auto.
    eapply Array_sel_In; eassumption.
  }
  {
    post; unstuck; sep_auto; auto.
  }
  t.
  {
    sep_auto; auto.
    autorewrite with list; auto.
    rewrite <- H14, <- H11; autorewrite with list; auto.
    rewrite <- H14, <- H18; autorewrite with list; auto.
  }
  t.
Qed.
