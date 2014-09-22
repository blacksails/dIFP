(* week_38b_induction.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working file. *)

(* ********** *)

Require Import Arith.

(* ********** *)

Check nat_ind.
(*
nat_ind : forall P : nat -> Prop,
            P 0 ->
            (forall n : nat,
               P n -> P (S n)) ->
            forall n : nat,
              P n
*)

(* ********** *)

(* An induction principle with two steps
   instead of one:
*)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (consecutive :
    forall x : nat,
      P x /\ P (S x)).
    intro x.
    induction x as [ | x' [IHx' IHSx']].

    split.
      exact H_P0.
    exact H_P1.

    split.
      exact IHSx'.
    exact (H_PSS x' IHx' IHSx').

  destruct (consecutive n) as [ly _].
  exact ly.
Qed.

(* ********** *)

(* Let us revisit evenp: *)

Definition specification_of_evenp (evenp : nat -> bool) :=
  (evenp 0 = true)
  /\
  (evenp 1 = false)
  /\
  (forall n'' : nat,
     evenp (S (S n'')) = evenp n'').

(* Uniqueness of the specification: *)

Proposition there_is_only_one_evenp :
  forall f g : nat -> bool,
    specification_of_evenp f ->
    specification_of_evenp g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_evenp.
  intros [Hf_0 [Hf_1 Hf_ij]] [Hg_0 [Hg_1 Hg_ij]] n.
(* We could write
     apply (nat_ind2 ... ... ... ... n).
   but that would be notationally daunting.
*)
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.  

  rewrite -> Hf_0.
  rewrite -> Hg_0.
  reflexivity.

  rewrite -> Hf_1.
  rewrite -> Hg_1.
  reflexivity.

  rewrite -> Hf_ij.
  rewrite -> Hg_ij.
  exact IH_n'.
Qed.

(* ********** *)

(* Let us revisit fibonacci: *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.

Theorem there_is_only_one_fibonacci_function :
  forall fib1 fib2 : nat -> nat,
    specification_of_the_fibonacci_function fib1 ->
    specification_of_the_fibonacci_function fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_the_fibonacci_function.
  intros [H_fib1_bc0 [H_fib1_bc1 H_fib1_ic]]
         [H_fib2_bc0 [H_fib2_bc1 H_fib2_ic]].
  intro n.
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.
      rewrite -> H_fib2_bc0.
      exact H_fib1_bc0.
    rewrite -> H_fib2_bc1.
    exact H_fib1_bc1.
  rewrite -> H_fib1_ic.
  rewrite -> H_fib2_ic.
  rewrite -> IH_n'.
  rewrite -> IH_Sn'.
  reflexivity.
Qed.

(* ********** *)

(* Let us revisit nat_ind: *)

Lemma nat_ind1 :
  forall P : nat -> Prop,
    P 0 ->
    (forall i : nat,
      P i -> P (S i)) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc H_ic n.
  induction n as [ | | n'' IH_n'' IH_Sn''] using nat_ind2.

  exact H_bc.

  exact (H_ic 0 H_bc).

  apply (H_ic (S n'') IH_Sn'').

  Restart.
  (* Replace "Restart." with a proof. *)

  intros P H_bc H_ic n.
  induction n as [ | n' IHn'].

  exact H_bc.

  exact (H_ic n' IHn').
Qed.

(* ********** *)

(* Exercises:

   (1) define nat_ind3 and
       (a) prove it by induction
       (b) prove it using nat_ind1
       (c) prove it using nat_ind2

   (2) using nat_ind3,
       (a) prove nat_ind1
       (b) prove nat_ind2
*)

Lemma nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    P 2 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i)) -> P (S (S (S i)))) ->
      forall n : nat,
        P n.
Proof.
  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (consecutive :
    forall x : nat,
      P x /\ P (S x) /\ P (S (S x))).
    intro x.
    induction x as [ | x' [IHx' [IHSx' IHSSx']]].
      split.
        exact H_P0.
      split.
        exact H_P1.
      exact H_P2.
    split.
      exact IHSx'.
    split.
      exact IHSSx'.
    apply (H_PSSS x' IHx' IHSx' IHSSx').
  destruct (consecutive n) as [ly _].
  exact ly.

  Restart.

  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (consecutive :
    forall x : nat,
      P x /\ P (S x) /\ P (S (S x))).
    intro x.
    induction x as [ | x' [IHx' [IHSx' IHSSx']]] using nat_ind1.
      split.
        exact H_P0.
      split.
        exact H_P1.
      exact H_P2.
    split.
      exact IHSx'.
    split.
      exact IHSSx'.
    apply (H_PSSS x' IHx' IHSx' IHSSx').
  destruct (consecutive n) as [ly _].
  exact ly.

  Restart.

  intros P H_P0 H_P1 H_P2 H_PSSS n.
  assert (consecutive :
    forall x : nat,
      P x /\ P (S x) /\ P (S (S x))).
    intro x.
    induction x as [ | | x'' [IHx'' [IHSx'' IHSSx'']] [_ [_ IHSSSx'']]] using nat_ind2.
        split.
          exact H_P0.
        split.
          exact H_P1.
        exact H_P2.
      split.
        exact H_P1.
      split.
        exact H_P2.
      apply (H_PSSS 0 H_P0 H_P1 H_P2).
    split.
      exact IHSSx''.
    split.
      exact IHSSSx''.
    apply (H_PSSS (S x'') IHSx'' IHSSx'' IHSSSx'').
  destruct (consecutive n) as [ly _].
  exact ly.
Qed.

Lemma nat_ind1_proved_using_nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    (forall i : nat,
      P i -> P (S i)) ->
    forall n : nat,
      P n.
Proof.
  intros P H_P0 H_PS.
  induction n as [ | | | n''' _ _ IHSSn'''] using nat_ind3.
        exact H_P0.
      apply (H_PS 0 H_P0).
    apply (H_PS (S 0) (H_PS 0 H_P0)).
  apply (H_PS (S (S n''')) IHSSn''').
Qed.

Lemma nat_ind2_proved_using_nat_ind3 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_P0 H_P1 H_PSS n.
  assert (consecutive :
    forall x : nat,
      P x /\ P (S x)).
    intro x.
    induction x as [ | | | x''' [IHx''' IHSx'''] [_ IHSSx'''] [_ IHSSSx''']] using nat_ind3.
          split.
            exact H_P0.
          exact H_P1.
        split.
          exact H_P1.
        apply (H_PSS 0 H_P0 H_P1).
      split.
        apply (H_PSS 0 H_P0 H_P1).
      apply (H_PSS 1 H_P1 (H_PSS 0 H_P0 H_P1)).
    split.
      exact IHSSSx'''.
    apply (H_PSS (S (S x''')) IHSSx''' IHSSSx''').
  destruct (consecutive n) as [ly _].
  exact ly.

  Restart.

  (* Hmm i guess i didn't need som of those assertions: *)
  intros P H_P0 H_P1 H_PSS n.
  induction n as [ | | | n''' IHn''' IHSn''' IHSSn'''] using nat_ind3.
        exact H_P0.
      exact H_P1.
    apply (H_PSS 0 H_P0 H_P1).
  apply (H_PSS (S n''') IHSn''' IHSSn''').

Qed.

(* ********** *)

(* end of week_38b_induction.v *)
