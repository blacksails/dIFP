(* week_38b_induction.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

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
Admitted.
(* Replace "Admitted." with a proof. *)

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
  induction n as [ | | n' IH_n' IH_Sn'] using nat_ind2.  
Abort.
(* Replace "Abort." with a proof. *)

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
Abort.
(* Replace "Abort." with a proof. *)

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

  Restart.
  (* Replace "Restart." with a proof. *)

  intros P H_bc H_ic n.
  induction n as [ | n' IHn'].
Abort.
(* Replace "Abort." with a proof. *)

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

(* ********** *)

(* end of week_38b_induction.v *)
