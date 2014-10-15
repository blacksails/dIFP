(* week_40b_fac.v *)
(* put together after *)
(* week_36d_fac_after_todays_lecture.v *)
(* dIFP 2014-2015, Q1, Week 40 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool unfold_tactic.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Specification of the factorial function: *)

Definition specification_of_factorial (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat,
    fac (S n') = (S n') * (fac n').

(* Uniqueness of the specification: *)

Theorem there_is_only_one_factorial :
  forall fac1 fac2 : nat -> nat,
    specification_of_factorial fac1 ->
    specification_of_factorial fac2 ->
    forall n : nat,
      fac1 n = fac2 n.
Proof.
  intros fac1 fac2.
  intros specification_1 specification_2.
  unfold specification_of_factorial in specification_1.
  destruct specification_1 as [H_fac1_bc H_fac1_ic].
  unfold specification_of_factorial in specification_2.
  destruct specification_2 as [H_fac2_bc H_fac2_ic].
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> H_fac1_bc.
  rewrite -> H_fac2_bc.
  reflexivity.

  rewrite -> (H_fac1_ic n').
  rewrite -> (H_fac2_ic n').
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ********** *)

(* The factorial function in continuation-passing style: *)

Fixpoint fac_cps (ans : Type) (n : nat) (k : nat -> ans) : ans :=
  match n with
    | O => k 1
    | S n' => fac_cps ans n' (fun v => k (S n' * v))
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fac_cps_base_case :
  forall (ans : Type) (k : nat -> ans),
    fac_cps ans 0 k = k 1.
Proof.
  unfold_tactic fac_cps.
Qed.

Lemma unfold_fac_cps_induction_case :
  forall (ans : Type) (n' : nat) (k : nat -> ans),
    fac_cps ans (S n') k = fac_cps ans n' (fun v => k (S n' * v)).
Proof.
  unfold_tactic fac_cps.
Qed.

(* Lemma about resetting the continuation: *)

Lemma about_fac_cps :
  forall (n : nat) (ans : Type) (k : nat -> ans),
    fac_cps ans n k = k (fac_cps nat n (fun v => v)).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  intros ans k.
  rewrite -> unfold_fac_cps_base_case.
  rewrite -> unfold_fac_cps_base_case.
  reflexivity.

  intros ans k.
  rewrite -> unfold_fac_cps_induction_case.
  rewrite -> (IHn' ans (fun v : nat => k (S n' * v))).
  rewrite -> unfold_fac_cps_induction_case.
  rewrite -> (IHn' nat (fun v : nat => S n' * v)).
  reflexivity.
Qed.

(* Main definition: *)

Definition fac_v1 (n : nat) : nat :=
  fac_cps nat n (fun v => v).

(* The main definition satisfies the specification: *)

Theorem fac_v1_fits_the_specification_of_factorial :
  specification_of_factorial fac_v1.
Proof.
  unfold specification_of_factorial.
  unfold fac_v1.
  split.

  rewrite -> unfold_fac_cps_base_case.
  reflexivity.

  intro n'.
  rewrite -> unfold_fac_cps_induction_case.
  rewrite -> about_fac_cps.
  reflexivity.
Qed.

(* ********** *)

(* Significance of the domain of answers: *)

Require Import List.

Definition make_singleton_list (n : nat) : list nat :=
  n :: nil.

Definition list_fac_v1 (n : nat) :=
  make_singleton_list (fac_v1 n).

Definition list_fac_v2 (n : nat) :=
  make_singleton_list (fac_cps nat n (fun v => v)).

Definition list_fac_v3 (n : nat) :=
   fac_cps (list nat) n make_singleton_list.

(* ********** *)

(* end of week_41b_fac.v *)