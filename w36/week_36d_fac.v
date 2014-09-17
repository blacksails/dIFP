(* week_36d_fac.v *)
(* dIFP 2014-2015, Q1, Week 36 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool.

Require Import unfold_tactic.

(* ********** *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_factorial (fac : nat -> nat) :=
  (fac 0 === 0)
  &&
  (fac 1 === 1)
  &&
  (fac 5 === 120).

(* ********** *)

Definition specification_of_factorial (fac : nat -> nat) :=
  (fac O = 1)
  /\
  (forall n' : nat,
    fac (S n') = (S n') * (fac n')).

Proposition there_is_only_one_factorial_function :
  forall fac1 fac2 : nat -> nat,
    specification_of_factorial fac1 ->
    specification_of_factorial fac2 ->
    forall n : nat,
      fac1 n = fac2 n.
Proof.
Abort.

(* ********** *)

Fixpoint fac_ds (n : nat) :=
  match n with
    | 0 => 1
    | S n' => (S n') * (fac_ds n')
  end.

Definition fac_v0 (n : nat) :=
  fac_ds n.

Compute unit_tests_for_factorial fac_v0.

(* The two mandatory unfold lemmas: *)

Lemma unfold_fac_ds_bc :
  fac_ds 0 = 1.
Proof.
  unfold_tactic fac_ds.
Qed.

Lemma unfold_fac_ds_ic :
  forall n' : nat,
    fac_ds (S n') = (S n') * (fac_ds n').
Proof.
  unfold_tactic fac_ds.
Qed.

Theorem fac_v0_satisfies_the_specification_of_factorial :
  specification_of_factorial fac_v0.
Proof.
Abort.

(* ********** *)

Fixpoint fac_acc (n a : nat) :=
  match n with
    | 0 => a
    | S n' => fac_acc n' (S n' * a)
  end.

Definition fac_v1 (n : nat) :=
  fac_acc n 1.

Compute unit_tests_for_factorial fac_v1.

(* The two mandatory unfold lemmas: *)

Lemma unfold_fac_acc_bc :
  forall a : nat,
    fac_acc 0 a = a.
Proof.
  unfold_tactic fac_acc.
Qed.

Lemma unfold_fac_acc_ic :
  forall n' a : nat,
    fac_acc (S n') a = fac_acc n' (S n' * a).
Proof.
  unfold_tactic fac_acc.
Qed.

Theorem fac_v1_satisfies_the_specification_of_factorial_first_try :
  specification_of_factorial fac_v1.
Proof.
Abort.

(* ********** *)

Fixpoint fac_cps (ans : Type) (n : nat) (k : nat -> ans) :=
  match n with
    | 0 => k 1
    | S n' => fac_cps ans n' (fun v => k (S n' * v))
  end.

Definition fac_v2 (n : nat) :=
  fac_cps nat n (fun v => v).

Compute unit_tests_for_factorial fac_v2.

(* The two mandatory unfold lemmas: *)

Lemma unfold_fac_cps_bc :
  forall (ans : Type)
         (k : nat -> ans),
    fac_cps ans 0 k = k 1.
Proof.
  unfold_tactic fac_cps.
Qed.

Lemma unfold_fac_cps_ic :
  forall (ans : Type)
         (n' : nat)
         (k : nat -> ans),
    fac_cps ans (S n') k = fac_cps ans n' (fun v => k (S n' * v)).
Proof.
  unfold_tactic fac_cps.
Qed.

Lemma about_fac_cps :
  forall (n : nat)
         (k : nat -> nat),
    fac_cps nat n k = k (fac_cps nat n (fun v => v)).
Proof.
  intro n.
  induction n as [ | n' IHn'].

  intro k.
  rewrite -> (unfold_fac_cps_bc nat k).
  rewrite -> (unfold_fac_cps_bc nat (fun v : nat => v)).
  reflexivity.

  intro k.
  rewrite -> (unfold_fac_cps_ic nat n' k).
  rewrite -> (IHn' (fun v : nat => k (S n' * v))).
  rewrite -> (unfold_fac_cps_ic nat n' (fun v : nat => v)).
  rewrite -> (IHn' (fun v : nat => S n' * v)).
  reflexivity.
Qed.

Theorem fac_v2_satisfies_the_specification_of_factorial :
  specification_of_factorial fac_v2.
Proof.
  unfold specification_of_factorial.
  unfold fac_v2.
  split.
  
  apply (unfold_fac_cps_bc nat (fun v => v)).

  intro n'.
  rewrite -> (unfold_fac_cps_ic nat n' (fun v => v)).
  rewrite -> (about_fac_cps n' (fun v => S n' * v)).
  reflexivity.
Qed.

(* ********** *)

(* end of week_36d_fac.v *)
