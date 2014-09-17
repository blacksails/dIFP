(* week_36d_fac_after_todays_lecture.v *)
(* dIFP 2014-2015, Q1, Week 36 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool.

Require Import unfold_tactic.

(* ********** *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_factorial (fac : nat -> nat) :=
  (fac 0 === 1)
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
  intros fac1 fac2 S_fac1 S_fac2 n.
  unfold specification_of_factorial in S_fac1.
  destruct S_fac1 as [H_fac1_bc H_fac1_ic].
  unfold specification_of_factorial in S_fac2.
  destruct S_fac2 as [H_fac2_bc H_fac2_ic].
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
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic fac_ds.
Qed.

Lemma unfold_fac_ds_ic :
  forall n' : nat,
    fac_ds (S n') = (S n') * (fac_ds n').
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic fac_ds.
Qed.

Theorem fac_v0_satisfies_the_specification_of_factorial :
  specification_of_factorial fac_v0.
Proof.
  unfold specification_of_factorial.
  split.

  unfold fac_v0.
  apply unfold_fac_ds_bc.

  intro n'.
  unfold fac_v0.
  apply (unfold_fac_ds_ic n').
Qed.

(* ********** *)

(* Version with an accumulator: *)

Fixpoint fac_acc (n a : nat) :=
  match n with
    | 0 => a
    | S n' => fac_acc n' (S n' * a)
  end.

Definition fac_v1 (n : nat) :=
  fac_acc n 1.

Compute unit_tests_for_factorial fac_v1.
(*
     = true
     : bool
*)

(* The two mandatory unfold lemmas: *)

Lemma unfold_fac_acc_bc :
  forall a : nat,
    fac_acc 0 a = a.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic fac_acc.
Qed.

Lemma unfold_fac_acc_ic :
  forall n' a : nat,
    fac_acc (S n') a = fac_acc n' (S n' * a).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic fac_acc.
Qed.

Theorem fac_v1_satisfies_the_specification_of_factorial_first_try :
  specification_of_factorial fac_v1.
Proof.
  unfold specification_of_factorial.
  unfold fac_v1.
  split.

  apply (unfold_fac_acc_bc 1).

  intro n'.
  rewrite -> (unfold_fac_acc_ic n' 1).
  rewrite -> (mult_1_r (S n')).
  (* Now what? *)
  (* We need something stronger! *)
Abort.

(* Educated guesswork (basically the goal just above): *)
Lemma about_fac_acc_tentative :
  forall n a : nat,
    fac_acc n a = a * (fac_acc n 1).
Proof.
(* Let's see whether that will do. *)
Admitted.

Theorem fac_v1_satisfies_the_specification_of_factorial_second_try :
  specification_of_factorial fac_v1.
Proof.
  unfold specification_of_factorial.
  unfold fac_v1.
  split.

  apply (unfold_fac_acc_bc 1).

  intro n'.
  rewrite -> (unfold_fac_acc_ic n' 1).
  rewrite -> (mult_1_r (S n')).
  rewrite -> (about_fac_acc_tentative n' (S n')).

  reflexivity.
  (* Hurrah, it works. *)
Abort.

(* Now for proving it: *)
Lemma about_fac_acc :
  forall n a : nat,
    fac_acc n a = a * (fac_acc n 1).
Proof.
  intros n a.
  induction n as [ | n' IHn'].

  rewrite -> (unfold_fac_acc_bc a).
  rewrite -> (unfold_fac_acc_bc 1).
  rewrite -> mult_1_r.
  reflexivity.

  rewrite -> (unfold_fac_acc_ic n' a).
  rewrite -> (unfold_fac_acc_ic n' 1).
  rewrite -> (mult_1_r (S n')).

  Restart.

  intros n.
  induction n as [ | n' IHn'].

  intro a.
  rewrite -> (unfold_fac_acc_bc a).
  rewrite -> (unfold_fac_acc_bc 1).
  rewrite -> mult_1_r.
  reflexivity.
 
  intro a.
  rewrite -> (unfold_fac_acc_ic n' a).
  rewrite -> (unfold_fac_acc_ic n' 1).
  rewrite -> (mult_1_r (S n')).
  rewrite -> (IHn' (S n' * a)).
  rewrite -> (IHn' (S n')).
  rewrite -> (mult_comm (S n') a).
  Check mult_assoc.
(*
mult_assoc
     : forall n m p : nat, n * (m * p) = n * m * p
*)
  symmetry.
  apply (mult_assoc a (S n') (fac_acc n' 1)).
Qed.

Theorem fac_v1_satisfies_the_specification_of_factorial :
  specification_of_factorial fac_v1.
Proof.
  unfold specification_of_factorial.
  unfold fac_v1.
  split.

  apply (unfold_fac_acc_bc 1).

  intro n'.
  rewrite -> (unfold_fac_acc_ic n' 1).
  rewrite -> (mult_1_r (S n')).
  rewrite -> (about_fac_acc n' (S n')).
  reflexivity.
Qed.

(* ********** *)

(* Continuation-passing style (for the advanced souls): *)

Fixpoint fac_cps (ans : Type) (n : nat) (k : nat -> ans) :=
  match n with
    | 0 => k 1
    | S n' => fac_cps ans n' (fun v => k (S n' * v))
  end.

Definition fac_v2 (n : nat) :=
  fac_cps nat n (fun v => v).

Compute unit_tests_for_factorial fac_v2.
(*
     = true
     : bool
*)

(* The two mandatory unfold lemmas: *)

Lemma unfold_fac_cps_bc :
  forall (ans : Type)
         (k : nat -> ans),
    fac_cps ans 0 k = k 1.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic fac_cps.
Qed.

Lemma unfold_fac_cps_ic :
  forall (ans : Type)
         (n' : nat)
         (k : nat -> ans),
    fac_cps ans (S n') k = fac_cps ans n' (fun v => k (S n' * v)).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic fac_cps.
Qed.

(* Useful Eureka lemma: *)
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

(* end of week_36d_fac_after_todays_lecture.v *)
