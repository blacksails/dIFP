(* week_36c_mul.v *)
(* dIFP 2014-2015, Q1, Week 36 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool.

Require Import unfold_tactic.

(* ********** *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_multiplication (mul : nat -> nat -> nat) :=
  (mul 0 0 === 0)
  &&
  (mul 0 1 === 0)
  &&
  (mul 1 1 === 1)
  &&
  (mul 1 2 === 2)
  &&
  (mul 2 1 === 2)
  &&
  (mul 21 2 === 42).

(* Exercise 0: flesh out the unit tests above with more tests. *)

(* mult is the built-in multiplication in Coq (infix notation: * ): *)
Compute (unit_tests_for_multiplication mult).
(*
     = true
     : bool
*)

(* Exercise 1: why is there a space in the comment just above
   on the right of the infix notation for multiplication?
*)
(* Because otherwise you would end the comment when closing the parentesis *)
(* ********** *)

Definition specification_of_multiplication (mul : nat -> nat -> nat) :=
  (forall j : nat,
    mul O j = 0)
  /\
  (forall i' j : nat,
    mul (S i') j = j + (mul i' j)).

(* ********** *)

(* For the following exercise,
   the following lemmas from the Arith library might come handy:
   plus_0_l, plus_0_r, plus_comm, and plus_assoc.
*)

Check plus_0_l.

(* Exercise:

   * show that 0 is left-absorbant for multiplication
     (aka mult_0_l in Arith)

   * show that 0 is right-absorbant for multiplication
     (aka mult_0_r in Arith)

   * show that 1 is left-neutral for multiplication
     (aka mult_1_l in Arith)

   * show that 1 is right-neutral for multiplication
     (aka mult_1_r in Arith)

   * show that multiplication is commutative
     (aka mult_comm in Arith)

   * show that the specification of multiplication is unique

   * implement multiplication,
     verify that your implementation passes the unit tests, and
     prove that your implementation satisfies the specification
*)

Proposition mult_bc_left :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall n : nat,
      mul 0 n = 0.
Proof.
  intro mul.
  intro S_mul.
  intro n.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [H_mul_bc _].
  apply (H_mul_bc n).
Qed.

Check plus_0_l.

Proposition mult_bc_right :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall n : nat,
      mul n 0 = 0.
Proof.
  intros mul S_mul.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [H_mul_bc H_mul_ic].
  intro i.
  induction i as [ | n' IHn'].
    apply (H_mul_bc 0).
  rewrite -> (H_mul_ic n' 0).
  rewrite -> IHn'.
  rewrite -> (plus_0_l 0).
  reflexivity.
Qed.

Proposition mult_ic_left :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i j : nat,
      mul (S i) j = j + (mul i j).
Proof.
  intros mul S_mul i j.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [_ H_mul_ic].
  apply (H_mul_ic i j).
Qed.

Check plus_Sn_m.
Check plus_assoc.
Check plus_comm.

Proposition mult_ic_right :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i j : nat,
      mul i (S j) = i + (mul i j).
Proof.
  intros mul S_mul i j.
  unfold specification_of_multiplication in S_mul.
  destruct S_mul as [H_mul_bc H_mul_ic].
  induction i as [ | n' IHn'].
    rewrite -> (H_mul_bc (S j)).
    rewrite -> (plus_0_l (mul 0 j)).
    symmetry.
    apply (H_mul_bc j).
  rewrite -> (H_mul_ic n' (S j)).
  rewrite -> (H_mul_ic n' j).
  rewrite -> IHn'.
  rewrite -> (plus_Sn_m j (n' + mul n' j)).
  rewrite -> (plus_Sn_m n' (j + mul n' j)).
  rewrite -> (plus_assoc j n' (mul n' j)).
  rewrite -> (plus_assoc n' j (mul n' j)).
  rewrite -> (plus_comm j n').
  reflexivity.
Qed.

Proposition mult_is_commutative :
  forall (mul : nat -> nat -> nat),
    specification_of_multiplication mul ->
    forall i j : nat,
      mul i j = mul j i.
Proof.
  intros mul S_mul i j.
  induction i as [ | i' IHi'].
    rewrite -> (mult_bc_left mul S_mul j).
    rewrite -> (mult_bc_right mul S_mul j).
    reflexivity.
  rewrite -> (mult_ic_left mul S_mul).
  rewrite -> (mult_ic_right mul S_mul).
  rewrite -> IHi'.
  reflexivity.
Qed.

Proposition there_is_only_one_mult :
  forall mul1 mul2 : nat -> nat -> nat,
    specification_of_multiplication mul1 ->
    specification_of_multiplication mul2 ->
    forall i j : nat,
      mul1 i j = mul2 i j.
Proof.
  intros mul1 mul2 S_mul1 S_mul2 i j.
  induction i.
    rewrite -> (mult_bc_left mul1 S_mul1 j).
    rewrite -> (mult_bc_left mul2 S_mul2 j). 
    reflexivity.
  rewrite -> (mult_ic_left mul1 S_mul1 i j).
  rewrite -> (mult_ic_left mul2 S_mul2 i j).
  rewrite -> IHi.
  reflexivity.
Qed.

Fixpoint my_mult (i j : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => plus j (my_mult i' j)
  end.

Compute (unit_tests_for_multiplication my_mult).

Lemma unfold_my_mult_bc :
  forall n : nat,
    my_mult 0 n = 0.
Proof.
  unfold_tactic my_mult.
Qed.

Lemma unfold_my_mult_ic :
  forall n' m : nat, 
    my_mult (S n') m = m + my_mult n' m.
Proof.
  unfold_tactic my_mult.
Qed.

Theorem my_mult_satisfies_spec :
  specification_of_multiplication my_mult.
Proof.
  unfold specification_of_multiplication.
  split.
    apply unfold_my_mult_bc.
  apply unfold_my_mult_ic.
Qed.

(* ********** *)

(* Exercise for the over-achievers:

   In no particular order,

   * show that multiplication is associative
     (aka mult_assoc in Arith),

   * show that multiplication distributes over addition on the left
     (aka mult_plus_distr_l in Arith), and

   * show that multiplication distributes over addition on the right
     (aka mult_plus_distr_r in Arith).
*)

(* ********** *)

(* Exercise for the over-achievers with time on their hands:
   repeat the exercises above with our own implementation
   of the addition function.
   (You will first need to compile week_36b_add.v with coqc.) 
*)

(*
Require Import week_36b_add.

Definition specification_of_multiplication' (mul : nat -> nat -> nat) :=
  (forall j : nat,
    mul O j = 0)
  /\
  (forall add : nat -> nat -> nat,
     specification_of_addition add ->
     forall i' j : nat,
       mul (S i') j = add j (mul i' j)).
*)

(* ********** *)

(* end of week_36c_mul.v *)
