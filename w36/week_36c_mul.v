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
  (mul 1 1 === 1).

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
