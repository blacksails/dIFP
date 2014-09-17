(* week_36b_add.v *)
(* dIFP 2014-2015, Q1, Week 36 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* Learning goals of this week:

   * using coqc

   * unit tests

   * booleans

   * infix notation

   * specifications of functions

   * properties of functions that satisfy a specification

   * the unfold tactic to replace an identifier by its denotation

   * structural induction over natural numbers

   * revert as an inverse of intro

   * uniqueness of a specification

   * structurally recursive definitions over natural numbers

   * unfold lemmas

   * unfold_tactic

   * checking than an implementation satisfies a specification

*)

(* ********** *)

Require Import Arith.

(* ********** *)

Definition unit_tests_for_addition_v0 (add : nat -> nat -> nat) :=
  (add 0 3 = 3)
  /\
  (add 1 3 = 4)
  /\
  (add 2 3 = 5)
  /\
  (add 3 0 = 3).

(* ********** *)

(* plus is Coq's built-in addition function (infix notation: +): *)

Check plus.
(*
plus
     : nat -> nat -> nat
*)

Compute (unit_tests_for_addition_v0 plus).
(*
     = 3 = 3 /\ 4 = 4 /\ 5 = 5 /\ 3 = 3
     : Prop
*)

(* That's unpractical.
   Let's rather compute over Booleans: *)

Require Import Bool.

Check true.
(*
true
     : bool
*)

Check false.
(*
false
     : bool
*)

(* andb is Coq's built-in Boolean conjunction function (infix notation: &&): *)

Check andb.
(*
andb
     : bool -> bool -> bool
*)

Compute (andb true true, andb true false, andb false false, andb false false).
(*
     = (true, false, false, false)
     : bool * bool * bool * bool
*)

Compute (true && true, true && false, false && false, false && false).
(*
     = (true, false, false, false)
     : bool * bool * bool * bool
*)

(* orb is Coq's built-in Boolean conjunction function (infix notation: ||): *)

Check orb.
(*
orb
     : bool -> bool -> bool
*)

Compute (orb true true, orb true false, orb false false, orb false false).
(*
     = (true, true, false, false)
     : bool * bool * bool * bool
*)

Compute (true || true, true || false, false || false, false || false).
(*
     = (true, true, false, false)
     : bool * bool * bool * bool
*)

(* The equality predicate for natural numbers: *)

Check eq_nat.
(*
eq_nat
     : nat -> nat -> Prop
*)

Compute (eq_nat 2 2, eq_nat 2 3).
(*
     = (True, False)
     : Prop * Prop
*)

(* The equality Boolean function for natural numbers: *)

Check beq_nat.
(*
beq_nat
     : nat -> nat -> bool
*)

Compute (beq_nat 2 2, beq_nat 2 3).
(*
     = (true, false)
     : bool * bool
*)

(* A second version of the unit tests for addition: *)

Definition unit_tests_for_addition_v1 (add : nat -> nat -> nat) :=
  (beq_nat (add 0 3) 3)
  &&
  (beq_nat (add 1 3) 4)
  &&
  (beq_nat (add 2 3) 5)
  &&
  (beq_nat (add 3 0) 3).

Compute (unit_tests_for_addition_v1 plus).
(*
     = true
     : bool
*)

(* A bit of syntactic sugar: *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

(* Now the unit tests are even readable: *)

Definition unit_tests_for_addition_v2 (add : nat -> nat -> nat) :=
  (add 0 3 === 3)
  &&
  (add 1 3 === 4)
  &&
  (add 2 3 === 5)
  &&
  (add 3 0 === 3).

Compute (unit_tests_for_addition_v2 plus).
(*
     = true
     : bool
*)

(* Yup, readable and practical: *)

Definition unit_tests_for_addition := unit_tests_for_addition_v2.

Compute (unit_tests_for_addition plus).
(*
     = true
     : bool
*)

(* ********** *)

(* A useful lemma: *)

Lemma f_equal_S :
  forall x y : nat,
    x = y -> S x = S y.
Proof.
  intros x y.
  intros H_xy.
  rewrite -> H_xy.
  reflexivity.
Qed.

(* ********** *)

(* The specification of the addition function, 
   by induction over natural numbers:
*)

Definition specification_of_addition (add : nat -> nat -> nat) :=
  (forall j : nat,
    add O j = j)
  /\
  (forall i' j : nat,
    add (S i') j = S (add i' j)).

(* ********** *)

(* A collection of properties
   about a function that satisfies the specification of addition:
*)

Proposition addition_bc_left :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall j : nat,
      add 0 j = j.
Proof.
  intros add.
  intros S_add.
  intro j.
  unfold specification_of_addition in S_add.
  destruct S_add as [H_add_bc _].
  apply (H_add_bc j).
Qed.

(* ********** *)

Proposition addition_ic_left :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall i' j : nat,
      add (S i') j = S (add i' j).
Proof.
  intros add.
  intros S_add.
  intros i' j.
  unfold specification_of_addition in S_add.
  destruct S_add as [_ H_add_ic].
  apply (H_add_ic i' j).
Qed.

Corollary addition_ic_left_twice :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall i'' j : nat,
      add (S (S i'')) j = S (S (add i'' j)).
Proof.
  intros add S_add i'' j.
  rewrite -> (addition_ic_left add S_add (S i'') j).
  rewrite -> (addition_ic_left add S_add i'' j).
  reflexivity.
Qed.


(* ********** *)

Proposition addition_bc_right :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall i : nat,
      add i 0 = i.
Proof.
  intros add S_add i.
  destruct i as [ | i'].
  apply (addition_bc_left add S_add 0).
  destruct i' as [|i'].

  Restart.

  intros add S_add.
  unfold specification_of_addition in S_add. 
  destruct S_add as [H_add_bc H_add_ic].
  intros i.
Abort.

(* ********** *)

Proposition addition_ic_right :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall i j : nat,
      add i (S j) = S (add i j).
Proof.

Corollary addition_ic_right_twice :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall i j : nat,
      add i (S (S j)) = S (S (add i j)).
Proof.
Abort.

(* ********** *)

(* Exercise:
   state and prove that zero is left-neutral for addition.
*)

(*
Proposition zero_is_neutral_for_addition_on_the_left :
  ...
*)

(* ********** *)

(* Exercise:
   state and prove that zero is right-neutral for addition.
*)

(*
Proposition zero_is_neutral_for_addition_on_the_right :
  ...
*)

(* ********** *)

Proposition addition_is_commutative :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall i j : nat,
      add i j = add j i.
Proof.
Abort.

(* ********** *)

Proposition addition_is_associative :
  forall (add : nat -> nat -> nat),
    specification_of_addition add ->
    forall i j k : nat,
      add i (add j k) = add (add i j) k.
Proof.
Abort.

(* ********** *)

Proposition there_is_only_one_addition :
  forall add1 add2 : nat -> nat -> nat,
    specification_of_addition add1 ->
    specification_of_addition add2 ->
    forall m n : nat,
      add1 m n = add2 m n.
Proof.
Abort.

(* ********** *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | 0 => j
    | S i' => S (add_v1 i' j)
  end.

Compute (unit_tests_for_addition add_v1).
(*
     = true
     : bool
*)

Require Import "unfold_tactic".

(* The two mandatory unfold lemmas: *)

Lemma unfold_add_v1_bc :
  forall j : nat,
    add_v1 0 j = j.
Proof.
  unfold_tactic add_v1.
Qed.

Lemma unfold_add_v1_ic :
  forall i' j : nat,
    add_v1 (S i') j = S (add_v1 i' j).
Proof.
  unfold_tactic add_v1.
Qed.

Theorem add_v1_satisfies_the_specification_of_addition :
  specification_of_addition add_v1.
Proof.
Abort.

(* ********** *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | 0 => j
    | S i' => add_v2 i' (S j)
  end.

Compute (unit_tests_for_addition add_v2).
(*
     = true
     : bool
*)

(* The two mandatory unfold lemmas: *)

Lemma unfold_add_v2_bc :
  forall j : nat,
    add_v2 0 j = j.
Proof.
  unfold_tactic add_v2.
Qed.

Lemma unfold_add_v2_ic :
  forall i' j : nat,
    add_v2 (S i') j = add_v2 i' (S j).
Proof.
  unfold_tactic add_v2.
Qed.

(* A useful lemma: *)

Proposition add_v2_ic_right :
  forall i j : nat,
    add_v2 i (S j) = S (add_v2 i j).
Proof.
Abort.

Theorem add_v2_satisfies_the_specification_of_addition :
  specification_of_addition add_v2.
Proof.
Abort.

(* ********** *)

Theorem functional_equality_of_add_v1_and_add_v2 :
  forall i j : nat,
    add_v1 i j = add_v2 i j.
Proof.
Abort.

(* ********** *)

(* end of week_36b_add.v *)
