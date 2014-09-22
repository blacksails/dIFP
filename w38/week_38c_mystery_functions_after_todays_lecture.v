(* week_38c_mystery_functions_after_todays_lecture.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working file as edited during the lecture. *)

(* ********** *)

Require Import Arith Bool.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" := (eqb A B) (at level 70, right associativity).

(* ********** *)

(* Are the following specifications unique?
   What are then the corresponding functions?

   Spend the rest of your dIFP weekly time
   to answer these questions
   for the specifications below.
   (At least 7 specifications would be nice.)
*)

(* ********** *)

Definition specification_of_the_mystery_function_0 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i + f j).

(* ***** *)

Proposition there_is_only_one_mystery_function_0 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_0 f ->
    specification_of_the_mystery_function_0 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_0:
*)
Definition unit_test_for_the_mystery_function_0 (f : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (f 0 =n= 1)
(*
   f 1
   = (* because S (i + j) = 1 if i = 0 and j = 0 *)
   f (S (0 + 0))    
   = (* by definition of mystery_function_0 *)
   f 0 + f 0
   = (* by definition of mystery_function_0 *)
   1 + 1
   =
   2
*)
  &&
  (f 1 =n= 2)
(*
   Similarly,
   f 2
   =
   f (S (0 + 1))
   =
   f 0 + f 1
   =
   1 + 2
   =
   3
*)
  &&
  (f 2 =n= 3)
(*
   We therefore conjecture that the mystery function
   is the successor function,
   i.e., the function that adds 1 to its argument.
*)
  .

Compute unit_test_for_the_mystery_function_0 S.

(* ***** *)

Theorem and_the_mystery_function_0_is_dot_dot_dot :
  specification_of_the_mystery_function_0 S.
Proof.
  unfold specification_of_the_mystery_function_0.
  split.

  reflexivity.

  intros i j.
  ring.
Qed.  

(* ********** *)

Definition specification_of_the_mystery_function_1 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + S j) = f i + S (f j)).

(* ***** *)

Proposition there_is_only_one_mystery_function_1 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_1 f ->
    specification_of_the_mystery_function_1 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_1:
*)
Definition unit_test_for_the_mystery_function_1 (f : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (f 0 =n= 0)
(*
   f 1
   = ...
*)
(* 
  &&
  (f 1 =n= ...)
*)
  .

(*
Compute unit_test_for_the_mystery_function_1 ....
*)

(* ***** *)

(*
Theorem and_the_mystery_function_1_is_dot_dot_dot :
  specification_of_the_mystery_function_1 ....
Proof.
  unfold specification_of_the_mystery_function_1.
  split.

  ...
Qed.  
*)

(* ********** *)

Definition specification_of_the_mystery_function_2 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).

(* ********** *)

Definition specification_of_the_mystery_function_3 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).

(* ********** *)

Definition specification_of_the_mystery_function_4 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + j) = f i + f j).

(* ********** *)

Definition specification_of_the_mystery_function_5 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i : nat,
    f (S i) = S (2 * i + f i)).

(* ********** *)

Definition specification_of_the_mystery_function_6 (f : nat -> nat) :=
  (forall i j : nat,
    f (i + j) = f i + 2 * i * j + f j).

(* ********** *)

Definition specification_of_the_mystery_function_7 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = 2 * f i * f j).

(* ********** *)

Definition specification_of_the_mystery_function_8 (f : nat -> nat) :=
  (f 0 = 2)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i * f j).

(* ********** *)

Definition specification_of_the_mystery_function_9 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (f 1 = 1)
  /\
  (f 2 = 1)
  /\
  (forall p q : nat,
    f (S (p + q)) = f (S p) * f (S q) + f p * f q).

(* ********** *)

Definition specification_of_the_mystery_function_10 (f : nat -> bool) :=
  (f 0 = true)
  /\
  (f 1 = false)
  /\
  (forall i j : nat,
     f (i + j) = eqb (f i) (f j)).

(* ********** *)

(* end of week_38c_mystery_functions_after_todays_lecture.v *)
