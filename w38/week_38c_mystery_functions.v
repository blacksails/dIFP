(* week_38c_mystery_functions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* Are the following specifications unique?
   What are then the corresponding functions?

   Spend the rest of your dIFP weekly time
   to answer these questions
   for the specifications below.
   (* At least 7 specifications would be nice.)
*)

(* ********** *)

Definition specification_of_the_mystery_function_0 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i + f j).

Proposition there_is_only_one_mystery_function_0 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_0 f ->
    specification_of_the_mystery_function_0 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(*
Theorem and_the_mystery_function_0_is_dot_dot_dot :
  specification_of_the_mystery_function_0 ???.
Proof.
  unfold specification_of_the_mystery_function_0.
  split.
Abort.
(* Replace "Abort." with a proof. *)
*)

(* ********** *)

Definition specification_of_the_mystery_function_1 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + S j) = f i + S (f j)).

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
    f (i + j) = f i + 2 * i * j * f j).

(* ********** *)

Definition specification_of_the_mystery_function_7 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = 2 * f i * f j).

(* ********** *)

Definition specification_of_the_mystery_function_power_8 (f : nat -> nat) :=
  (f 0 = 2)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i * f j).

(* ********** *)

Definition mystery_function_9 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (f 1 = 1)
  /\
  (f 2 = 1)
  /\
  (forall p q : nat,
    f (S (p + q)) = f (S p) * f (S q) + f p * f q).

(* ********** *)

Require Import Bool.

Definition specification_of_the_mystery_function_power_10 (f : nat -> bool) :=
  (f 0 = true)
  /\
  (f 1 = false)
  /\
  (forall i j : nat,
     f (i + j) = eqb (f i) (f j)).

(* ********** *)

(* end of week_38c_mystery_functions.v *)
