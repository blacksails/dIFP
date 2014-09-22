(* one_more_mystery_function.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* Is the following specification unique?
   What is then the corresponding function?

   Here is one more mystery function to add
   to the pool.

   You should still aim to answer the two questions above
   for at least 7 specifications in the pool.
*)

(* ********** *)

Require Import Arith.

Lemma plus_1_l :
  forall x : nat,
    1 + x = S x.
Proof.
  intro x.
  rewrite -> plus_Sn_m.
  rewrite -> plus_0_l.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_42 (f : nat -> nat) :=
  (f 1 = 42)
  /\
  (forall i j : nat,
    f (i + j) = f i + f j).

(* ********** *)

(* end of one_more_mystery_function.v *)
