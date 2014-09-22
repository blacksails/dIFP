(* more_mystery_functions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* Are the following specifications unique?
   What are then the corresponding functions?

   Here are two more mystery functions to add
   to the pool.

   You should still aim to answer the two questions above
   for at least 7 specifications in the pool.
*)

(* ********** *)

Definition specification_of_the_mystery_function_11 (f : nat -> nat * nat) :=
  (f 0 = (1, 0))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (x + y, x)).

(* ********** *)

Definition specification_of_the_mystery_function_12 (f : nat -> nat * nat) :=
  (f 0 = (0, 1))
  /\
  (forall n' : nat,
    f (S n') = let (x, y) := f n'
               in (S x, y * S x)).

(* ********** *)

(* end of more_mystery_functions.v *)
