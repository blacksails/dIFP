(* week_39a_binary_trees.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool unfold_tactic.

(* ********** *)

Inductive binary_tree_nat : Type :=
  | Leaf : nat -> binary_tree_nat
  | Node : binary_tree_nat -> binary_tree_nat -> binary_tree_nat.

Definition bt_0 :=
  Leaf 42.

Definition bt_1 :=
  Node (Leaf 10)
       (Leaf 20).

Definition bt_2 :=
  Node (Node (Leaf 10)
             (Leaf 20))
       (Leaf 30).

(*
Print bt_2.
bt_2 = Node (Node (Leaf 10) (Leaf 20)) (Leaf 30)
     : binary_tree_nat
*)

(* ********** *)

(* A unit test: *)

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_test_for_number_of_leaves (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 1)
  &&
  (candidate bt_1 =n= 2)
  &&
  (candidate bt_2 =n= 3)
  &&
  (candidate (Node bt_1 bt_2) =n= 5)
  .

Definition specification_of_number_of_leaves (number_of_leaves : binary_tree_nat -> nat) :=
  (forall n : nat,
     number_of_leaves (Leaf n) = 1)
  /\
  (forall t1 t2 : binary_tree_nat,
     number_of_leaves (Node t1 t2) = (number_of_leaves t1) + (number_of_leaves t2)).

Theorem there_is_only_one_number_of_leaves :
  forall f g : binary_tree_nat -> nat,
    specification_of_number_of_leaves f ->
    specification_of_number_of_leaves g ->
    forall t : binary_tree_nat,
      f t = g t.
Proof.
  intros f g.
  unfold specification_of_number_of_leaves.
  intros [Hf_leaf Hf_node] [Hg_leaf Hg_node].
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> Hf_leaf.
  rewrite -> Hg_leaf.
  reflexivity.

  rewrite -> Hf_node.
  rewrite -> Hg_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

Fixpoint number_of_leaves_ds (t : binary_tree_nat) : nat :=
  match t with
    | Leaf n =>
      1
    | Node t1 t2 =>
      (number_of_leaves_ds t1) + (number_of_leaves_ds t2)
  end.

Lemma unfold_number_of_leaves_ds_leaf :
  forall n : nat,
    number_of_leaves_ds (Leaf n) = 1.
Proof.
  unfold_tactic number_of_leaves_ds.
Qed.

Lemma unfold_number_of_leaves_ds_node :
  forall t1 t2 : binary_tree_nat,
    number_of_leaves_ds (Node t1 t2) =
    (number_of_leaves_ds t1) + (number_of_leaves_ds t2).
Proof.
  unfold_tactic number_of_leaves_ds.
Qed.

Definition number_of_leaves_v0 (t : binary_tree_nat) : nat :=
  number_of_leaves_ds t.

Compute unit_test_for_number_of_leaves number_of_leaves_v0.
(*
     = true
     : bool
*)

(* Homework:
   write a version number_of_leaves_v1
   that uses an accumulator.
*)

(* ********** *)

(* Exercise:
   do the same as above for computing the number of nodes
   of a binary tree.
*)

(* ********** *)

(* end of week_39a_binary_trees.v *)