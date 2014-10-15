(* week_40c_flatten.v *)
(* dIFP 2014-2015, Q1, Week 40 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool unfold_tactic.

(* ********** *)

(* Data type of binary trees of natural numbers: *)

Inductive binary_tree_nat : Type :=
  | Leaf : nat -> binary_tree_nat
  | Node : binary_tree_nat -> binary_tree_nat -> binary_tree_nat.

(* There is one base case: leaves.
   There is one induction case, with two subtrees.
*)

(* ********** *)

(* Sample of binary trees of natural numbers: *)

Definition bt_0 :=
  Leaf 42.

Definition bt_1 :=
  Node (Leaf 10)
       (Leaf 20).

Definition bt_2 :=
  Node (Node (Leaf 10)
             (Leaf 20))
       (Leaf 30).

(* ********** *)
(*
Definition unit_test_for_flatten (candidate : binary_tree_nat -> nat) :=
  (candidate bt_0 =n= 1)
  &&
  (candidate bt_1 =n= 2)
  &&
  (candidate bt_2 =n= 3)
  &&
  (candidate (Node bt_1 bt_2) =n= 5)
  .
*)
(* ********** *)

Definition specification_of_flatten (flatten : binary_tree_nat -> list nat) :=
  (forall n : nat,
     flatten (Leaf n) = n :: nil)
  /\
  (forall t1 t2 : binary_tree_nat,
     flatten (Node t1 t2) = (flatten t1) ++ (flatten t2)).

Theorem there_is_only_one_flatten :
  forall flatten1 flatten2 : binary_tree_nat -> list nat,
    specification_of_flatten flatten1 ->
    specification_of_flatten flatten2 ->
    forall t : binary_tree_nat,
      flatten1 t = flatten2 t.
Proof.
  intros flatten1 flatten2.
  unfold specification_of_flatten.
  intros [H1_leaf H1_node] [H2_leaf H2_node].
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].

  rewrite -> H2_leaf.
  apply H1_leaf.

  rewrite -> H1_node.
  rewrite -> H2_node.
  rewrite -> IHt1.
  rewrite -> IHt2.
  reflexivity.
Qed.

(* ********** *)

(* Version with append: *)

Fixpoint flatten_ds (t : binary_tree_nat) : list nat :=
  match t with
    | Leaf n => n :: nil
    | Node t1 t2 => (flatten_ds t1) ++ (flatten_ds t2)
  end.

Definition flatten_v0 (t : binary_tree_nat) : list nat :=
  flatten_ds t.

(* ********** *)

(* Version with an accumulator: *)

Fixpoint flatten_acc (t : binary_tree_nat) (a : list nat) : list nat :=
  match t with
    | Leaf n => n :: a
    | Node t1 t2 => flatten_acc t1 (flatten_acc t2 a)
  end.

Definition flatten_v1 (t : binary_tree_nat) : list nat :=
  flatten_acc t nil.

(* ********** *)

Fixpoint swap_ds (t : binary_tree_nat) : binary_tree_nat :=
  match t with
    | Leaf n => Leaf in
    | Node t1 t2 => Node (swap_ds t2) (swap_ds t1)
  end.

Definition swap_v0 (t : binary_tree_nat) : binary_tree_nat :=
  swap_ds t.

(* Prove that composing swap_v0 with itself yields the identity function. *)

(* ********** *)

(* What is the result of applying flatten_v0
   to the result of applying swap_v0 to a tree?
*)

(* ********** *)

(* end of week_40c_flatten.v *)
