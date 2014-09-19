(* week_37b_lists.v *)
(* dIFP 2014-2015, Q1, Week 37 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* New tactics:
   - assert (to declare a new hypothesis)
   - clear (to garbage collect the hypotheses).
*)

Require Import unfold_tactic.

Require Import Arith Bool List.

(* The goal of this file is to study lists:
   Infix :: is cons, and nil is the empty list.
*)

Compute 3 :: 2 :: 1 :: nil.
(*
     = 3 :: 2 :: 1 :: nil
     : list nat
*)

(* ********** *)

Lemma f_equal_S :
  forall x y : nat,
    x = y -> S x = S y.
Proof.
  intros x y.
  intro H_xy.
  rewrite -> H_xy.
  reflexivity.
Qed.

Lemma unfold_plus_bc :
  forall y : nat,
    0 + y = y.
Proof.
  unfold_tactic plus.
Qed.

Lemma unfold_plus_ic :
  forall x' y : nat,
    (S x') + y = S (x' + y).
Proof.
  unfold_tactic plus.
Qed.

Lemma plus_1_l :
  forall n : nat,
    1 + n = S n.
Proof.
  intro n.
  rewrite -> (unfold_plus_ic 0 n).
  rewrite -> (unfold_plus_bc n).
  reflexivity.
Qed.

Lemma plus_1_r :
  forall n : nat,
    n + 1 = S n.
Proof.
  intro n.
  rewrite -> (plus_comm n 1).
  apply (plus_1_l n).
Qed.

Lemma Sn_1_plus_n :
  forall n : nat,
    S n = 1 + n.
Proof.
  intro n.
  symmetry.
  apply (plus_1_l n).
Qed.

(* ********** *)

(* The length of a list: *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_length_nat (length : list nat -> nat) :=
  (length nil === 0)
  &&
  (length (1 :: nil) === 1)
  &&
  (length (2 :: 1 :: nil) === 2)
  &&
  (length (3 :: 2 :: 1 :: nil) === 3)
  .

Definition unit_tests_for_length_bool (length : list bool -> nat) :=
  (length nil === 0)
  &&
  (length (true :: nil) === 1)
  &&
  (length (true :: true :: nil) === 2)
  &&
  (length (true :: true :: true :: nil) === 3)
  .

Definition specification_of_length (T : Type) (length : list T -> nat) :=
  (length nil = 0)
  /\
  (forall (x : T) (xs' : list T),
     length (x :: xs') = S (length xs')).

Theorem there_is_only_one_length :
  forall (T : Type) (length_1 length_2 : list T -> nat),
    specification_of_length T length_1 ->
    specification_of_length T length_2 ->
    forall xs : list T,
      length_1 xs = length_2 xs.
Proof.
  intros T length_1 length_2.

  unfold specification_of_length.
  intros [Hbc1 Hic1] [Hbc2 Hic2].

  intro xs.
  induction xs as [ | x xs' IHxs'].

  rewrite -> Hbc1.
  rewrite -> Hbc2.
  reflexivity.

  rewrite (Hic1 x xs').
  rewrite (Hic2 x xs').
  rewrite -> IHxs'.
  reflexivity.
Qed.

(* ***** *)

(* A first implementation of length: *)

Fixpoint length_ds (T : Type) (xs : list T) : nat :=
  match xs with
    | nil => 0
    | x :: xs' => S (length_ds T xs')
  end.

Definition length_v1 (T : Type) (xs : list T) : nat :=
  length_ds T xs.

Compute unit_tests_for_length_nat (length_v1 nat).
(*
     = true
     : bool
*)

Compute unit_tests_for_length_bool (length_v1 bool).
(*
     = true
     : bool
*)

(* The canonical unfold lemmas: *)

Lemma unfold_length_ds_base_case :
  forall T : Type,
    length_ds T nil = 0.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_ds.
Qed.

Lemma unfold_length_ds_induction_case :
  forall (T : Type) (x : T) (xs' : list T),
    length_ds T (x :: xs') = S (length_ds T xs').
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_v1.
Qed.

Proposition length_v1_fits_the_specification_of_length :
  forall T : Type,
    specification_of_length T (length_v1 T).
Proof.
  intro T.
  unfold specification_of_length.
  split.

  unfold length_v1.
  apply (unfold_length_ds_base_case T).
  
  unfold length_v1.
  apply (unfold_length_ds_induction_case T).
Qed.

(* ***** *)

(* A second implementation of length: *)

Fixpoint length_acc (T : Type) (xs : list T) (a : nat) : nat :=
  match xs with
    | nil => a
    | x :: xs' => length_acc T xs' (S a)
  end.

Definition length_v2 (T : Type) (xs : list T) : nat :=
  length_acc T xs 0.

Compute unit_tests_for_length_nat (length_v2 nat).
(*
     = true
     : bool
*)

Compute unit_tests_for_length_bool (length_v2 bool).
(*
     = true
     : bool
*)

(* The canonical unfold lemmas: *)

Lemma unfold_length_acc_base_case :
  forall (T : Type) (a : nat),
    length_acc T nil a = a.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_acc.
Qed.

Lemma unfold_length_acc_induction_case :
  forall (T : Type) (x : T) (xs' : list T) (a : nat),
    length_acc T (x :: xs') a = length_acc T xs' (S a).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic length_acc.
Qed.

(* A useful lemma (Eureka): *)

Lemma about_length_acc :
  forall (T : Type) (xs : list T) (a : nat),
    length_acc T xs a = (length_acc T xs 0) + a.
Proof.
  intros T xs.

  induction xs as [| x xs IHxs].

  intro a.
  rewrite -> (unfold_length_acc_base_case T 0).
  rewrite -> (unfold_length_acc_base_case T a).
  rewrite -> (plus_0_l a).

  reflexivity.

  intro a.
  rewrite -> (unfold_length_acc_induction_case T x xs).
  rewrite -> (unfold_length_acc_induction_case).

  rewrite -> (Sn_1_plus_n).
  rewrite -> (IHxs (1 + a)).
  rewrite -> (IHxs 1).
  rewrite -> (plus_assoc (length_acc T xs 0) 1 a).

  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

Proposition length_v2_fits_the_specification_of_length :
  forall T : Type,
    specification_of_length T (length_v2 T).
Proof.
  intros T.
  unfold specification_of_length.

  split.
  unfold length_v2.

  rewrite -> (unfold_length_acc_base_case T 0).
  reflexivity.

  intros x xs.
  unfold length_v2.

  rewrite -> (unfold_length_acc_induction_case T x xs 0).
  rewrite -> (Sn_1_plus_n (length_acc T xs 0)).
  rewrite -> (about_length_acc T xs 1).

  rewrite -> (plus_1_r).
  rewrite -> (plus_1_l (length_acc T xs 0)).

  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ********** *)

Fixpoint equal_list_nat (xs ys : list nat) :=
  match xs with
    | nil =>
      match ys with
        | nil => true
        | y :: ys' => false
      end
    | x :: xs' =>
      match ys with
        | nil => false
        | y :: ys' => (beq_nat x y) && (equal_list_nat xs' ys')
      end
  end.

(* ********** *)

(* Concatenating two lists: *)

Definition unit_tests_for_append_nat (append : list nat -> list nat -> list nat) :=
  (equal_list_nat (append nil
                          nil)
                  nil)
  &&
  (equal_list_nat (append (1 :: nil)
                          nil)
                  (1 :: nil))
  &&
  (equal_list_nat (append nil
                          (1 :: nil))
                  (1 :: nil))
  &&
  (equal_list_nat (append (1 :: 2 :: nil)
                          (3 :: 4 :: 5 :: nil))
                  (1 :: 2 :: 3 :: 4 :: 5 :: nil))
  .

Definition specification_of_append (T : Type) (append : list T -> list T -> list T) :=
  (forall ys : list T,
     append nil ys = ys)
  /\
  (forall (x : T) (xs' ys : list T),
     append (x :: xs') ys = x :: (append xs' ys)).

Theorem there_is_only_one_append :
  forall (T : Type) (append_1 append_2 : list T -> list T -> list T),
    specification_of_append T append_1 ->
    specification_of_append T append_2 ->
    forall xs ys : list T,
      append_1 xs ys = append_2 xs ys.
Proof.
  intros T append_1 append_2.
  unfold specification_of_append.
  intros [Hbc1 Hic1] [Hbc2 Hic2].

  intro xs.
  induction xs as [ | x xs' IHxs'].

  intro ys.
  rewrite -> (Hbc1 ys).
  rewrite -> (Hbc2 ys).
  reflexivity.

  intro ys.
  rewrite (Hic1 x xs').
  rewrite (Hic2 x xs').
  rewrite -> IHxs'.
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

Fixpoint append_ds (T : Type) (xs ys : list T) : list T :=
  match xs with
    | nil => ys
    | x :: xs' => x :: append_ds T xs' ys
  end.

Definition append_v1 (T : Type) (xs ys : list T) : list T :=
  append_ds T xs ys.

Compute unit_tests_for_append_nat (append_v1 nat).

Lemma unfold_append_v1_base_case :
  forall (T : Type) (ys : list T),
    append_ds T nil ys = ys.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic append_ds.
Qed.

Lemma unfold_append_v1_induction_case :
  forall (T : Type) (x : T) (xs' ys : list T),
    append_ds T (x :: xs') ys = x :: append_ds T xs' ys.
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic append_ds.
Qed.

Proposition append_v1_fits_the_specification_of_append :
  forall T : Type,
    specification_of_append T (append_v1 T).
Proof.
  intro T.
  unfold specification_of_append.
  split.

  apply (unfold_append_v1_base_case T).

  apply (unfold_append_v1_induction_case T).
Qed.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* Properties:
     for all ys, append nil ys = ys
     for all xs, append xs nil = xs
     for all xs ys zs,
       append (append xs ys) zs = append xs (append ys zs)
     for all xs ys,
       length (append xs ys) = (length xs) + (length ys)
*)

Definition unit_tests_for_append_nat_properties (append : list nat -> list nat -> list nat) :=
  (equal_list_nat (append nil (0 :: nil))
                  (0 :: nil))
  &&
  (equal_list_nat (append (0 :: nil) nil)
                  (0 :: nil))
  &&
  (equal_list_nat (append (append (0 :: nil) (1 :: nil)) (2 :: nil))
                  (append (0 :: nil) (append (1 :: nil) (2 :: nil))))
  &&
  (length (append (1 :: 2 :: nil) (3 :: 4 :: 5 :: nil))
          === (length (1 :: 2 :: nil)) + (length (3 :: 4 :: 5 :: nil)))
  .

Compute unit_tests_for_append_nat_properties (append_v1 nat).

(* Exercise: write a unit test that validates these properties. *)

Lemma nil_is_neutral_for_append_on_the_left :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall ys : list T,
      append nil ys = ys.
Proof.
  intros T append.
  unfold specification_of_append.
  intros [Hbc Hic].
  intro ys.
  apply (Hbc ys).
Qed.

Lemma nil_is_neutral_for_append_on_the_right :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall xs : list T,
      append xs nil = xs.
Proof.
  intros T append.

  unfold specification_of_append.
  intros [Hbc Hic].

  intro xs.
  induction xs as [ | x xs' IHxs'].

  apply (Hbc nil).

  rewrite -> (Hic x xs' nil).
  rewrite -> IHxs'.
  reflexivity.
Qed.

Lemma append_is_associative :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall xs ys zs: list T,
      append (append xs ys) zs = append xs (append ys zs).
Proof.
  intros T append.

  unfold specification_of_append.
  intros [Hbc Hic].

  intros xs.
  induction xs as [ | x xs' IHxs'].

  intros ys zs.
  rewrite -> (Hbc ys).
  rewrite -> (Hbc (append ys zs)).
  reflexivity.

  intros ys zs.
  rewrite -> (Hic x xs' ys).
  rewrite -> (Hic x (append xs' ys)).
  rewrite -> (Hic x xs' (append ys zs)).
  rewrite -> (IHxs' ys zs).
  reflexivity.
Qed.

(* ********** *)

Proposition append_preserves_length :
  forall (T : Type)
         (length : list T -> nat)
         (append : list T -> list T -> list T),
    specification_of_length T length ->
    specification_of_append T append ->
    forall xs ys : list T,
      length (append xs ys) = (length xs) + (length ys).
Proof.
  intros T length append.

  unfold specification_of_length.
  intros [H_length_bc H_length_ic].

  unfold specification_of_append.
  intros [H_append_bc H_append_ic].

  intro xs.
  induction xs as [ | x xs' IHxs'].

  intro ys.
  rewrite -> (H_append_bc ys).
  rewrite -> H_length_bc.
  rewrite -> plus_0_l.
  reflexivity.

  intro ys.
  rewrite -> (H_append_ic x xs' ys).
  rewrite -> (H_length_ic x (append xs' ys)).
  rewrite -> (IHxs' ys).
  rewrite -> (H_length_ic x xs').
  symmetry.
  apply plus_Sn_m.
Qed.

(* ********** *)

(* Reversing a list: *)

Definition unit_tests_for_reverse_nat (reverse : list nat -> list nat) :=
  (equal_list_nat (reverse nil)
                  nil)
  &&
  (equal_list_nat (reverse (1 :: nil))
                  (1 :: nil))
  &&
  (equal_list_nat (reverse (1 :: 2 :: nil))
                  (2 :: 1 :: nil))
  &&
  (equal_list_nat (reverse (1 :: 2 :: 3 :: nil))
                  (3 :: 2 :: 1 :: nil))
  .

Definition specification_of_reverse (T : Type) (reverse : list T -> list T) :=
  forall (append : list T -> list T -> list T),
    specification_of_append T append ->
    (reverse nil = nil)
    /\
    (forall (x : T) (xs' : list T),
       reverse (x :: xs') = append (reverse xs') (x :: nil)).

Theorem there_is_only_one_reverse :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall reverse_1 reverse_2 : list T -> list T,
      specification_of_reverse T reverse_1 ->
      specification_of_reverse T reverse_2 ->
      forall xs : list T,
        reverse_1 xs = reverse_2 xs.
Proof.
  intros T append S_append.
  intros reverse_1 reverse_2.
  intros S_rev1 S_rev2.

  unfold specification_of_reverse in S_rev1.
  unfold specification_of_reverse in S_rev2.
  destruct (S_rev1 append S_append) as [H_rev1_bc H_rev1_ic].
  destruct (S_rev2 append S_append) as [H_rev2_bc H_rev2_ic].
  clear S_rev1 S_rev2.

  unfold specification_of_append in S_append.
  destruct S_append as [H_append_bc H_append_ic].

  intro xs.
  induction xs as [| x' xs' IHxs'].

  rewrite -> H_rev1_bc.
  rewrite -> H_rev2_bc.
  reflexivity.

  rewrite -> (H_rev1_ic x' xs').
  rewrite -> (H_rev2_ic x' xs').
  rewrite -> (IHxs').

  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* An implementation of reverse: *)

Fixpoint reverse_ds (T : Type) (xs : list T) : list T :=
  match xs with
    | nil => nil
    | x :: xs' => append_v1 T (reverse_ds T xs') (x :: nil)
  end.

Definition reverse_v1 (T : Type) (xs : list T) : list T :=
  reverse_ds T xs.

Compute unit_tests_for_reverse_nat (reverse_v1 nat).

Lemma unfold_reverse_ds_base_case :
  forall (T : Type),
    reverse_ds T nil = nil.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic reverse_ds.
Qed.

Lemma unfold_reverse_ds_induction_case :
  forall (T : Type)
         (x : T)
         (xs' : list T),
    reverse_ds T (x :: xs') =
    append_v1 T (reverse_ds T xs') (x :: nil).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic reverse_ds.
Qed.

Proposition reverse_v1_fits_the_specification_of_reverse :
  forall T : Type,
    specification_of_reverse T (reverse_v1 T).
Proof.
  intro T.
  unfold specification_of_reverse.

  intros append S_append.

  split.

  apply unfold_reverse_ds_base_case.

  intros x xs'.
  unfold reverse_v1.
  rewrite -> (unfold_reverse_ds_induction_case T x xs').

  rewrite -> (there_is_only_one_append T append (append_v1 T) S_append
                                       (append_v1_fits_the_specification_of_append T)
                                       (reverse_ds T xs') (x :: nil)).
  reflexivity.
Qed.

(* Replace "Abort." with a proof. *)

(* ***** *)

(* A second implementation of reverse, with an accumulator : *)

Fixpoint reverse_acc (T : Type) (xs a : list T) : list T :=
  match xs with
    | nil => a
    | x :: xs' => reverse_acc T xs' (x :: a)
  end.

Definition reverse_v2 (T : Type) (xs : list T) :=
  reverse_acc T xs nil.

Compute unit_tests_for_reverse_nat (reverse_v2 nat).

(* A useful lemma (Eureka): *)

Lemma unfold_reverse_acc_base_case :
  forall (T : Type) (a : list T),
    reverse_acc T nil a = a.
Proof.
  unfold_tactic reverse_acc.
Qed.

Lemma unfold_reverse_acc_induction_case :
  forall (T : Type) (x : T) (xs' a : list T),
    reverse_acc T (x :: xs') a = reverse_acc T xs' (x :: a).
Proof.
  unfold_tactic reverse_acc.
Qed.

Lemma about_reverse_acc :
  forall (T : Type)
         (append : list T -> list T -> list T),
    specification_of_append T append ->
    forall xs a : list T,
      reverse_acc T xs a = append (reverse_acc T xs nil) a.
Proof.
  intros T append S_append.
  intros xs.

  assert (S_append_ := S_append).
  destruct S_append as [H_append_bc H_append_ic].

  induction xs as [|x' xs' IHxs'].

  intro a.

  rewrite -> (unfold_reverse_acc_base_case T a).
  rewrite -> (unfold_reverse_acc_base_case T nil).
  rewrite -> (H_append_bc a).
  reflexivity.

  intro a.
  rewrite -> (unfold_reverse_acc_induction_case T x' xs' a).
  rewrite -> (unfold_reverse_acc_induction_case T x' xs' nil).
  rewrite -> (IHxs' (x' :: a)).
  
  rewrite -> (IHxs' (x' :: nil)).
  rewrite -> (append_is_associative T append S_append_ (reverse_acc T xs' nil) (x' :: nil) a).
  rewrite -> (H_append_ic x' nil a).
  rewrite -> (H_append_bc a).
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

Proposition reverse_v2_fits_the_specification_of_reverse :
  forall T : Type,
    specification_of_reverse T (reverse_v2 T).
Proof.
  intro T.
  unfold specification_of_reverse.

  intro append.
  intro S_append.

  split.

  apply (unfold_reverse_acc_base_case T nil).

  intros x xs.
  unfold reverse_v2.
  rewrite -> (unfold_reverse_acc_induction_case T x xs nil).

  rewrite -> (about_reverse_acc T append S_append xs (x :: nil)).

  reflexivity.
Qed.

(* Replace "Abort." with a proof. *)

(* ********** *)

(* Properties:
     for all xs,
       length xs = length (reverse xs)
     forall xs ys,
       reverse (append xs ys) = append (reverse ys) (reverse xs)
w     forall xs,
       reverse (reverse xs) = xs
*)

Definition unit_tests_for_reverse_nat_properties
           (reverse : list nat -> list nat)
           (append : list nat -> list nat -> list nat) :=
  (length (0 :: 1 :: nil) === length (reverse (0 :: 1 :: nil)))
  &&
  (equal_list_nat (reverse (append (0 :: 1 :: nil) (2 :: 3 :: nil)))
                  (append (reverse (2 :: 3 :: nil)) (reverse (0 :: 1 :: nil))))
  &&
  (equal_list_nat (reverse (reverse (0 :: 1 :: nil))) (0 :: 1 :: nil))
  .

Compute unit_tests_for_reverse_nat_properties (reverse_v2 nat) (append_v1 nat).

(* Exercise: write a unit test that validates these properties. *)

Proposition reverse_preserves_length :
  forall (T : Type)
         (length : list T -> nat)
         (append : list T -> list T -> list T)
         (reverse : list T -> list T),
    specification_of_length T length ->
    specification_of_append T append ->
    specification_of_reverse T reverse ->
    forall xs : list T,
      length xs = length (reverse xs).
Proof.
  intro T.
  intros length append reverse.
  intros S_length S_append S_reverse.

  destruct (S_reverse append S_append) as [H_reverse_bc H_reverse_ic].
  assert (S_append_ := S_append).
  assert (S_length_ := S_length).
  destruct S_length as [H_length_bc H_length_ic].
  destruct S_append as [H_append_bc H_append_ic].

  intro xs.
  induction xs as [| x xs IHxs].

  rewrite -> H_length_bc.
  rewrite -> H_reverse_bc.
  rewrite -> H_length_bc.
  reflexivity.

  rewrite -> H_length_ic.
  rewrite -> H_reverse_ic.
  rewrite -> (append_preserves_length T length append S_length_ S_append_ (reverse xs) (x :: nil)).
  rewrite -> (H_length_ic x nil).
  rewrite -> H_length_bc.
  rewrite -> (plus_1_r (length (reverse xs))).
  rewrite <- IHxs.
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

Proposition reverse_preserves_append_sort_of :
  forall (T : Type)
         (append : list T -> list T -> list T)
         (reverse : list T -> list T),
    specification_of_append T append ->
    specification_of_reverse T reverse ->
    forall xs ys : list T,
      reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof.
  intros T append reverse.
  intros S_append S_reverse.
  intro xs.

  assert (S_append_ := S_append).
  destruct S_append as [H_append_bc H_append_ic].
  destruct (S_reverse append S_append_) as [H_reverse_bc H_reverse_ic].

  induction xs as [| x xs IHxs].

  intro ys.
  rewrite -> (H_append_bc ys).
  rewrite -> H_reverse_bc.
  rewrite -> (nil_is_neutral_for_append_on_the_right T append S_append_ (reverse ys)).
  reflexivity.

  intro ys.
  rewrite -> (H_append_ic x xs ys).
  rewrite -> (H_reverse_ic x (append xs ys)).
  rewrite -> (IHxs ys).
  rewrite -> (append_is_associative T append S_append_ (reverse ys) (reverse xs) (x :: nil)).
  rewrite -> (H_reverse_ic x xs).
  reflexivity.
Qed.

(* Replace "Abort." with a proof. *)

Proposition reverse_is_involutive :
  forall (T : Type)
         (append : list T -> list T -> list T)
         (reverse : list T -> list T),
    specification_of_append T append ->
    specification_of_reverse T reverse ->
    forall xs : list T,
      reverse (reverse xs) = xs.
Proof.
  intros T append reverse.
  intros S_append S_reverse.

  assert (S_append_ := S_append).
  destruct (S_reverse append S_append) as [H_reverse_bc H_reverse_ic].
  destruct S_append as [H_append_bc H_append_ic].

  intro xs.
  induction xs as [| x xs IHxs].

  rewrite -> H_reverse_bc.
  rewrite -> H_reverse_bc.
  reflexivity.

  rewrite -> (H_reverse_ic x xs).
  rewrite -> (reverse_preserves_append_sort_of T append reverse S_append_ S_reverse (reverse xs) (x :: nil)).
  rewrite -> (H_reverse_ic x nil).
  rewrite -> H_reverse_bc.
  rewrite -> (H_append_bc (x :: nil)).
  rewrite -> (IHxs).
  rewrite -> (H_append_ic x nil xs).
  rewrite -> (H_append_bc xs).
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* Mapping a function over the elements of a list: *)

Definition unit_tests_for_map_nat (map : (nat -> nat) -> list nat -> list nat) :=
  (equal_list_nat (map (fun n => n) 
                       nil)
                  nil)
  &&
  (equal_list_nat (map (fun n => n)
                       (1 :: nil))
                  (1 :: nil))
  &&
  (equal_list_nat (map (fun n => n)
                       (1 :: 2 :: 3 :: nil))
                  (1 :: 2 :: 3 :: nil))
  &&
  (equal_list_nat (map (fun n => S n)
                       nil)
                  nil)
  &&
  (equal_list_nat (map (fun n => S n)
                       (1 :: nil))
                  (2 :: nil))
  &&
  (equal_list_nat (map (fun n => S n)
                       (1 :: 2 :: 3 :: nil))
                  (2 :: 3 :: 4 :: nil))
  &&
  (equal_list_nat (map (fun n => n * 2)
                       (1 :: 2 :: 3 :: nil))
                  (2 :: 4 :: 6 :: nil))
  &&
  (equal_list_nat (map (fun n => 0)
                       (1 :: 2 :: 3 :: nil))
                  (0 :: 0 :: 0 :: nil))
  .

(* Exercise: add more tests. *)

Definition specification_of_map (T1 T2 : Type) (map : (T1 -> T2) -> list T1 -> list T2) :=
  (forall f : T1 -> T2,
     map f nil = nil)
  /\
  (forall (f : T1 -> T2) (x : T1) (xs' : list T1),
     map f (x :: xs') = (f x) :: (map f xs')).

Theorem there_is_only_one_map :
  forall (T1 T2 : Type)
         (map_1 map_2 : (T1 -> T2) -> list T1 -> list T2),
    specification_of_map T1 T2 map_1 ->
    specification_of_map T1 T2 map_2 ->
    forall (f : T1 -> T2)
           (xs : list T1),
      map_1 f xs = map_2 f xs.
Proof.
  intros T1 T2.
  intros map_1 map_2.
  intros S_map1 S_map2.
  intros f xs.

  destruct S_map1 as [H_map1_bc H_map1_ic].
  destruct S_map2 as [H_map2_bc H_map2_ic].

  induction xs as [| x' xs' IHxs'].

  rewrite -> (H_map1_bc f).
  rewrite -> (H_map2_bc f).
  reflexivity.
  
  rewrite -> (H_map1_ic f x' xs').
  rewrite -> (H_map2_ic f x' xs').

  rewrite -> IHxs'.
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* An implementation of map: *)

Fixpoint map_ds (T1 T2 : Type) (f : T1 -> T2) (xs : list T1) : list T2 :=
  match xs with
    | nil => nil
    | x :: xs' => (f x) :: (map_ds T1 T2 f xs')
  end.

Definition map_v1 (T1 T2 : Type) (f : T1 -> T2) (xs : list T1) : list T2 :=
  map_ds T1 T2 f xs.

Compute unit_tests_for_map_nat (map_v1 nat nat).

Lemma unfold_map_ds_base_case :
  forall (T1 T2 : Type)
         (f : T1 -> T2),
    map_ds T1 T2 f nil = nil.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic map_ds.
Qed.

Lemma unfold_map_ds_induction_case :
  forall (T1 T2 : Type)
         (f : T1 -> T2)
         (x : T1)
         (xs' : list T1),
    map_ds T1 T2 f (x :: xs') =
    (f x) :: (map_ds T1 T2 f xs').
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic map_ds.
Qed.

Proposition map_v1_fits_the_specification_of_map :
  forall T1 T2 : Type,
    specification_of_map T1 T2 (map_v1 T1 T2).
Proof.
  intros T1 T2.

  unfold specification_of_map.
  split.

  apply (unfold_map_ds_base_case T1 T2).
  apply (unfold_map_ds_induction_case T1 T2).
Qed.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* Properties:
     for all f1 f2 xs,
       map f2 (map f1 xs) = map (fun x => f2 (f1 x)) xs
     for all f xs ys,
        map f (append xs ys) = append (map f xs) (map f ys)
     for all f xs,
       map f (reverse xs) = reverse (map f xs)
*)

Definition unit_tests_for_map_nat_properties
           (map : (nat -> nat) -> list nat -> list nat)
           (append : list nat -> list nat -> list nat)
           (reverse : list nat -> list nat) :=
  (equal_list_nat (map (fun a => a + 1) (map (fun b => b * 2) (0 :: 1 :: 2 :: 3 :: nil)))
                  (map (fun x => (fun a => a + 1) ((fun b => b * 2) x)) (0 :: 1 :: 2 :: 3 :: nil)))
    &&
  (equal_list_nat (map (fun a => a * a) (append (0 :: 1 :: nil) (2 :: 3 :: nil)))
                  (append (map (fun a => a * a) (0 :: 1 :: nil)) (map (fun a => a * a) (2 :: 3 :: nil))))
  &&
  (equal_list_nat (map (fun a => a * 3) (reverse (0 :: 1 :: nil)))
                  (reverse (map (fun a => a * 3) (0 :: 1 :: nil))))
  .

Compute unit_tests_for_map_nat_properties (map_v1 nat nat) (append_v1 nat) (reverse_v1 nat).

(* Exercise: write a unit test that validates these properties. *)

Proposition listlessness_of_map :
  forall (T1 T2 T3 : Type)
         (map12 : (T1 -> T2) -> list T1 -> list T2)
         (map23 : (T2 -> T3) -> list T2 -> list T3)
         (map13 : (T1 -> T3) -> list T1 -> list T3),
    specification_of_map T1 T2 map12 ->
    specification_of_map T2 T3 map23 ->
    specification_of_map T1 T3 map13 ->
    forall (f1 : T1 -> T2)
           (f2 : T2 -> T3)
           (xs : list T1),
      map23 f2 (map12 f1 xs) = map13 (fun x => f2 (f1 x)) xs.
Proof.
  intros T1 T2 T3.
  intros map1 map2 map3.
  intros S_map1 S_map2 S_map3.
  intros f1 f2 xs.

  destruct S_map1 as [H_map1_bc H_map1_ic].
  destruct S_map2 as [H_map2_bc H_map2_ic].
  destruct S_map3 as [H_map3_bc H_map3_ic].

  induction xs as [| x' xs' IHxs'].
  
  rewrite -> (H_map1_bc f1).
  rewrite -> (H_map2_bc f2).
  rewrite -> (H_map3_bc (fun x : T1 => f2 (f1 x))).
  reflexivity.

  rewrite -> (H_map1_ic f1 x' xs').
  rewrite -> (H_map2_ic f2 (f1 x') (map1 f1 xs')).
  rewrite -> IHxs'.
  rewrite -> (H_map3_ic (fun x : T1 => f2 (f1 x)) x' xs').
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

Proposition append_preserves_map :
  forall (T1 T2 : Type)
         (map : (T1 -> T2) -> list T1 -> list T2)
         (append_1 : list T1 -> list T1 -> list T1)
         (append_2 : list T2 -> list T2 -> list T2),
    specification_of_map T1 T2 map ->
    specification_of_append T1 append_1 ->
    specification_of_append T2 append_2 ->
    forall (f : T1 -> T2) (xs ys : list T1),
       map f (append_1 xs ys) = append_2 (map f xs) (map f ys).
Proof.
  intros T1 T2 map append_1 append_2.
  intros S_map S_append_1 S_append_2.
  intros f xs.

  destruct S_map as [H_map_bc H_map_ic].
  destruct S_append_1 as [H_append_1_bc H_append_1_ic].
  destruct S_append_2 as [H_append_2_bc H_append_2_ic].

  induction xs as [| x' xs' IHxs'].

  intro ys.  
  rewrite -> (H_append_1_bc ys).
  rewrite -> (H_map_bc f).
  rewrite -> (H_append_2_bc (map f ys)).
  reflexivity.

  intro ys.
  rewrite -> (H_append_1_ic x' xs' ys).
  rewrite -> (H_map_ic f x' (append_1 xs' ys)).
  rewrite -> (IHxs' ys).
  
  rewrite -> (H_map_ic f x' xs').
  rewrite -> (H_append_2_ic (f x') (map f xs') (map f ys)).
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

Proposition reverse_preserves_map_sort_of :
  forall (T1 T2 : Type)
         (append_1 : list T1 -> list T1 -> list T1)
         (append_2 : list T2 -> list T2 -> list T2)
         (reverse_1 : list T1 -> list T1)
         (reverse_2 : list T2 -> list T2)
         (map : (T1 -> T2) -> list T1 -> list T2),
    specification_of_append T1 append_1 ->
    specification_of_append T2 append_2 ->
    specification_of_reverse T1 reverse_1 ->
    specification_of_reverse T2 reverse_2 ->
    specification_of_map T1 T2 map ->
    forall (f : T1 -> T2)
           (xs : list T1),
      map f (reverse_1 xs) = reverse_2 (map f xs).
Proof.
  intros T1 T2 append1 append2 reverse1 reverse2 map.
  intros S_append1 S_append2 S_reverse1 S_reverse2 S_map.
  intros f xs.

  assert (S_map_ := S_map).
  assert (S_append1_ := S_append1).
  assert (S_append2_ := S_append2).

  destruct (S_reverse1 append1 S_append1) as [H_reverse1_bc H_reverse1_ic].
  destruct (S_reverse2 append2 S_append2) as [H_reverse2_bc H_reverse2_ic].
  clear S_reverse1 S_reverse2.
  destruct S_append1 as [H_append1_bc H_append1_ic].
  destruct S_append2 as [H_append2_bc H_append2_ic].
  destruct S_map as [H_map_bc H_map_ic].
  
  induction xs as [| x' xs' IHxs'].

  rewrite -> H_reverse1_bc.
  rewrite -> H_map_bc.
  rewrite -> H_reverse2_bc.  
  reflexivity.

  rewrite -> (H_reverse1_ic x' xs').
  rewrite -> (append_preserves_map T1 T2 map append1 append2 S_map_ S_append1_ S_append2_
                                   f (reverse1 xs') (x' :: nil)).
  rewrite -> (H_map_ic f x' nil).
  rewrite -> (H_map_bc f).
  rewrite -> IHxs'.

  rewrite -> (H_map_ic f x' xs').
  rewrite -> (H_reverse2_ic (f x') (map f xs')).
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* end of week_37b_lists.v *)
