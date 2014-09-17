(* week_37a_sum.v *)
(* dIFP 2014-2015, Q1, Week 37 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* The goal of this file is to study the sum function:
     sum f n = f 0 + f 1 + ... + f n
*)

(* ********** *)

Require Import Arith Bool.

Require Import unfold_tactic.

(* ********** *)

(* The canonical unfold lemmas
   associated to plus and mult,
   which are predefined:
*)

Lemma unfold_plus_bc :
  forall y : nat,
    0 + y = y.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic plus.
Qed.

Lemma unfold_plus_ic :
  forall x' y : nat,
    (S x') + y = S (x' + y).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic plus.
Qed.

Lemma unfold_mult_bc :
  forall y : nat,
    0 * y = 0.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic mult.
Qed.

Lemma unfold_mult_ic :
  forall x' y : nat,
    (S x') * y = y + (x' * y).
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic mult.
Qed.

(* ********** *)

Notation "A === B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_tests_for_sum (sum : (nat -> nat) -> nat -> nat) :=
  (sum (fun n => 0) 0 === 0)
  &&
  (sum (fun n => 0) 1 === 0 + 0)
  &&
  (sum (fun n => 0) 2 === 0 + 0 + 0)
  &&
  (sum (fun n => 1) 0 === 1)
  &&
  (sum (fun n => 1) 1 === 1 + 1)
  &&
  (sum (fun n => 1) 2 === 1 + 1 + 1)
  &&
  (sum (fun n => n) 0 === 0)
  &&
  (sum (fun n => n) 1 === 0 + 1)
  &&
  (sum (fun n => n) 2 === 0 + 1 + 2)
  &&
  (sum (fun n => n * n) 0 === 0 * 0)
  &&
  (sum (fun n => n * n) 1 === 0 * 0 + 1 * 1)
  &&
  (sum (fun n => n * n) 2 === 0 * 0 + 1 * 1 + 2 * 2)
  &&
  (sum (fun n => n * n) 3 === 0 * 0 + 1 * 1 + 2 * 2 + 3 * 3)
  &&
  (sum S 0 === 1)
  &&
  (sum S 1 === 1 + 2)
  &&
  (sum S 2 === 1 + 2 + 3)
  .

(* Exercise: add some more tests to this unit test. *)

(* ********** *)

Definition specification_of_sum (sum : (nat -> nat) -> nat -> nat) :=
  forall f : nat -> nat,
    sum f 0 = f 0
    /\
    forall n' : nat,
      sum f (S n') = sum f n' + f (S n').

(* ********** *)

Theorem there_is_only_one_sum :
  forall sum1 sum2 : (nat -> nat) -> nat -> nat,
    specification_of_sum sum1 ->
    specification_of_sum sum2 ->
    forall (f : nat -> nat)
           (n : nat),
      sum1 f n = sum2 f n.
Proof.
  intros sum1 sum2.
  intros S_sum1 S_sum2.
  intros f n.
  induction n as [ | n' IHn' ].
    unfold specification_of_sum in S_sum1.
    unfold specification_of_sum in S_sum2.
    destruct (S_sum1 f) as [ H_sum1_bc H_sum1_ic].
    destruct (S_sum2 f) as [ H_sum2_bc H_sum2_ic].
    clear S_sum1.
    clear S_sum2.
    rewrite -> H_sum2_bc.
    apply H_sum1_bc.

  unfold specification_of_sum in S_sum1.
  unfold specification_of_sum in S_sum2.
  destruct (S_sum1 f) as [ H_sum1_bc H_sum1_ic].
  destruct (S_sum2 f) as [ H_sum2_bc H_sum2_ic].
  clear S_sum1.
  clear S_sum2.
  rewrite -> (H_sum1_ic n').
  rewrite -> (H_sum2_ic n').
  rewrite -> IHn'.
  reflexivity.
Qed.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* Misc. instances of the sum function: *)

Lemma about_sum_0 :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall n : nat,
      sum (fun i => 0) n = 0.
Proof.
  intros sum S_sum n.
  induction n as [ | n' IHn' ].
    unfold specification_of_sum in S_sum.
    destruct (S_sum (fun _ : nat => 0)) as [ H_sum_bc H_sum_ic ].
    clear S_sum.
    apply H_sum_bc.
  unfold specification_of_sum in S_sum.
  destruct (S_sum (fun _ : nat => 0)) as [ H_sum_bc H_sum_ic ].
  clear S_sum.
  rewrite -> (H_sum_ic n').
  rewrite -> (plus_0_r (sum (fun _ : nat => 0) n')).
  apply IHn'.
Qed.

(* Replace "Abort." with a proof. *)

(* ***** *)

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

Lemma about_sum_1 :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall n : nat,
      sum (fun i => 1) n = S n.
Proof.
  intros sum S_sum n.
  induction n as [ | n' IHn'].
    unfold specification_of_sum in S_sum.
    destruct (S_sum (fun _ : nat => 1)) as [H_sum_bc H_sum_ic].
    clear S_sum.
    apply H_sum_bc.
  unfold specification_of_sum in S_sum.
  destruct (S_sum (fun _ : nat => 1)) as [_ H_sum_ic].
  clear S_sum.
  rewrite -> (H_sum_ic n').
  rewrite -> IHn'.
  rewrite -> (plus_Sn_m n' 1).
  rewrite -> (plus_1_r n').
  reflexivity.
Qed.

(* Replace "Abort." with a proof. *)

(* ***** *)

Lemma about_sum_identity :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall n : nat,
      2 * sum (fun i => i) n = n * S n.
Proof.
  intros sum S_sum n.
  induction n as [ | n' IHn'].
    unfold specification_of_sum in S_sum.
    destruct (S_sum (fun i : nat => i)) as [H_sum_bc _].
    clear S_sum.
    rewrite -> H_sum_bc.
    rewrite -> (mult_0_r 2).
    rewrite -> (mult_0_l 1).
    reflexivity.
  unfold specification_of_sum in S_sum.
  destruct (S_sum (fun i : nat => i)) as [_ H_sum_ic].
  clear S_sum.
  rewrite -> (H_sum_ic n').
  Check mult_plus_distr_l.
  rewrite -> (mult_plus_distr_l 2 (sum (fun i : nat => i) n') (S n')).
  rewrite -> IHn'.
  Check mult_plus_distr_r.
  rewrite <- (mult_plus_distr_r n' 2 (S n')).
  Check plus_comm.
  rewrite -> (plus_comm n' 2).
  rewrite -> (unfold_plus_ic 1 n').
  rewrite -> (unfold_plus_ic 0 n').
  rewrite -> (plus_0_l n').
  Check mult_comm.
  rewrite -> (mult_comm (S (S n')) (S n')).
  reflexivity.
Qed.

(* ***** *)

Lemma about_sum_even_numbers :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall n : nat,
      sum (fun i => 2 * i) n = n * S n.
Proof.
  intros sum S_sum n.
  induction n as [ | n' IHn'].
    unfold specification_of_sum in S_sum.
    destruct (S_sum (fun i => 2 * i)) as [H_sum_bc _].
    rewrite -> H_sum_bc.
    rewrite -> (mult_0_r 2).
    rewrite -> (mult_0_l 1).
    reflexivity.
  unfold specification_of_sum in S_sum.
  destruct (S_sum (fun i => 2 * i)) as [_ H_sum_ic].
  clear S_sum.
  rewrite -> (H_sum_ic n').
  rewrite -> IHn'.
  Check mult_plus_distr_r.
  rewrite <- (mult_plus_distr_r n' 2 (S n')).
  rewrite -> (plus_comm n' 2).
  rewrite -> (unfold_plus_ic 1 n').
  rewrite -> (unfold_plus_ic 0 n').
  rewrite -> (unfold_plus_bc n').
  rewrite -> (mult_comm (S (S n')) (S n')).
  reflexivity.
Qed.

(* ***** *)

Lemma a_humble_little_lemma :
  forall a b c : nat,
    a + b + b + c = a + 2 * b + c.
Proof.
  intros a b c.
  rewrite -> (unfold_mult_ic 1 b).
  rewrite -> (unfold_mult_ic 0 b).
  rewrite -> (unfold_mult_bc b).
  rewrite -> plus_0_r.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Lemma binomial_2 :
  forall x y : nat,
    (x + y) * (x + y) = x * x + 2 * x * y + y * y.
Proof.
  intros x y.
  rewrite -> (mult_plus_distr_r x y (x + y)).
  rewrite -> (mult_plus_distr_l x x y).
  rewrite -> (mult_plus_distr_l y x y).
  rewrite -> plus_assoc.
  rewrite <- (mult_assoc 2 x y).
  rewrite (unfold_mult_ic 1 (x * y)).
  rewrite (unfold_mult_ic 0 (x * y)).
  rewrite (unfold_mult_bc (x * y)).
  rewrite -> (plus_0_r (x * y)).
  rewrite -> plus_assoc.
  rewrite -> (mult_comm y x).
  reflexivity.

  Restart.

  intros x y.
  rewrite -> mult_plus_distr_r.
  rewrite -> mult_plus_distr_l.
  rewrite -> mult_plus_distr_l.
  rewrite -> plus_assoc.
  rewrite -> unfold_mult_ic.
  rewrite -> unfold_mult_ic.
  rewrite -> unfold_mult_bc.
  rewrite -> plus_assoc.
  rewrite -> plus_0_r.
  rewrite -> mult_plus_distr_r.
  rewrite -> plus_assoc.
  rewrite -> (mult_comm x y).
  reflexivity.
Qed.

Lemma about_sum_odd_numbers :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall n : nat,
      sum (fun i => S (2 * i)) n = S n * S n.
Proof.
  intros sum S_sum n.
  induction n as [ | n' IHn'].
    unfold specification_of_sum in S_sum.
    destruct (S_sum (fun i : nat => S (2 * i))) as [H_sum_bc _].
    clear S_sum.
    rewrite -> (H_sum_bc).
    rewrite -> (mult_0_r 2).
    rewrite -> (mult_1_r 1).
    reflexivity.
  unfold specification_of_sum in S_sum.
  destruct (S_sum (fun i : nat => S (2 * i))) as [_ H_sum_ic].
  clear S_sum.
  rewrite -> (H_sum_ic n').
  rewrite -> IHn'.
  rewrite -> (unfold_mult_ic 1 (S n')).
  rewrite -> (unfold_mult_ic 0 (S n')).
  rewrite -> (unfold_mult_bc (S n')).
  rewrite -> (plus_0_r (S n')).
  rewrite <- (plus_Sn_m (S n') (S n')).
  rewrite -> (mult_succ_l (S n') (S (S n'))).
  rewrite -> (mult_succ_r (S n') (S n')).
  rewrite -> (plus_comm (S (S n')) (S n')).
  rewrite plus_assoc.
  reflexivity.
Qed.

(* ***** *)

(* From the June exam of dProgSprog 2012-2013: *)

Lemma factor_sum_on_the_left :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall (h : nat -> nat)
           (c k : nat),
      sum (fun x => c * h x) k = c * sum (fun x => h x) k.
Proof.
  intros sum S_sum h c k.
Abort.


(* Replace "Abort." with a proof. *)

Lemma factor_sum_on_the_right :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall (h : nat -> nat)
           (c k : nat),
      sum (fun x => h x * c) k = (sum (fun x => h x) k) * c.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

Theorem June_exam :
  forall sum : (nat -> nat) -> nat -> nat,
    specification_of_sum sum ->
    forall (f g : nat -> nat)
           (m n : nat),
      sum (fun i => sum (fun j => f i * g j) n) m =
      (sum (fun i => f i) m) * (sum (fun j => g j) n).
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* Food for thought:
   is the following specification of sum
   equivalent to the one above?
*)

Definition alt_specification_of_sum (sum : (nat -> nat) -> nat -> nat) :=
  (forall f : nat -> nat,
    sum f 0 = f 0)
  /\
  (forall (f : nat -> nat)
          (n' : nat),
     sum f (S n') = sum f n' + f (S n')).

(* ********** *)

(* A first implementation: *)

Fixpoint sum_ds (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S n' => sum_ds f n' + f n
  end.

Lemma unfold_sum_ds_bc :
  forall f : nat -> nat,
    sum_ds f 0 = f 0.
(* left-hand side in the base case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic sum_ds.
Qed.

Lemma unfold_sum_ds_ic :
  forall (f : nat -> nat)
         (n' : nat),
    sum_ds f (S n') = sum_ds f n' + f (S n').
(* left-hand side in the inductive case
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic sum_ds.
Qed.

Definition sum_v0 (f : nat -> nat) (n : nat) : nat :=
  sum_ds f n.

Compute unit_tests_for_sum sum_v0.

Theorem sum_v0_satisfies_the_specification_of_sum :
  specification_of_sum sum_v0.
Proof.
  unfold specification_of_sum.
  unfold sum_v0.
  intro f.
  split.
Abort.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* A second implementation: *)

Fixpoint sum_ds' (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S n' => f n + sum_ds' f n'
  end.

Definition sum_v1 (f : nat -> nat) (n : nat) : nat :=
  sum_ds' f n.

Compute unit_tests_for_sum sum_v1.

Theorem sum_v1_satisfies_the_specification_of_sum :
  specification_of_sum sum_v1.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(*
   Prove the equivalence of sum_v0 and sum_v1.
*)

Theorem sum_v0_and_sum_v1_are_functionally_equal :
  forall (f : nat -> nat)
         (n : nat),
    sum_v0 f n = sum_v1 f n.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* A third implementation: *)

Fixpoint sum_acc (f : nat -> nat) (n a : nat) : nat :=
  match n with
  | 0 => f 0 + a
  | S n' => sum_acc f n' (a + f n)
  end.

Definition sum_v2 (f : nat -> nat) (n : nat) : nat :=
  sum_acc f n 0.

(* Does this implementation fit the specification of sum? *)

(* ********** *)

(* A fourth implementation: *)

Fixpoint sum_acc' (f : nat -> nat) (n a : nat) : nat :=
  match n with
  | 0 => f 0 + a
  | S n' => sum_acc f n' (f n + a)
  end.

Definition sum_v3 (f : nat -> nat) (n : nat) : nat :=
  sum_acc' f n 0.

(* Does this implementation fit the specification of sum? *)

(* ********** *)

(* end of week_37a_sum.v *)
