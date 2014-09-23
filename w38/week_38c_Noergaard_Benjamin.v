(* week_38c_mystery_functions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working file. *)

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
  intros f g S_fun_0_f S_fun_0_g n.
  unfold specification_of_the_mystery_function_0 in S_fun_0_f.
  destruct S_fun_0_f as [H_fun_0_f_bc H_fun_0_f_ic].
  unfold specification_of_the_mystery_function_0 in S_fun_0_g.
  destruct S_fun_0_g as [H_fun_0_g_bc H_fun_0_g_ic].
  induction n as [ | n' IHn'].
    rewrite -> H_fun_0_g_bc.
    exact H_fun_0_f_bc.
  rewrite -> (plus_n_O n').
  rewrite -> H_fun_0_f_ic.
  rewrite -> H_fun_0_f_bc.
  rewrite -> H_fun_0_g_ic.
  rewrite -> H_fun_0_g_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_0:
*)
Definition unit_test_for_the_mystery_function_0 (f : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (f 0 =n= 1)
  &&
  (f 1 =n= 2)
  &&
  (f 2 =n= 3)
  &&
  (f 3 =n= 4)
  &&
  (f 21 =n= 22)
  .

Compute unit_test_for_the_mystery_function_0 S.

(* ***** *)

Theorem and_the_mystery_function_0_is_S :
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
  intros f g.
  unfold specification_of_the_mystery_function_1.
  intros [S_fun_1_f_bc S_fun_1_f_ic] [S_fun_1_g_bc S_fun_1_g_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> S_fun_1_g_bc.
    exact S_fun_1_f_bc.
  rewrite -> (plus_n_O n').
  rewrite -> plus_n_Sm.
  rewrite -> S_fun_1_f_ic.
  rewrite -> S_fun_1_f_bc.
  rewrite -> S_fun_1_g_ic.
  rewrite -> S_fun_1_g_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ***** *)

(* Flesh out the following unit test
   as you tabulate mystery_function_1:
*)
Definition unit_test_for_the_mystery_function_1 (f : nat -> nat) :=
(*
   The following equality is in the specification:
*)
  (f 0 =n= 0)
  &&
  (f 1 =n= 1)
  &&
  (f 2 =n= 2)
  &&
  (f 3 =n= 3)
  &&
  (f 42 =n= 42)
  .

Compute unit_test_for_the_mystery_function_1 (fun x => x).

(* ***** *)

Theorem and_the_mystery_function_1_is_the_identity :
  specification_of_the_mystery_function_1 (fun x => x).
Proof.
  unfold specification_of_the_mystery_function_1.
  split.
    reflexivity.
  intros i j.
  reflexivity.
Qed.  

(* ********** *)

Definition specification_of_the_mystery_function_2 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).

Proposition there_is_only_one_mystery_function_2 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_2 f ->
    specification_of_the_mystery_function_2 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g.
  unfold specification_of_the_mystery_function_2.
  intros [S_fun2f_bc S_fun2f_ic] [S_fun2g_bc S_fun2g_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> S_fun2g_bc.
    exact S_fun2f_bc.
  rewrite -> (plus_n_O n').
  rewrite -> S_fun2f_ic.
  rewrite -> S_fun2f_bc.
  rewrite -> S_fun2g_ic.
  rewrite -> S_fun2g_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_2 (f : nat -> nat) :=
  (f 0 =n= 0)
  &&
  (f 1 =n= 2)
  &&
  (f 2 =n= 4)
  &&
  (f 3 =n= 6)
  &&
  (f 10 =n= 20)
  &&
  (f 21 =n= 42).

Compute unit_test_for_the_mystery_function_2 (mult 2).

Theorem and_the_mystery_function_2_is_multiplication_by_2 :
  specification_of_the_mystery_function_2 (mult 2).
Proof.
  unfold specification_of_the_mystery_function_2.
  split.
    rewrite -> mult_0_r.
    reflexivity.
  intros i j.
  rewrite -> mult_succ_r.
  rewrite -> mult_plus_distr_l.
  rewrite -> (plus_comm (2*i + 2*j) 2).
  rewrite -> plus_assoc.
  rewrite -> (plus_Sn_m 1 (2*i)).
  rewrite -> (plus_n_Sm 1 (2*i)).
  rewrite -> (plus_comm (1 + S (2 * i)) (2*j)).
  rewrite -> plus_assoc.
  rewrite -> (plus_comm (2*j) 1).
  rewrite -> (plus_Sn_m 0 (2*j)).
  rewrite -> plus_0_l.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_3 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = S (f i) + S (f j)).

Proposition there_is_only_one_mystery_function_3 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_3 f ->
    specification_of_the_mystery_function_3 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [S_fun3f_bc S_fun3f_ic] [S_fun3g_bc S_fun3g_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> S_fun3g_bc.
    exact S_fun3f_bc.
  rewrite -> (plus_n_O n').
  rewrite -> S_fun3f_ic.
  rewrite -> S_fun3f_bc.
  rewrite -> S_fun3g_ic.
  rewrite -> S_fun3g_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_3 (f : nat -> nat) :=
  (f 0 =n= 1)
  &&
  (f 1 =n= 4)
  &&
  (f 2 =n= 7)
  &&
  (f 3 =n= 10)
  &&
  (f 4 =n= 13).

Compute unit_test_for_the_mystery_function_3 (fun x => 3 * x + 1).

Theorem and_the_mystery_function_3_is_the_odd_case_of_collatz :
  specification_of_the_mystery_function_3 (fun x => 3 * x + 1).
Proof.
  unfold specification_of_the_mystery_function_3.
  split.
    rewrite -> mult_0_r.
    rewrite -> plus_0_l.
    reflexivity.
  intros i j.
  rewrite -> plus_n_Sm.
  rewrite -> mult_plus_distr_l.
  rewrite -> mult_succ_r.
  rewrite -> (plus_comm (3*i + (3 * j + 3)) 1).
  rewrite -> plus_assoc.
  rewrite -> (plus_comm 1 (3 * i)).
  rewrite -> plus_assoc.
  rewrite -> (plus_comm (3 * i + 1 + 3 * j) 3).
  rewrite -> plus_assoc.
  rewrite -> (plus_Sn_m 2 (3 * i + 1)).
  rewrite -> plus_n_Sm.
  rewrite -> (plus_comm (2 + S (3 * i + 1)) (3*j)).
  rewrite -> plus_assoc.
  rewrite -> (plus_comm (3 * j) 2).
  rewrite -> plus_Sn_m.
  rewrite -> (plus_comm 1 (3 * j)).
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_4 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i j : nat,
    f (i + j) = f i + f j).

Proposition there_is_only_one_mystery_function_4 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_4 f ->
    specification_of_the_mystery_function_4 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [S_fun4f_bc S_fun4f_ic] [S_fun4g_bc S_fun4g_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> S_fun4g_bc.
    exact S_fun4f_bc.
  Check plus_n_Sm.
  rewrite <- (plus_0_r n').
  rewrite -> (plus_n_Sm n' 0).
  rewrite -> S_fun4f_ic.
Abort.

Theorem and_the_mystery_function_4_is_0 :
  specification_of_the_mystery_function_4 (fun n => 0).
Proof.
  unfold specification_of_the_mystery_function_4.
  split.
    reflexivity.
  intros n m.
  rewrite -> plus_0_r.
  reflexivity.
Qed.

Theorem but_the_mystery_function_4_can_also_be_2n :
  specification_of_the_mystery_function_4 (fun n => n + n).
Proof.
  unfold specification_of_the_mystery_function_4.
  split.
    rewrite -> plus_0_r.
    reflexivity.
  intros i j.
  rewrite -> plus_assoc.
  rewrite -> (plus_comm i j).
  rewrite -> (plus_comm (j + i + i) j).
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  rewrite <- (plus_assoc (j + j) i i).
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_5 (f : nat -> nat) :=
  (f 0 = 0)
  /\
  (forall i : nat,
    f (S i) = S (2 * i + f i)).

Proposition there_is_only_one_mystery_function_5 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_5 f ->
    specification_of_the_mystery_function_5 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [S_fun5f_bc S_fun5f_ic] [S_fun5g_bc S_fun5g_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> S_fun5g_bc.
    exact S_fun5f_bc.
  rewrite -> S_fun5f_ic.
  rewrite -> S_fun5g_ic.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_5 (f : nat -> nat) :=
  (f 0 =n= 0)
  &&
  (f 1 =n= 1)
  &&
  (f 2 =n= 4)
  &&
  (f 3 =n= 9)
  &&
  (f 4 =n= 16)
  &&
  (f 10 =n= 100).

Compute unit_test_for_the_mystery_function_5 (fun n => n * n).

Theorem and_the_mystery_function_5_is_square :
  specification_of_the_mystery_function_5 (fun n => n * n).
Proof.
  unfold specification_of_the_mystery_function_5.
  split.
    rewrite -> mult_0_l.
    reflexivity.
  intro i.
  rewrite -> mult_succ_r.
  rewrite -> mult_succ_l.
  rewrite <- (plus_n_Sm (i * i + i) i).
  rewrite -> mult_succ_l.
  rewrite -> mult_1_l.
  rewrite -> (plus_comm (i + i)).
  rewrite -> plus_assoc.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_6 (f : nat -> nat) :=
  (forall i j : nat,
    f (i + j) = f i + 2 * i * j + f j).

Proposition there_is_only_one_mystery_function_6 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_6 f ->
    specification_of_the_mystery_function_6 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g S_fun6f S_fun6g n.
  induction n as [ | n' IHn'].
Abort.

(* ********** *)

Definition specification_of_the_mystery_function_7 (f : nat -> nat) :=
  (f 0 = 1)
  /\
  (forall i j : nat,
    f (S (i + j)) = 2 * f i * f j).

Proposition there_is_only_one_mystery_function_7 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_7 f ->
    specification_of_the_mystery_function_7 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [S_fun7f_bc S_fun7f_ic] [S_fun7g_bc S_fun7g_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> S_fun7g_bc.
    exact S_fun7f_bc.
  rewrite <- (plus_0_r n').
  rewrite -> S_fun7f_ic.
  rewrite -> S_fun7f_bc.
  rewrite -> S_fun7g_ic.
  rewrite -> S_fun7g_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

Definition unit_test_for_the_mystery_function_7 (f : nat -> nat) :=
  (f 0 =n= 1)
  &&
  (f 1 =n= 2)
  &&
  (f 2 =n= 4)
  &&
  (f 3 =n= 8)
  &&
  (f 4 =n= 16)
  &&
  (f 10 =n= 1024).

Fixpoint pow n m :=
  match m with
  | 0 => 1
  | S m => n * (pow n m)
  end.

Infix "^" := pow : nat_scope.

Compute unit_test_for_the_mystery_function_7 (pow 2).

Require Import unfold_tactic.

Lemma unfold_pow_bc :
  forall n : nat,
    pow n 0 = 1.
Proof.
  unfold_tactic pow.
Qed.

Lemma unfold_pow_ic :
  forall n m : nat,
    pow n (S m) = n * (pow n m).
Proof.
  unfold_tactic pow.
Qed.

Lemma pow_plus_exponent :
  forall n m p : nat,
    pow n (m + p) = pow n m * pow n p.
Proof.
  intros n m p.
  induction m as [ | m' IHm'].
    rewrite -> plus_0_l.
    rewrite -> unfold_pow_bc.
    rewrite -> mult_1_l.
    reflexivity.
  rewrite -> plus_Sn_m.
  rewrite -> unfold_pow_ic.
  rewrite -> IHm'.
  rewrite -> mult_assoc.
  rewrite <- unfold_pow_ic.
  reflexivity.
Qed.

Theorem and_the_mystery_function_7_is_pow2n :
  specification_of_the_mystery_function_7 (pow 2).
Proof.
  unfold specification_of_the_mystery_function_7.
  split.
    apply unfold_pow_bc.
  intros i j.
  rewrite -> (unfold_pow_ic 2 (i + j)).
  rewrite -> (pow_plus_exponent 2 i j).
  rewrite -> mult_assoc.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_the_mystery_function_8 (f : nat -> nat) :=
  (f 0 = 2)
  /\
  (forall i j : nat,
    f (S (i + j)) = f i * f j).

Proposition there_is_only_one_mystery_function_8 :
  forall f g : nat -> nat,
    specification_of_the_mystery_function_8 f ->
    specification_of_the_mystery_function_8 g ->
    forall n : nat,
      f n = g n.
Proof.
  intros f g [S_fun8f_bc S_fun8f_ic] [S_fun8g_bc S_fun8g_ic] n.
  induction n as [ | n' IHn'].
    rewrite -> S_fun8g_bc.
    exact S_fun8f_bc.
  rewrite <- (plus_0_r n').
  rewrite -> S_fun8f_ic.
  rewrite -> S_fun8f_bc.
  rewrite -> S_fun8g_ic.
  rewrite -> S_fun8g_bc.
  rewrite -> IHn'.
  reflexivity.
Qed.

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

(* end of week_38c_mystery_functions.v *)
