(* week_40b_fib.v *)
(* dIFP 2014-2015, Q1, Week 40 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

Require Import Arith Bool unfold_tactic.

Lemma plus_1_l :
  forall n : nat,
    1 + n = S n.
Proof.
  intro n.
  rewrite -> plus_Sn_m.
  rewrite -> plus_0_l.
  reflexivity.
Qed.

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Specialized induction principle: *)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc0 H_bc1 H_ic n.
  assert (H_Pn_PSn : P n /\ P (S n)).
    induction n as [ | n' [IH_n' IH_Sn']].
  
    split.

      apply H_bc0.

    apply H_bc1.
  
    split.

      apply IH_Sn'.

    apply (H_ic n' IH_n' IH_Sn').

  destruct H_Pn_PSn as [H_Pn _].
  apply H_Pn.
Qed.

(* ********** *)

Definition unit_test_for_the_fibonacci_function (candidate: nat -> nat) :=
  (candidate 0 =n= 0)
  &&
  (candidate 1 =n= 1)
  &&
  (candidate 2 =n= 1)
  &&
  (candidate 3 =n= 2)
  &&
  (candidate 4 =n= 3)
  &&
  (candidate 5 =n= 5)
  &&
  (candidate 6 =n= 8)
  &&
  (candidate 7 =n= 13)
  &&
  (candidate 8 =n= 21)
  &&
  (candidate 9 =n= 34)
  .

(* A specification: *)

Definition specification_of_fibonacci (fib : nat -> nat) :=
  (fib 0 = 0)
  /\
  (fib 1 = 1)
  /\
  (forall n'' : nat,
     fib (S (S n'')) = fib (S n'') + fib n'').

Theorem there_is_only_one_fibonacci :
  forall fib1 fib2 : nat -> nat,
    specification_of_fibonacci fib1 ->
    specification_of_fibonacci fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_fibonacci.
  intros [H_fib1_bc0 [H_fib1_bc1 H_fib1_ic]]
         [H_fib2_bc0 [H_fib2_bc1 H_fib2_ic]]
         n.
  induction n as [ | | n'' IHn'' IHSn''] using nat_ind2.

  rewrite -> H_fib2_bc0.
  apply H_fib1_bc0.

  rewrite -> H_fib2_bc1.
  apply H_fib1_bc1.

  rewrite -> H_fib1_ic.
  rewrite -> IHSn''.
  rewrite -> IHn''.
  rewrite <- H_fib2_ic.
  reflexivity.
Qed.

(* ********** *)

(* The fibonacci function in direct style: *)

Fixpoint fib_ds (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib_ds n' + fib_ds n''
              end
  end.

(*
Compute map fib_ds (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil).
     = 0 :: 1 :: 1 :: 2 :: 3 :: 5 :: 8 :: 13 :: nil
     : list nat
*)

(* Associated unfold lemmas: *)

Lemma unfold_fib_ds_base_case_0 :
  fib_ds 0 = 0.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma unfold_fib_ds_base_case_1 :
  fib_ds 1 = 1.
Proof.
  unfold_tactic fib_ds.
Qed.

Lemma unfold_fib_ds_induction_case :
  forall n'' : nat,
    fib_ds (S (S n'')) = fib_ds (S n'') + fib_ds n''.
Proof.
  unfold_tactic fib_ds.
Qed.

(* Main definition: *)

Definition fib_v0 (n : nat) : nat :=
  fib_ds n.

Compute unit_test_for_the_fibonacci_function fib_v0.

(* The main definition satisfies the specification: *)

Theorem fib_ds_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_ds.
Proof.
  unfold specification_of_fibonacci.
  split.

    apply unfold_fib_ds_base_case_0.

  split.

    apply unfold_fib_ds_base_case_1.

  intro n''.
  apply unfold_fib_ds_induction_case.
Qed.

Theorem fib_v0_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v0.
Proof.
  unfold fib_v0.
  exact fib_ds_satisfies_the_specification_of_fibonacci.
Qed.

(* ********** *)

(* The fibonacci function in continuation-passing style: *)

Fixpoint fib_cps (ans : Type) (n : nat) (k : nat -> ans) : ans :=
  match n with
    | 0 => k 0
    | S n' =>
      match n' with
        | 0 => k 1
        | S n'' =>
          fib_cps ans n' (fun v1 =>
                            fib_cps ans n'' (fun v2 =>
                                               k (v1 + v2)))
      end
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_cps_base_case_0 :
  forall (ans : Type) (k : nat -> ans),
    fib_cps ans 0 k = k 0.
Proof.
  unfold_tactic fib_cps.
Qed.

Lemma unfold_fib_cps_base_case_1 :
  forall (ans : Type) (k : nat -> ans),
    fib_cps ans 1 k = k 1.
Proof.
  unfold_tactic fib_cps.
Qed.

Lemma unfold_fib_cps_induction_case :
  forall (ans : Type) (n'' : nat) (k : nat -> ans),
    fib_cps ans (S (S n'')) k =
    fib_cps ans (S n'') (fun v1 => fib_cps ans n'' (fun v2 => k (v1 + v2))).
Proof.
  unfold_tactic fib_ds.
Qed.

(* Lemma about resetting the continuation: *)

Lemma about_fib_cps :
  forall (n : nat) (ans: Type) (k : nat -> ans),
    fib_cps ans n k = k (fib_cps nat n (fun a => a)).
Proof.
  intro n.
  induction n as [ | | n'' IHn'' IHSn''] using nat_ind2.

  intros ans k.
  rewrite -> unfold_fib_cps_base_case_0.
  rewrite -> unfold_fib_cps_base_case_0.
  reflexivity.

  intros ans k.
  rewrite -> unfold_fib_cps_base_case_1.
  rewrite -> unfold_fib_cps_base_case_1.
  reflexivity.

  intros ans k.
  rewrite -> unfold_fib_cps_induction_case.
  rewrite -> unfold_fib_cps_induction_case.
  rewrite -> IHSn''.
  rewrite -> IHn''.
  rewrite -> (IHSn'' nat (fun v1 => fib_cps nat n'' (fun v2 => v1 + v2))).
  rewrite -> (IHn'' nat (fun v2 => fib_cps nat (S n'') (fun v => v) + v2)).
  reflexivity.
Qed.
      
(* Main definition: *)

Definition fib_v1 (n : nat) : nat :=
  fib_cps nat n (fun v => v).

Compute unit_test_for_the_fibonacci_function fib_v1.

(* The main definition satisfies the specification: *)

Theorem fib_v1_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v1.
Proof.
  unfold specification_of_fibonacci.
  unfold fib_v1.
  split.

    rewrite -> unfold_fib_cps_base_case_0.
    reflexivity.

  split.

    rewrite -> unfold_fib_cps_base_case_1.
    reflexivity.

  intro n''.
  rewrite -> unfold_fib_cps_induction_case.
  rewrite -> about_fib_cps.
  rewrite -> about_fib_cps.
  reflexivity.
Qed.

(* ********** *)

(* The fibonacci function with an accumulator: *)

Fixpoint fib_acc (n a1 a0 : nat) : nat :=
  match n with
    | 0 => a0
    | S n' => fib_acc n' (a1 + a0) a1
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_acc_base_case :
  forall a1 a0 : nat,
    fib_acc 0 a1 a0 = a0.
Proof.
  unfold_tactic fib_acc.
Qed.

Lemma unfold_fib_acc_induction_case :
  forall n' a1 a0 : nat,
    fib_acc (S n') a1 a0 = fib_acc n' (a1 + a0) a1.
Proof.
  unfold_tactic fib_acc.
Qed.

(* Main definition: *)

Definition fib_v2 (n : nat) : nat :=
  fib_acc n 1 0.

Compute unit_test_for_the_fibonacci_function fib_v2.

(* Eureka lemma: *)

Lemma about_fib_acc :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall j i : nat,
      fib_acc j (fib (S i)) (fib i) = fib (j + i).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [_ [_ H_fib_ic]].
  intro j.
  induction j as [ | j' IHj'].

  intro i.
  rewrite -> unfold_fib_acc_base_case.
  rewrite -> plus_0_l.
  reflexivity.

  intro i.
  rewrite -> unfold_fib_acc_induction_case.
  rewrite <- (H_fib_ic i).
  rewrite -> (IHj' (S i)).
  rewrite -> plus_Snm_nSm.
  reflexivity.
Qed.

(* The main definition satisfies the specification: *)

Theorem fib_v2_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v2.
Proof.
  unfold specification_of_fibonacci.
  unfold fib_v2.
  split.

    apply unfold_fib_acc_base_case.

  split.

    rewrite -> unfold_fib_acc_induction_case.
    apply unfold_fib_acc_base_case.

  intro n''.

  rewrite <- unfold_fib_ds_base_case_1.
  rewrite <- unfold_fib_ds_base_case_0 at 2.
  rewrite -> (about_fib_acc fib_ds fib_ds_satisfies_the_specification_of_fibonacci (S (S n'')) 0).
  rewrite -> plus_0_r.

  rewrite <- unfold_fib_ds_base_case_0 at 2.
  rewrite -> (about_fib_acc fib_ds fib_ds_satisfies_the_specification_of_fibonacci (S n'') 0).
  rewrite -> plus_0_r.

  rewrite <- unfold_fib_ds_base_case_0 at 2.
  rewrite -> (about_fib_acc fib_ds fib_ds_satisfies_the_specification_of_fibonacci n'').  
  rewrite -> plus_0_r.

  apply unfold_fib_ds_induction_case.
Qed.

(* ********** *)

(* The fibonacci function with an accumulator in CPS: *)

Fixpoint fib_acc_cps (ans : Type) (n a1 a0 : nat) (k : nat -> ans) : ans :=
  match n with
    | 0 => k a0
    | S n' => fib_acc_cps ans n' (a1 + a0) a1 k
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_acc_cps_base_case :
  forall (ans: Type)
         (a1 a0 : nat)
         (k : nat -> ans),
    fib_acc_cps ans 0 a1 a0 k = k a0.
Proof.
  unfold_tactic fib_acc_cps.
Qed.

Lemma unfold_fib_acc_cps_induction_case :
  forall (ans: Type)
         (n' a1 a0 : nat)
         (k : nat -> ans),
    fib_acc_cps ans (S n') a1 a0 k =
    fib_acc_cps ans n' (a1 + a0) a1 k.
Proof.
  unfold_tactic fib_acc_cps.
Qed.

(* Main definition: *)

Definition fib_v3 (n : nat) : nat :=
  fib_acc_cps nat n 1 0 (fun a => a).

Compute unit_test_for_the_fibonacci_function fib_v3.

(* Eureka lemma: *)

Lemma about_fib_acc_cps :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall (ans : Type)
           (j i : nat)
           (k : nat -> ans),
      fib_acc_cps ans j (fib (S i)) (fib i) k =
      k (fib (j + i)).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [_ [_ H_fib_ic]].
  intros ans j.
  induction j as [ | j' IHj'].

  intros i k.
  rewrite -> unfold_fib_acc_cps_base_case.
  rewrite -> plus_0_l.
  reflexivity.

  intros i k.
  rewrite -> unfold_fib_acc_cps_induction_case.
  rewrite <- (H_fib_ic i).
  rewrite -> (IHj' (S i) k).
  rewrite -> plus_Snm_nSm.
  reflexivity.
Qed.

(* The main definition satisfies the specification: *)

Theorem fib_v3_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v3.
Proof.
  unfold specification_of_fibonacci.
  unfold fib_v3.
  split.

    apply unfold_fib_acc_cps_base_case.

  split.

    rewrite -> unfold_fib_acc_cps_induction_case.
    rewrite -> plus_0_r.
    rewrite -> unfold_fib_acc_cps_base_case.
    reflexivity.

  intro n''.

  rewrite <- unfold_fib_ds_base_case_1.
  rewrite <- unfold_fib_ds_base_case_0 at 2.
  rewrite -> (about_fib_acc_cps fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat (S (S n'')) 0).
  rewrite -> plus_0_r.

  rewrite <- unfold_fib_ds_base_case_1.
  rewrite <- unfold_fib_ds_base_case_0 at 2.
  rewrite -> (about_fib_acc_cps fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat (S n'') 0).
  rewrite -> plus_0_r.

  rewrite <- unfold_fib_ds_base_case_1.
  rewrite <- unfold_fib_ds_base_case_0 at 2.
  rewrite -> (about_fib_acc_cps fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat n'' 0).  
  rewrite -> plus_0_r.

  apply unfold_fib_ds_induction_case.
Qed.

(* ********** *)

(* The fibonacci function with a co-accumulator: *)

Fixpoint fib_co_acc (n : nat) : nat * nat :=
  match n with
    | O => (1, 0)
    | S n' => let (a1, a0) := fib_co_acc n'
              in (a1 + a0, a1)
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_co_acc_base_case :
  fib_co_acc 0 = (1, 0).
Proof.
  unfold_tactic fib_co_acc.
Qed.

Lemma unfold_fib_co_acc_induction_case :
  forall n' : nat,
    fib_co_acc (S n') = let (a1, a0) := fib_co_acc n'
                        in (a1 + a0, a1).
Proof.
  unfold_tactic fib_co_acc.
Qed.

(* Main definition: *)

Definition fib_v4 (n : nat) : nat :=
  let (a1, a0) := fib_co_acc n
  in a0.

Compute unit_test_for_the_fibonacci_function fib_v4.

(* Eureka lemma: *)

Lemma about_fib_co_acc :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      fib_co_acc n = (fib (S n), fib n).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [H_fib_bc_0 [H_fib_bc_1 H_fib_ic]].
  intro n.
  induction n as [ | n' IHn'].

  rewrite -> unfold_fib_co_acc_base_case.
  rewrite -> H_fib_bc_1.
  rewrite -> H_fib_bc_0.
  reflexivity.

  rewrite -> unfold_fib_co_acc_induction_case.
  rewrite -> IHn'.
  rewrite <- (H_fib_ic n').
  reflexivity.
Qed.

(* The main definition satisfies the specification: *)

Theorem fib_v4_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v4.
Proof.
  unfold specification_of_fibonacci.
  unfold fib_v4.
  split.

    rewrite -> unfold_fib_co_acc_base_case.
    reflexivity.

  split.

    rewrite -> unfold_fib_co_acc_induction_case.
    rewrite -> unfold_fib_co_acc_base_case.
    reflexivity.

  intro n''.
  rewrite -> (about_fib_co_acc fib_ds fib_ds_satisfies_the_specification_of_fibonacci (S n'')).
  rewrite -> (about_fib_co_acc fib_ds fib_ds_satisfies_the_specification_of_fibonacci n'').
  case n'' as [ | n'''].

  rewrite <- unfold_fib_ds_base_case_0 at 3.
  apply (unfold_fib_ds_induction_case 0).

  rewrite -> (about_fib_co_acc fib_ds fib_ds_satisfies_the_specification_of_fibonacci (S (S (S n''')))).
  apply (unfold_fib_ds_induction_case (S n''')).
Qed.

(* ********** *)

(* The fibonacci function with a co-accumulator in CPS: *)

Fixpoint fib_co_acc_cps (ans : Type) (n : nat) (k : nat * nat -> ans) : ans :=
  match n with
    | O =>
      k (1, 0)
    | S n' =>
      fib_co_acc_cps ans
                     n'
                     (fun p =>
                        match p with
                          | (a1, a0) =>
                            k (a1 + a0, a1)
                        end)
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_co_acc_cps_base_case :
  forall (ans : Type)
         (k : nat * nat -> ans),
    fib_co_acc_cps ans 0 k = k (1, 0).
Proof.
  unfold_tactic fib_co_acc_cps.
Qed.

Lemma unfold_fib_co_acc_cps_induction_case :
  forall (ans : Type)
         (n' : nat)
         (k : nat * nat -> ans),
    fib_co_acc_cps ans (S n') k =
    fib_co_acc_cps ans
                   n'
                   (fun p =>
                      match p with
                        | (a1, a0) =>
                          k (a1 + a0, a1)
                      end).
Proof.
  unfold_tactic fib_co_acc_cps.
Qed.

(* Main definition: *)

Definition fib_v5 (n : nat) : nat :=
  fib_co_acc_cps nat
                 n
                 (fun p =>
                    match p with
                      | (a1, a0) =>
                        a0
                    end).

Compute unit_test_for_the_fibonacci_function fib_v5.

(* Eureka lemma: *)

Lemma about_fib_co_acc_cps :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall (ans : Type)
           (n : nat)
           (k : nat * nat -> ans),
      fib_co_acc_cps ans n k =
      k (fib (S n), fib n).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [H_fib_bc_0 [H_fib_bc_1 H_fib_ic]].
  intros ans n.
  induction n as [ | n' IHn'].

  intro k.
  rewrite -> unfold_fib_co_acc_cps_base_case.
  rewrite -> H_fib_bc_1.
  rewrite -> H_fib_bc_0.
  reflexivity.

  intro k.
  rewrite -> unfold_fib_co_acc_cps_induction_case.
  rewrite -> IHn'.
  rewrite <- (H_fib_ic n').
  reflexivity.
Qed.

(* The main definition satisfies the specification: *)

Theorem fib_v5_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v5.
Proof.
  unfold specification_of_fibonacci.
  unfold fib_v5.
  split.

    rewrite -> unfold_fib_co_acc_cps_base_case.
    reflexivity.

  split.

    rewrite -> unfold_fib_co_acc_cps_induction_case.
    rewrite -> unfold_fib_co_acc_cps_base_case.
    reflexivity.

  intro n''.
  rewrite -> (about_fib_co_acc_cps fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat (S n'') _).
  rewrite -> (about_fib_co_acc_cps fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat n'' _).
  rewrite <- (unfold_fib_ds_induction_case n'').
  exact (about_fib_co_acc_cps fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat (S (S n'')) (fun p : nat * nat => let (a1, a0) := p in a0)).
Qed.

(* ********** *)

(* The fibonacci function with a co-accumulator in CPS with a curried continuation: *)

Fixpoint fib_co_acc_cps' (ans : Type) (n : nat) (k : nat -> nat -> ans) : ans :=
  match n with
    | O =>
      k 1 0
    | S n' =>
      fib_co_acc_cps' ans
                     n'
                     (fun a1 a0 =>
                        k (a1 + a0) a1)
  end.

(* Associated unfold lemmas: *)

Lemma unfold_fib_co_acc_cps'_base_case :
  forall (ans : Type)
         (k : nat -> nat -> ans),
    fib_co_acc_cps' ans 0 k = k 1 0.
Proof.
  unfold_tactic fib_co_acc_cps'.
Qed.

Lemma unfold_fib_co_acc_cps'_induction_case :
  forall (ans : Type)
         (n' : nat)
         (k : nat -> nat -> ans),
    fib_co_acc_cps' ans (S n') k =
    fib_co_acc_cps' ans
                    n'
                    (fun a1 a0 =>
                       k (a1 + a0) a1).
Proof.
  unfold_tactic fib_co_acc_cps'.
Qed.

(* Main definition: *)

Definition fib_v6 (n : nat) : nat :=
  fib_co_acc_cps' nat
                  n
                  (fun a1 a0 =>
                     a0).

Compute unit_test_for_the_fibonacci_function fib_v6.

(* Eureka lemma: *)

Lemma about_fib_co_acc_cps' :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall (ans : Type)
           (n : nat)
           (k : nat -> nat -> ans),
      fib_co_acc_cps' ans n k =
      k (fib (S n)) (fib n).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [H_fib_bc_0 [H_fib_bc_1 H_fib_ic]].
  intros ans n.
  induction n as [ | n' IHn'].

  intro k.
  rewrite -> unfold_fib_co_acc_cps'_base_case.
  rewrite -> H_fib_bc_1.
  rewrite -> H_fib_bc_0.
  reflexivity.

  intro k.
  rewrite -> unfold_fib_co_acc_cps'_induction_case.
  rewrite -> IHn'.
  rewrite <- (H_fib_ic n').
  reflexivity.
Qed.

(* The main definition satisfies the specification: *)

Theorem fib_v6_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v6.
Proof.
  unfold specification_of_fibonacci.
  unfold fib_v6.
  split.

    rewrite -> unfold_fib_co_acc_cps'_base_case.
    reflexivity.

  split.

    rewrite -> unfold_fib_co_acc_cps'_induction_case.
    rewrite -> unfold_fib_co_acc_cps'_base_case.
    reflexivity.

  intro n''.
  rewrite -> (about_fib_co_acc_cps' fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat (S n'') _).
  rewrite -> (about_fib_co_acc_cps' fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat n'' _).
  rewrite <- (unfold_fib_ds_induction_case n'').
  exact (about_fib_co_acc_cps' fib_ds fib_ds_satisfies_the_specification_of_fibonacci nat (S (S n'')) (fun a1 a0 : nat => a0)).
Qed.

(* ********** *)

(* end of week_40c_fib.v *)