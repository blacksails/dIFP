(* week_38a_recap.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* Learning goals for this week:

   - Using previous lemmas (with rewrite or apply)
     without giving them all their arguments,
     and
     acquiring a sense of which arguments are actually needed,
     to disambiguate.

     To this end, all the proofs of this week's exercises
     should be in two versions, separated by "Restart.":
     * in the first version,
       all the uses of previous lemmas
       should have _complete arguments_; and
     * in the second version,
       all the uses of previous lemmas
       should have _as few arguments as possible_.

   - at

   - The exact tactic:
     it is like apply, requires all the arguments,
     and is used to complete a subgoal.

   - The f_equal tactic:
     it is like f_equal_S,
     just for any function rather than just for S.

   - Proofs by case.

   - Searching the libraries.
*)

(* ********** *)

Require Import Arith Bool.

Search (_ + _ = _ + _ -> _ = _).

SearchAbout plus.

(* ********** *)

Require Import unfold_tactic.

Lemma unfold_plus_bc :
  forall y : nat,
    0 + y = y.
(* left-hand side in the base case of plus
   =
   the corresponding conditional branch *)
Proof.
  unfold_tactic plus.
Qed.

Lemma unfold_plus_ic :
  forall x' y : nat,
    (S x') + y = S (x' + y).
(* left-hand side in the inductive case of plus
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

(* ***** *)

Lemma plus_1_l :
  forall x : nat,
    1 + x = S x.
Proof.
  intro x.
  rewrite -> (unfold_plus_ic 0).
  rewrite -> (unfold_plus_bc x).
  reflexivity.

  Restart.

  intro x.
  rewrite -> unfold_plus_ic.
  rewrite -> unfold_plus_bc.
  reflexivity.
Qed.

Lemma plus_1_r :
  forall x : nat,
    x + 1 = S x.
Proof.
  intro x.
  rewrite -> (plus_comm x 1).
  exact (plus_1_l x).

  Restart.

  intro x.
  rewrite -> plus_comm.
  apply plus_1_l.
Qed.

(* ***** *)

Lemma f_equal_S :
  forall x y : nat,
    x = y -> S x = S y.
Proof.
  intros x y.
  intro H_xy.
  rewrite -> H_xy.
  reflexivity.

  Restart.

  Check f_equal.
  Check (f_equal S).
  apply (f_equal S).

  Restart.

  exact (f_equal S).

  Restart.

  apply f_equal.
Qed.

Lemma f_equal_plus_1 :
  forall x y : nat,
    x = y -> 1 + x = 1 + y.
Proof.
  exact (f_equal (plus 1)).

  Restart.

  apply f_equal.
Qed.

Lemma f_equal_plus_10 :
  forall x y : nat,
    x = y -> 10 + x = 10 + y.
Proof.
  exact (f_equal (plus 10)).

  Restart.

  apply f_equal.
Qed.

Lemma f_equal_plus_20 :
  forall x y : nat,
    x = y -> x + 20 = 20 + y.
Proof.
  intros x y H_xy.
  rewrite -> (plus_comm x 20).
  exact (f_equal (plus 20) H_xy).

  Restart.

  intros x y H_xy.
  rewrite -> plus_comm.
  apply f_equal.
  exact H_xy.
Qed.

Lemma f_equal_plus_30 :
  forall x y : nat,
    x = y -> 30 + x = y + 30.
Proof.
  intros x y H_xy.
  rewrite -> (plus_comm y 30).
  exact (f_equal (plus 30) H_xy).

  Restart.

  intros x y H_xy.
  rewrite -> plus_comm.

  Restart.

  intros x y H_xy.
  rewrite -> (plus_comm y 30).

  Restart.

  intros x y H_xy.
  rewrite -> (plus_comm y _).

  Restart.

  intros x y H_xy.
  rewrite -> (plus_comm _ 30).

  apply f_equal.
  exact H_xy.
Qed.

(* ********** *)

(* Binomial expansion at rank 2: *)

Definition square (x : nat) : nat :=
  x * x.

Lemma unfold_square :
  forall x : nat,
    square x = x * x.
Proof.
  unfold_tactic square.
Qed.

Lemma binomial_2 :
  forall x y : nat,
    square (x + y) = square x + 2 * x * y + square y.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

(* ********** *)

(* [To be done at home, let's skip to the evenp example.] *)

(* The power (i.e., exponentiation) function: *)

(* A unit test: *)

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_test_for_power (candidate : nat -> nat -> nat) :=
  (candidate 2 0 =n= 1)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 10 =n= 1024)
  .

(* A specification: *)

Definition specification_of_power (power : nat -> nat -> nat) :=
  (forall x : nat,
     power x 0 = 1)
  /\
  (forall x n' : nat,
     power x (S n') = x * (power x n')).

(* Uniqueness of the specification: *)

Proposition there_is_only_one_power :
  forall power1 power2 : nat -> nat -> nat,
    specification_of_power power1 ->
    specification_of_power power2 ->
    forall x n : nat,
      power1 x n = power2 x n.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

(* Some lemmas about power: *)

Lemma about_power_base_one :
  forall power : nat -> nat -> nat,
    specification_of_power power ->
    forall n : nat,
      power 1 n = 1.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

Lemma about_power_base_mult :
  forall power : nat -> nat -> nat,
    specification_of_power power ->
    forall x y n : nat,
      power (x * y) n = (power x n) * (power y n).
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

Lemma about_power_exponent_plus :
  forall power : nat -> nat -> nat,
    specification_of_power power ->
    forall x i j : nat,
      power x (i + j) = (power x i) * (power x j).
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

Lemma about_power_exponent_mult :
  forall power : nat -> nat -> nat,
    specification_of_power power ->
    forall x i j : nat,
      power x (i * j) = power (power x i) j.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

(* ***** *)

(* First implementation: *)

Fixpoint power_v1 (x n : nat) : nat :=
  match n with
    | 0 => 1
    | S n' => x * (power_v1 x n')
  end.

Compute unit_test_for_power power_v1.
(*
     = true
     : bool
*)

Lemma unfold_power_v1_bc :
  forall x : nat,
    power_v1 x 0 = 1.
Proof.
  unfold_tactic power_v1.
Qed.

Lemma unfold_power_v1_ic :
  forall x n' : nat,
    power_v1 x (S n') = x * (power_v1 x n').
Proof.
  unfold_tactic power_v1.
Qed.

Proposition power_v1_satisfies_the_specification_of_power :
  specification_of_power power_v1.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

(* ***** *)

(* Second implementation
   (lambda-dropped version of the first): *)

Definition power_v2 (x n_orig : nat) : nat :=
  let fix visit (n : nat) : nat :=
      match n with
        | 0 => 1
        | S n' => x * (visit n')
      end
  in visit n_orig.

Compute unit_test_for_power power_v2.
(*
     = true
     : bool
*)

Lemma unfold_power_v2_bc :
  forall x : nat,
    power_v2 x 0 = 1.
Proof.
  unfold_tactic power_v2.
Qed.

Lemma unfold_power_v2_ic :
  forall x n' : nat,
    power_v2 x (S n') = x * (power_v2 x n').
Proof.
  unfold_tactic power_v2.
Qed.

Proposition power_v2_satisfies_the_specification_of_power :
  specification_of_power power_v2.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

(* ***** *)

(* Third implementation (version with an accumulator): *)

Fixpoint power_acc (x n a : nat) : nat :=
  match n with
    | 0 => a
    | S n' => power_acc x n' (x * a)
  end.

Definition power_v3 (x n : nat) : nat :=
  power_acc x n 1.

Compute unit_test_for_power power_v3.
(*
     = true
     : bool
*)

Lemma unfold_power_acc_bc :
  forall x a : nat,
    power_acc x 0 a = a.
Proof.
  unfold_tactic power_acc.
Qed.

Lemma unfold_power_acc_ic :
  forall x n' a : nat,
    power_acc x (S n') a = power_acc x n' (x * a).
Proof.
  unfold_tactic power_acc.
Qed.

Proposition power_v3_satisfies_the_specification_of_power :
  specification_of_power power_v3.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

(* ********** *)

(* The even predicate: *)

(* A unit test: *)

Notation "A =b= B" := (eqb A B) (at level 70, right associativity).

Definition unit_test_for_evenp (candidate : nat -> bool) :=
  (candidate 0 =b= true)
  &&
  (candidate 1 =b= false)
  &&
  (candidate 2 =b= true)
  &&
  (candidate 3 =b= false)
  .

(* A specification: *)

Definition specification_of_evenp (evenp : nat -> bool) :=
  (evenp 0 = true)
  /\
  (evenp 1 = false)
  /\
  (forall n'' : nat,
     evenp (S (S n'')) = evenp n'').

(* Uniqueness of the specification: *)

Proposition there_is_only_one_evenp :
  forall f g : nat -> bool,
    specification_of_evenp f ->
    specification_of_evenp g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* Properties: *)

Lemma about_evenp :
  forall evenp : nat -> bool,
    specification_of_evenp evenp ->
    forall x : nat,
      evenp (S x) = negb (evenp x).
Proof.
  intros evenp.
  unfold specification_of_evenp.
  intros [H_0 [H_1 H_SS]].
  intro x.
  induction x as [ | x' IHx'].

  rewrite -> H_1.
  rewrite -> H_0.
  unfold negb.
  reflexivity.

  rewrite -> H_SS.
  rewrite -> IHx'.
  destruct (evenp x') eqn:H_evenp_x'.

    unfold negb.
    reflexivity.

  unfold negb.
  reflexivity.
Qed.

Lemma about_evenp_of_a_sum :
  forall evenp : nat -> bool,
    specification_of_evenp evenp ->
    forall x y : nat,
      evenp (x + y) = eqb (evenp x) (evenp y).
Proof.
  intros evenp.
  unfold specification_of_evenp.
  intros [H_0 [H_1 H_SS]].
  intro x.
  induction x as [ | x' IHx'].

  intro y.
  rewrite -> plus_0_l.
  rewrite -> H_0.
  unfold eqb.
  destruct (evenp y) eqn:H_y.
    reflexivity.
  reflexivity.

  intros [ | y'].

  rewrite -> plus_0_r.
  rewrite -> H_0.
  destruct (evenp (S x')) eqn:H_evenp_Sx'.
  unfold eqb.
  reflexivity.

  unfold eqb.
  reflexivity.

  rewrite -> unfold_plus_ic.
  rewrite -> plus_comm.
  rewrite -> unfold_plus_ic.
  rewrite -> plus_comm.
  rewrite -> H_SS.
  rewrite -> IHx'.
  rewrite -> about_evenp.
  rewrite -> about_evenp.
  destruct (evenp x') eqn:H_evenp_x'.
    destruct (evenp y') eqn:H_evenp_y'.
      unfold negb.
      unfold eqb.
      reflexivity.
    unfold negb.
    unfold eqb.
    reflexivity.
  destruct (evenp y') eqn:H_evenp_y'.
    unfold negb.
    unfold eqb.
    reflexivity.
  unfold negb.
  unfold eqb.
  reflexivity.
Qed.

(* An implementation: *)

Fixpoint evenp_v0 (n : nat) : bool :=
  match n with
    | 0 => true
    | S n' => match n' with
                | 0 => false
                | S n'' => evenp_v0 n''
              end
  end.

Compute unit_test_for_evenp evenp_v0.
(*
     = true
     : bool
*)

(* Or equivalently (syntactic sugar): *)

Fixpoint evenp_v0' (n : nat) : bool :=
  match n with
    | 0 => true
    | S 0 => false
    | S (S n'') => evenp_v0' n''
  end.

Compute unit_test_for_evenp evenp_v0'.
(*
     = true
     : bool
*)

Lemma unfold_evenp_v0_bc0 :
  evenp_v0 0 = true.
Proof.
  unfold_tactic evenp_v0.
Qed.

Lemma unfold_evenp_v0_bc1 :
  evenp_v0 1 = false.
Proof.
  unfold_tactic evenp_v0.
Qed.

Lemma unfold_evenp_v0_ic :
  forall n'' : nat,
    evenp_v0 (S (S n'')) = evenp_v0 n''.
Proof.
  unfold_tactic evenp_v0.
Qed.

Proposition evenp_satisfies_the_specification_of_evenp :
  specification_of_evenp evenp_v0.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

(* ********** *)

(* The Fibonacci numbers: *)

(* A unit test: *)

Definition unit_test_for_fib (candidate: nat -> nat) :=
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

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.

(* Uniqueness of the specification: *)

Proposition there_is_only_one_fibonacci_function :
  forall fib1 fib2 : nat -> nat,
    specification_of_the_fibonacci_function fib1 ->
    specification_of_the_fibonacci_function fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* A first implementation: *)

Fixpoint fib_ds (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib_ds n' + fib_ds n''
              end
  end.

Definition fib_v0 (n : nat) : nat :=
  fib_ds n.

Compute unit_test_for_fib fib_v0.

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

Theorem fib_ds_fits_the_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function fib_ds.
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

Corollary fib_v0_fits_the_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function fib_v0.
Proof.
  unfold fib_v0.
  apply fib_ds_fits_the_specification_of_the_fibonacci_function.
Qed.

(* ***** *)

(* A second implementation, with an accumulator: *)

Fixpoint fib_acc (n a1 a0 : nat) : nat :=
  match n with
    | 0 => a0
    | S n' => fib_acc n' (a1 + a0) a1
  end.

Definition fib_v1 (n : nat) : nat :=
  fib_acc n 1 0.

Compute unit_test_for_fib fib_v1.

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

Lemma unfold_fib_v1 :
  forall n : nat,
    fib_v1 n = fib_acc n 1 0.
Proof.
  unfold_tactic fib_acc.
Qed.

(* Eureka lemma: *)

Lemma about_fib_acc :
  forall fib : nat -> nat,
    specification_of_the_fibonacci_function fib ->
    forall k i : nat,
      fib_acc k (fib (S i)) (fib i) = fib (k + i).
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)
Qed.

Theorem fib_v1_fits_the_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function fib_v1.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* ***** *)

(* A third implementation, with a co-accumulator: *)

Fixpoint fib_co_acc (n : nat) : nat * nat :=
  match n with
    | O => (1, 0)
    | S n' => let (a1, a0) := fib_co_acc n'
              in (a1 + a0, a1)
  end.

Definition fib_v2 (n : nat) : nat :=
  match n with
    | O => 0
    | S n' => let (a1, a0) := fib_co_acc n'
              in a1
  end.

Compute unit_test_for_fib fib_v2.

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

Lemma unfold_fib_v2_0 :
  fib_v2 0 = 0.
Proof.
  unfold_tactic fib_v2.
Qed.

Lemma unfold_fib_v2_Sn' :
  forall n' : nat,
    fib_v2 (S n') = let (a1, a0) := fib_co_acc n'
                    in a1.
Proof.
  unfold_tactic fib_v2.
Qed.

(* Eureka lemma: *)

Lemma about_fib_co_acc :
  forall fib : nat -> nat,
    specification_of_the_fibonacci_function fib ->
    forall n : nat,
      fib_co_acc n = (fib (S n), fib n).
Proof.
Abort.
(* Replace "Abort." with a (standard) proof. *)

Theorem fib_v2_fits_the_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function fib_v2.
Proof.
Abort.
(* Replace "Abort." with a proof. *)

(* ********** *)

(* end of week_38a_recap.v *)
