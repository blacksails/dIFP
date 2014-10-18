(* filtering_lists.v *)
(* dIFP 2014-2015, Q1 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: Benjamin Nørgaard *)
(* Student number: 201209884 *)

(* ********** *)

(* The goal of this project is to study
   how to filter elements in or out of lists.
*)

Require Import List Bool.

Ltac unfold_tactic name :=
  intros; unfold name;
  reflexivity.

(* The Bool library defines
     true,
     false,
     andb (noted && in infix notation),
     orb (noted || in infix notation),
     and negb.
   It also provides the following equations:

    andb_true_l : forall b : bool, true && b = b
    andb_true_r : forall b : bool, b && true = b
   andb_false_l : forall b : bool, false && b = false
   andb_false_r : forall b : bool, b && false = false
    orb_false_l : forall b : bool, false || b = b
    orb_false_r : forall b : bool, b || false = b
     orb_true_r : forall b : bool, b || true = true
     orb_true_l : forall b : bool, true || b = true

   andb_true_iff
        : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true
   andb_false_iff:
     forall b1 b2 : bool, b1 && b2 = false <-> b1 = false \/ b2 = false
   orb_false_iff
        : forall b1 b2 : bool, b1 || b2 = false <-> b1 = false /\ b2 = false
   orb_true_iff
        : forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true

You will also have the use of the two following unfold lemmas:
*)

Lemma unfold_negb_base_case_true :
  negb true = false.
Proof.
  unfold_tactic negb.
Qed.

Lemma unfold_negb_base_case_false :
  negb false = true.
Proof.
  unfold_tactic negb.
Qed.

(* Also, when, among the assumptions, you have
     H_foo : true = false
   remember that the command
     discriminate H_foo.
   solves the current subgoal.
*)

(* And finally, remember that
      destruct blah as [...] eqn:H_blah.
    has the niceness of adding an assumption H_blah
    that reflects the destruction.  For example,
    if foo has type bool,
      destruct foo as [ | ] eqn:H_foo.
    will successively provide
      H_foo : foo = true
    and then
      H_foo : foo = false
*)

(* ********** *)

(* All of that said, here is a specification: *)

Definition specification_of_filter_in (filter_in : (nat -> bool) -> list nat -> list nat) :=
  (forall p : nat -> bool,
     filter_in p nil = nil)
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = true ->
     filter_in p (x :: xs') = x :: (filter_in p xs'))
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = false ->
     filter_in p (x :: xs') = filter_in p xs').

(* You are asked to:

   * write unit tests for filter_in;

   * prove whether this definition specifies a unique function;

   * implement a definition of filter_in that satisfies the
     specification;

   * prove the following theorems:
*)

(* We will use the following function to construct a function which compares two nat lists *)
Fixpoint beq_list (T : Type) (l1 l2 : list T) (comp : T -> T -> bool) := 
  match l1 with
  | nil =>
      match l2 with
      | nil => true
      | _ => false
      end
  | e :: l =>
      match l2 with
      | nil => false
      | e' :: l' =>
          match comp e e' with
          | false => false
          | true => beq_list T l l' comp
          end
      end
  end.

Require Import Arith.

Definition beq_nat_list (l1 l2 : list nat) :=
  beq_list nat l1 l2 beq_nat.

Notation "A =l= B" := (beq_nat_list A B) (at level 70, right associativity).

Fixpoint odd (n : nat) :=
  match n with
    | O => false
    | 1 => true
    | S (S n) => odd n
  end.

Definition even (n : nat) :=
  negb (odd n).

Definition unit_test_for_filter_in (candidate : (nat -> bool) -> list nat -> list nat) :=
  (candidate (fun _ => true) 
             (1 :: 2 :: 3 :: nil) =l= (1 :: 2 :: 3 :: nil))
  &&
  (candidate (fun _ => false) 
             (1 :: 2 :: 3 :: nil) =l= nil)
  &&
  (candidate (fun x => (beq_nat x 2)) 
             (1 :: 2 :: 3 :: nil) =l= (2 :: nil))
  &&
  (candidate (fun x => (even x))
             (1 :: 2 :: 3 :: nil) =l= (2 :: nil))
  &&
  (candidate (fun x => (odd x))
             (1 :: 2 :: 3 :: nil) =l= (1 :: 3 :: nil)).

Theorem there_is_only_one_filter_in :
  forall (f g : (nat -> bool) -> list nat -> list nat),
    specification_of_filter_in f ->
    specification_of_filter_in g ->
    forall (p : (nat -> bool)) (xs : list nat),
      f p xs = g p xs.
Proof.
  intros f g.
  intros S_f S_g.
  intros p xs.
  unfold specification_of_filter_in in S_f.
  destruct S_f as [H_f_nil [H_f_true H_f_false]]. 
  unfold specification_of_filter_in in S_g.
  destruct S_g as [H_g_nil [H_g_true H_g_false]].
  induction xs as [ | x xs' IHxs'].
    rewrite -> H_g_nil.
    apply (H_f_nil p).
  case (p x) as [ | ] eqn:H_p.
    rename H_p into H_p_true.
    rewrite -> (H_f_true p x xs' H_p_true).
    rewrite -> (H_g_true p x xs' H_p_true).
    rewrite -> IHxs'.
    reflexivity.
  rename H_p into H_p_false.
  rewrite -> (H_f_false p x xs' H_p_false).
  rewrite -> (H_g_false p x xs' H_p_false).
  apply IHxs'.
Qed.

Fixpoint filter_in_ds (p : nat -> bool) (xs : list nat) :=
  match xs with
  | nil => nil
  | x :: xs' => 
      match p x with
      | true => x :: filter_in_ds p xs'
      | false => filter_in_ds p xs'
      end
  end.

Definition filter_in_v0 (p : nat -> bool) (xs : list nat) :=
  filter_in_ds p xs.

Compute unit_test_for_filter_in filter_in_v0.

Lemma unfold_filter_in_ds_bc :
  forall (p : nat -> bool),
    filter_in_ds p nil = nil.
Proof.
  unfold_tactic filter_in_ds.
Qed.

Lemma unfold_filter_in_ds_ic :
  forall (p : nat -> bool) (x : nat) (xs' : list nat),
    filter_in_ds p (x :: xs') = 
      match p x with
      | true => x :: filter_in_ds p xs'
      | false => filter_in_ds p xs'
      end.
Proof.
  unfold_tactic filter_in_ds.
Qed.

Proposition filter_in_v0_fits_the_specification_of_filter_in :
  specification_of_filter_in filter_in_v0.
Proof.
  unfold specification_of_filter_in.
  split.
    intro p.
    unfold filter_in_v0.
    apply (unfold_filter_in_ds_bc p).
  split.
    intros p x xs'.
    intro H_p_true.
    unfold filter_in_v0.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p_true.
    reflexivity.
  intros p x xs'.
  intros H_p_false.
  unfold filter_in_v0.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p_false.
  reflexivity.
Qed.

(* The following lemma will be handy, because we will be able to use things we 
* have proven about filter_in_v0 for any filter_in satisfying the specification *)
Lemma any_filter_in_can_be_rewritten_to_filter_in_v0 :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall (p : nat -> bool) (xs : list nat),
      filter_in p xs = filter_in_v0 p xs.
Proof.
  intros filter_in S_filter_in.
  intros p xs.
  rewrite -> (there_is_only_one_filter_in filter_in
                                          filter_in_v0
                                          S_filter_in
                                          filter_in_v0_fits_the_specification_of_filter_in).
  reflexivity.
Qed.

Theorem about_filtering_in_all_of_the_elements :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall xs : list nat, (* I renamed this from ns to xs for consistency *)
      filter_in (fun _ => true) xs = xs.
Proof.
  intros filter_in S_filter_in.
  intro xs.
  rewrite -> (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in
                                                             S_filter_in).
  induction xs as [ | x xs' IHxs'].
    unfold filter_in_v0.
    rewrite -> unfold_filter_in_ds_bc.
    reflexivity.
  unfold filter_in_v0.
  rewrite -> unfold_filter_in_ds_ic.
  unfold filter_in_v0 in IHxs'.
  rewrite -> IHxs'.
  reflexivity.
Qed.

Theorem about_filtering_in_none_of_the_elements :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall xs : list nat, (* I renamed this from ns to xs for consistency *)
      filter_in (fun _ => false) xs = nil.
Proof.
  intros filter_in S_filter_in.
  intro xs.
  rewrite -> (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in 
                                                             S_filter_in).
  induction xs as [ | x xs' IHxs'].
    unfold filter_in_v0.
    rewrite unfold_filter_in_ds_bc.
    reflexivity.
  unfold filter_in_v0.
  rewrite -> unfold_filter_in_ds_ic.
  unfold filter_in_v0 in IHxs'.
  apply IHxs'.
Qed.

Theorem about_filtering_in_incrementally :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall (p1 p2 : nat -> bool)
           (xs : list nat), (* I renamed this to xs from ns for consistency *)
      filter_in p2 (filter_in p1 xs) =
      filter_in (fun n => andb (p1 n) (p2 n)) xs. 
      (* I renamed x to n in the above funtion to avoid automatic naming when
      * doing induction on xs*)
Proof.
  intros filter_in S_filter_in.
  intros p1 p2 xs.
  rewrite ->3 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in 
                                                              S_filter_in).
  unfold filter_in_v0.
  induction xs as [ | x xs' IHxs' ].
    rewrite -> (unfold_filter_in_ds_bc p1).
    rewrite -> (unfold_filter_in_ds_bc p2).
    rewrite -> unfold_filter_in_ds_bc.
    reflexivity.
  case (p1 x) as [ | ] eqn:H_p1.
    case (p2 x) as [ | ] eqn:H_p2.
      rename H_p1 into H_p1_true.
      rename H_p2 into H_p2_true.
      rewrite -> unfold_filter_in_ds_ic.
      rewrite -> H_p1_true.
      rewrite -> unfold_filter_in_ds_ic.
      rewrite -> H_p2_true.
      rewrite -> IHxs'.
      rewrite -> unfold_filter_in_ds_ic.
      rewrite -> H_p1_true.
      rewrite -> andb_true_l.
      rewrite -> H_p2_true.
      reflexivity.
    rename H_p1 into H_p1_true.
    rename H_p2 into H_p2_false.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p1_true.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p2_false.
    rewrite -> IHxs'.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p1_true.
    rewrite -> andb_true_l.
    rewrite -> H_p2_false.
    reflexivity.
  rename H_p1 into H_p1_false.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p1_false.
  rewrite -> IHxs'.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p1_false.
  rewrite -> andb_false_l.
  reflexivity.
Qed.
     
(* ********** *)
     
(* Here is another specification: *)
   
Definition specification_of_filter_out (filter_out : (nat -> bool) -> list nat -> list nat) :=
  (forall p : nat -> bool,
     filter_out p nil = nil)
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = true ->
     filter_out p (x :: xs') = filter_out p xs')
  /\
  (forall (p : nat -> bool)
          (x : nat)
          (xs' : list nat),
     p x = false ->
     filter_out p (x :: xs') = x :: (filter_out p xs')).

(* You are asked to:

   * write unit tests for filter_out;

   * prove whether this definition specifies a unique function;

   * implement a definition of filter_out that satisfies the
     specification;

   * prove properties that are analogue to filter_in; and to

   * prove the two following propositions:
*)

Definition unit_test_for_filter_out (candidate : (nat -> bool) -> list nat -> list nat) :=
  (candidate (fun _ => true) 
             (1 :: 2 :: 3 :: nil) =l= nil)
  &&
  (candidate (fun _ => false) 
             (1 :: 2 :: 3 :: nil) =l= (1 :: 2 :: 3 :: nil))
  &&
  (candidate (fun x => (beq_nat x 2)) 
             (1 :: 2 :: 3 :: nil) =l= (1 :: 3 :: nil))
  &&
  (candidate (fun x => (even x))
             (1 :: 2 :: 3 :: nil) =l= (1 :: 3 :: nil))
  &&
  (candidate (fun x => (odd x))
             (1 :: 2 :: 3 :: nil) =l= (2 :: nil)).

Theorem there_is_only_one_filter_out :
  forall (f g : (nat -> bool) -> list nat -> list nat),
    specification_of_filter_out f ->
    specification_of_filter_out g ->
    forall (p : (nat -> bool)) (xs : list nat),
      f p xs = g p xs.
Proof.
  intros f g.
  intros S_f S_g.
  intros p xs.
  unfold specification_of_filter_out in S_f.
  destruct S_f as [H_f_nil [H_f_true H_f_false]]. 
  unfold specification_of_filter_out in S_g.
  destruct S_g as [H_g_nil [H_g_true H_g_false]].
  induction xs as [ | x xs' IHxs'].
    rewrite -> (H_f_nil p).
    rewrite -> (H_g_nil p).
    reflexivity.
  case (p x) as [ | ] eqn:H_p.
    rename H_p into H_p_true.
    rewrite -> (H_f_true p x xs' H_p_true).
    rewrite -> (H_g_true p x xs' H_p_true).
    apply IHxs'.
  rename H_p into H_p_false.
  rewrite -> (H_f_false p x xs' H_p_false).
  rewrite -> (H_g_false p x xs' H_p_false).
  rewrite -> IHxs'.
  reflexivity.
Qed.

Fixpoint filter_out_ds (p : nat -> bool) (xs : list nat) :=
  match xs with
  | nil => nil
  | x :: xs' => 
      match p x with
      | true => filter_out_ds p xs'
      | false => x :: filter_out_ds p xs'
      end
  end.

Definition filter_out_v0 (p : nat -> bool) (xs : list nat) :=
  filter_out_ds p xs.

Compute unit_test_for_filter_out filter_out_v0.

Lemma unfold_filter_out_ds_bc :
  forall (p : nat -> bool),
    filter_out_ds p nil = nil.
Proof.
  unfold_tactic filter_out_ds.
Qed.

Lemma unfold_filter_out_ds_ic :
  forall (p : nat -> bool) (x : nat) (xs' : list nat),
    filter_out_ds p (x :: xs') = 
      match p x with
      | true => filter_out_ds p xs'
      | false => x :: filter_out_ds p xs'
      end.
Proof.
  unfold_tactic filter_out_ds.
Qed.

Proposition filter_out_v0_fits_the_specification_of_filter_out :
  specification_of_filter_out filter_out_v0.
Proof.
  unfold specification_of_filter_out.
  split.
    intro p.
    unfold filter_out_v0.
    apply (unfold_filter_out_ds_bc p).
  split.
    intros p x xs'.
    intros H_p_true.
    unfold filter_out_v0.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p_true.
    reflexivity.
  intros p x xs'.
  intro H_p_false.
  unfold filter_out_v0.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p_false.
  reflexivity.
Qed.

Lemma any_filter_out_can_be_rewritten_to_filter_out_v0 :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    forall (p : nat -> bool) (xs : list nat),
      filter_out p xs = filter_out_v0 p xs.
Proof.
  intros filter_out S_filter_out.
  intros p xs.
  rewrite -> (there_is_only_one_filter_out filter_out
                                           filter_out_v0
                                           S_filter_out
                                           filter_out_v0_fits_the_specification_of_filter_out).
  reflexivity.
Qed.

Theorem about_filtering_out_all_of_the_elements :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    forall xs : list nat,
      filter_out (fun _ => true) xs = nil.
Proof.
  intros filter_out S_filter_out.
  intro xs.
  rewrite -> (any_filter_out_can_be_rewritten_to_filter_out_v0 filter_out 
                                                               S_filter_out).
  induction xs as [ | x xs' IHxs'].
    unfold filter_out_v0.
    rewrite -> unfold_filter_out_ds_bc.
    reflexivity.
  unfold filter_out_v0.
  rewrite -> unfold_filter_out_ds_ic.
  unfold filter_out_v0 in IHxs'.
  apply IHxs'.
Qed.

Theorem about_filtering_out_none_of_the_elements :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    forall xs : list nat,
      filter_out (fun _ => false) xs = xs.
Proof.
  intros filter_out S_filter_out.
  intro xs.
  rewrite -> (any_filter_out_can_be_rewritten_to_filter_out_v0 filter_out 
                                                               S_filter_out).
  induction xs as [ | x xs' IHxs'].
    unfold filter_out_v0.
    rewrite unfold_filter_out_ds_bc.
    reflexivity.
  unfold filter_out_v0.
  rewrite unfold_filter_out_ds_ic.
  unfold filter_out_v0 in IHxs'.
  rewrite -> IHxs'.
  reflexivity.
Qed.

Theorem about_filtering_out_incrementally :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    forall (p1 p2 : nat -> bool)
           (xs : list nat),
      filter_out p2 (filter_out p1 xs) =
      filter_out (fun n => orb (p1 n) (p2 n)) xs.
Proof.
  intros filter_out S_filter_out.
  intros p1 p2 xs.
  rewrite ->3 (any_filter_out_can_be_rewritten_to_filter_out_v0 filter_out 
                                                                S_filter_out).
  unfold filter_out_v0.
  induction xs as [ | x xs' IHxs' ].
    rewrite -> (unfold_filter_out_ds_bc p1).
    rewrite -> (unfold_filter_out_ds_bc p2).
    rewrite -> unfold_filter_out_ds_bc.
    reflexivity.
  case (p1 x) as [ | ] eqn:H_p1.
    case (p2 x) as [ | ] eqn:H_p2.
      rename H_p1 into H_p1_true.
      rename H_p2 into H_p2_true.
      rewrite -> unfold_filter_out_ds_ic.
      rewrite -> H_p1_true.
      rewrite -> unfold_filter_out_ds_ic.
      rewrite -> H_p1_true.
      rewrite -> orb_true_l.
      apply IHxs'.
    rename H_p1 into H_p1_true.
    rename H_p2 into H_p2_false.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p1_true.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p1_true.
    rewrite -> orb_true_l.
    apply IHxs'.
  rename H_p1 into H_p1_false.
  case (p2 x) as [ | ] eqn:H_p2.
    rename H_p2 into H_p2_true.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p1_false.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p2_true.
    rewrite -> IHxs'.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p2_true.
    rewrite -> orb_true_r.
    reflexivity.
  rename H_p2 into H_p2_false.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p1_false.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p2_false.
  rewrite -> IHxs'.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p1_false.
  rewrite -> orb_false_l.
  rewrite -> H_p2_false.
  reflexivity.
Qed.


Proposition filter_out_from_filter_in :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    specification_of_filter_out (fun p ns => filter_in (fun n => negb (p n)) ns).
    (* Renamed x to n in the above innermost function to avoid automatic naming *)
Proof.
  intros filter_in S_filter_in.
  unfold specification_of_filter_out.
  split.
    intro p.
    rewrite -> (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in 
                                                               S_filter_in).
    unfold filter_in_v0.
    apply unfold_filter_in_ds_bc.
  split.
    intros p x xs'.
    intro H_p_true.
    rewrite ->2 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in 
                                                                S_filter_in).
    unfold filter_in_v0.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p_true.
    rewrite -> unfold_negb_base_case_true.
    reflexivity.
  intros p x xs'.
  intro H_p_false.
  rewrite ->2 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in 
                                                              S_filter_in).
  unfold filter_in_v0.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p_false.
  rewrite -> unfold_negb_base_case_false.
  reflexivity.
Qed.

Proposition filter_in_from_filter_out :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    specification_of_filter_in (fun p ns => filter_out (fun n => negb (p n)) ns).
Proof.
  intros filter_out S_filter_out.
  unfold specification_of_filter_in.
  split.
    intro p.
    rewrite -> (any_filter_out_can_be_rewritten_to_filter_out_v0 filter_out 
                                                                 S_filter_out).
    unfold filter_out_v0.
    apply unfold_filter_out_ds_bc.
  split.
    intros p x xs'.
    intro H_p_true.
    rewrite ->2 (any_filter_out_can_be_rewritten_to_filter_out_v0 filter_out
                                                                  S_filter_out).
    unfold filter_out_v0.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p_true.
    rewrite -> unfold_negb_base_case_true.
    reflexivity.
  intros p x xs'.
  intro H_p_false.
  rewrite ->2 (any_filter_out_can_be_rewritten_to_filter_out_v0 filter_out 
                                                                S_filter_out).
  unfold filter_out_v0.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p_false.
  rewrite -> unfold_negb_base_case_false.
  reflexivity.
Qed.

(* Which consequences of these propositions can you think of? *)

Definition filter_out_v1 (p : nat -> bool) (xs : list nat) :=
  filter_in_v0 (fun n => negb (p n)) xs.

Compute unit_test_for_filter_out filter_out_v1.

Proposition filter_out_v1_fits_the_specification_of_filter_out :
  specification_of_filter_out filter_out_v1.
Proof.
  unfold specification_of_filter_out.
  split.
    intro p.
    unfold filter_out_v1.
    unfold filter_in_v0.
    apply unfold_filter_in_ds_bc.
  split.
    intros p x xs'.
    intro H_p_true.
    unfold filter_out_v1.
    unfold filter_in_v0.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p_true.
    rewrite -> unfold_negb_base_case_true.
    reflexivity.
  intros p x xs'.
  intro H_p_false.
  unfold filter_out_v1.
  unfold filter_in_v0.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p_false.
  rewrite -> unfold_negb_base_case_false.
  reflexivity.
Qed.

Definition filter_in_v1 (p : nat -> bool) (xs : list nat) :=
  filter_out_v0 (fun n => negb (p n)) xs.

Compute unit_test_for_filter_in filter_in_v1.

Proposition filter_in_v1_fits_the_specification_of_filter_in :
  specification_of_filter_in filter_in_v1.
Proof.
  unfold specification_of_filter_in.
  split.
    intro p.
    unfold filter_in_v1.
    unfold filter_out_v0.
    apply unfold_filter_out_ds_bc.
  split.
    intros p x xs'.
    intro H_p_true.
    unfold filter_in_v1.
    unfold filter_out_v0.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p_true.
    rewrite -> unfold_negb_base_case_true.
    reflexivity.
  intros p x xs'.
  intro H_p_false.
  unfold filter_in_v1.
  unfold filter_out_v0.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p_false.
  rewrite -> unfold_negb_base_case_false.
  reflexivity.
Qed.

(* Using the two propositions above we could have proven filter_out theorems
* using the filter_in_ds unfold lemmas and vice versa. Let's try to do that in
* the following proofs. *)

Lemma any_filter_in_can_be_rewritten_to_filter_in_v1 :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall (p : nat -> bool) (xs : list nat),
      filter_in p xs = filter_in_v1 p xs.
Proof.
  intros filter_in S_filter_in.
  intros p xs.
  rewrite -> (there_is_only_one_filter_in filter_in
                                          filter_in_v1
                                          S_filter_in
                                          filter_in_v1_fits_the_specification_of_filter_in).
  reflexivity.
Qed.

Lemma any_filter_out_can_be_rewritten_to_filter_out_v1 :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    forall (p : nat -> bool) (xs : list nat),
      filter_out p xs = filter_out_v1 p xs.
Proof.
  intros filter_out S_filter_out.
  intros p xs.
  rewrite -> (there_is_only_one_filter_out filter_out
                                           filter_out_v1
                                           S_filter_out
                                           filter_out_v1_fits_the_specification_of_filter_out).
  reflexivity.
Qed.

(* ********** *)

(* What is the result

   * of applying filter_in to the concatenation of two lists? 
   
   * of applying filter_out to the concatenation of two lists?

   * of applying filter_in to a reversed list?

   * of applying filter_out to a reversed list?
*)

(* ********** *)

Lemma unfold_append_bc :
  forall (xs : list nat),
    nil ++ xs = xs.
Proof.
  apply app_nil_l.
Qed.

Lemma unfold_append_ic :
  forall (x : nat) (xs1' xs2 : list nat),
    (x :: xs1') ++ xs2 = x :: (xs1' ++ xs2).
Proof.
  intros x xs1' xs2.
  symmetry.
  apply app_comm_cons.
Qed.

Theorem about_filter_in_and_concatenation_of_lists :
  forall (filter_in : (nat -> bool) -> list nat -> list nat),
    specification_of_filter_in filter_in ->
    forall (p : nat -> bool) (xs1 xs2 : list nat),
      filter_in p (xs1 ++ xs2) = filter_in p xs1 ++ filter_in p xs2.
Proof.
  intros filter_in S_filter_in.
  intros p xs1 xs2.
  rewrite ->3 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in
                                                              S_filter_in).
  unfold filter_in_v0.
  induction xs1 as [ | x xs1' IHxs1'].
    rewrite -> unfold_append_bc.
    rewrite -> unfold_filter_in_ds_bc.
    rewrite -> unfold_append_bc.
    reflexivity.
  rewrite -> unfold_append_ic.
  case (p x) as [ | ] eqn:H_p.
    rename H_p into H_p_true.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p_true.
    rewrite -> IHxs1'.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p_true.
    rewrite -> unfold_append_ic.
    reflexivity.
  rename H_p into H_p_false.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p_false.
  rewrite -> IHxs1'.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p_false.
  reflexivity.
Qed.

Theorem about_filter_out_and_concatenation_of_lists :
  forall (filter_out : (nat -> bool) -> list nat -> list nat),
    specification_of_filter_out filter_out ->
    forall (p : nat -> bool) (xs1 xs2 : list nat),
      filter_out p (xs1 ++ xs2) = filter_out p xs1 ++ filter_out p xs2.
Proof.
  intros filter_out S_filter_out.
  intros p xs1 xs2.
  rewrite ->3 (any_filter_out_can_be_rewritten_to_filter_out_v0 filter_out S_filter_out).
  unfold filter_out_v0.
  induction xs1 as [ | x xs1' IHxs1'].
    rewrite -> unfold_append_bc.
    rewrite -> unfold_filter_out_ds_bc.
    rewrite -> unfold_append_bc.
    reflexivity.
  rewrite -> unfold_append_ic.
  case (p x) as [ | ] eqn:H_p.
    rename H_p into H_p_true.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p_true.
    rewrite -> IHxs1'.
    rewrite -> unfold_filter_out_ds_ic.
    rewrite -> H_p_true.
    reflexivity.
  rename H_p into H_p_false.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p_false.
  rewrite -> IHxs1'.
  rewrite -> unfold_filter_out_ds_ic.
  rewrite -> H_p_false.
  reflexivity.
  Show Proof.

  Restart.
  (* or proven by the help of the connection between filter_in and filter_out *)
  intros filter_out S_filter_out.
  intros p xs1 xs2.
  rewrite ->3 (any_filter_out_can_be_rewritten_to_filter_out_v1 filter_out
                                                                S_filter_out).
  unfold filter_out_v1.
  assert (S_filter_in_v0 := filter_in_v0_fits_the_specification_of_filter_in).
  apply (about_filter_in_and_concatenation_of_lists filter_in_v0
                                                    S_filter_in_v0
                                                    (fun n : nat => negb (p n))
                                                    xs1 xs2).
Qed.

Lemma unfold_reverse_bc :
  forall (T : Type),
    rev nil = (nil : list T).
Proof.
  unfold_tactic rev.
Qed.

Lemma unfold_reverse_ic :
  forall (T : Type) (x : T) (xs : list T),
    rev (x :: xs) = rev xs ++ x :: nil.
Proof.
  unfold_tactic rev.
Qed.

Theorem about_filter_in_and_reverse_list :
  forall (filter_in : (nat -> bool) -> list nat -> list nat),
    specification_of_filter_in filter_in ->
    forall (p : nat -> bool) (xs : list nat),
      filter_in p (rev xs) = rev (filter_in p xs).
Proof.
  intros filter_in S_filter_in.
  intros p xs.
  induction xs as [ | x xs' IHxs'].
    rewrite ->2 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in
                                                                S_filter_in).
    unfold filter_in_v0.
    rewrite -> unfold_reverse_bc.
    rewrite -> unfold_filter_in_ds_bc.
    rewrite -> unfold_reverse_bc.
    reflexivity.
  rewrite -> unfold_reverse_ic.
  case (p x) as [ | ] eqn:H_p.
    rename H_p into H_p_true.
    rewrite -> (about_filter_in_and_concatenation_of_lists filter_in
                                                           S_filter_in
                                                           p (rev xs') (x :: nil)).
    rewrite -> IHxs'.
    rewrite ->3 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in
                                                                S_filter_in).
    unfold filter_in_v0.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p_true.
    rewrite -> unfold_filter_in_ds_bc.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p_true.
    rewrite -> unfold_reverse_ic.
    reflexivity.
  rename H_p into H_p_false.
  rewrite -> (about_filter_in_and_concatenation_of_lists filter_in
                                                         S_filter_in
                                                         p (rev xs') (x :: nil)).
  rewrite -> IHxs'.
  rewrite ->3 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in
                                                              S_filter_in).
  unfold filter_in_v0.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p_false.
  rewrite -> unfold_filter_in_ds_bc.
  rewrite -> app_nil_r.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p_false.
  reflexivity.
Qed.

Theorem about_filter_out_and_reverse_list :
  forall (filter_out : (nat -> bool) -> list nat -> list nat),
    specification_of_filter_out filter_out ->
    forall (p : nat -> bool) (xs : list nat),
      filter_out p (rev xs) = rev (filter_out p xs).
Proof.
  intros filter_out S_filter_out.
  intros p xs.
  rewrite ->2 (any_filter_out_can_be_rewritten_to_filter_out_v1 filter_out
                                                               S_filter_out).
  unfold filter_out_v1.
  assert (S_filter_in_v0 := filter_in_v0_fits_the_specification_of_filter_in).
  apply (about_filter_in_and_reverse_list filter_in_v0
                                          S_filter_in_v0
                                          (fun n : nat => negb (p n))
                                          xs).
Qed.

(* end of filtering_lists.v *)
