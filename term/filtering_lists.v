(* filtering_lists.v *)
(* dIFP 2014-2015, Q1 *)
(* Teacher: Olivier Danvy <danvy@cs.au.dk> *)

(* Student name: ... *)
(* Student number: ... *)

(* ********** *)

(* The goal of this project is to study
   how to filter elements in or out of lists.
*)

Require Import List Bool unfold_tactic.

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

Require Import Arith NPeano.

Definition beq_nat_list (l1 l2 : list nat) :=
  beq_list nat l1 l2 beq_nat.

Notation "A =l= B" := (beq_nat_list A B) (at level 70, right associativity).

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
    forall (filter : (nat -> bool)) (l : list nat),
      f filter l = g filter l.
Proof.
  intros f g.
  intros S_f S_g.
  unfold specification_of_filter_in in S_f.
  destruct S_f as [H_f_nil [H_f_true H_f_false]]. 
  unfold specification_of_filter_in in S_g.
  destruct S_g as [H_g_nil [H_g_true H_g_false]].
  intros filter l.
  induction l as [ | x xs IHxs ].
    rewrite -> H_f_nil.
    rewrite -> H_g_nil.
    reflexivity.
  destruct (filter x) as [ | ] eqn:H_filter.
    assert (H_f_filter_true := H_filter).
    rename H_filter into H_g_filter_true.
    apply (H_f_true filter x xs) in H_f_filter_true.
    apply (H_g_true filter x xs) in H_g_filter_true.
    rewrite -> H_f_filter_true.
    rewrite -> H_g_filter_true.
    rewrite -> IHxs.
    reflexivity.
  assert (H_f_filter_false := H_filter).
  rename H_filter into H_g_filter_false.
  apply (H_f_false filter x xs) in H_f_filter_false.
  apply (H_g_false filter x xs) in H_g_filter_false.
  rewrite -> H_f_filter_false.
  rewrite -> H_g_filter_false.
  rewrite -> IHxs.
  reflexivity.
Qed.

Fixpoint filter_in_ds (filter : nat -> bool) (nats : list nat) :=
  match nats with
  | nil => nil
  | n :: nats' => 
      match filter n with
      | true => n :: filter_in_ds filter nats'
      | false => filter_in_ds filter nats'
      end
  end.

Definition filter_in_v0 (filter : nat -> bool) (nats : list nat) :=
  filter_in_ds filter nats.

Compute unit_test_for_filter_in filter_in_v0.

Lemma unfold_filter_in_ds_bc :
  forall (filter : nat -> bool),
    filter_in_ds filter nil = nil.
Proof.
  unfold_tactic filter_in_ds.
Qed.

Lemma unfold_filter_in_ds_ic :
  forall (filter : nat -> bool) (n : nat) (nats : list nat),
    filter_in_ds filter (n :: nats) = 
      match filter n with
      | true => n :: filter_in_ds filter nats 
      | false => filter_in_ds filter nats
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
    exact (unfold_filter_in_ds_bc p).
  split.
    intros p x xs'.
    intros H_filter_true.
    unfold filter_in_v0.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_filter_true.
    reflexivity.
  intros p x xs'.
  intros H_filter_false.
  unfold filter_in_v0.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_filter_false.
  reflexivity.
Qed.

Lemma any_filter_in_can_be_rewritten_to_filter_in_v0 :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall (filter : nat -> bool) (nats : list nat),
      filter_in filter nats = filter_in_v0 filter nats.
Proof.
  intros filter_in S_filter_in.
  intros filter nats.
  rewrite -> (there_is_only_one_filter_in filter_in 
                                          filter_in_v0 
                                          S_filter_in 
                                          filter_in_v0_fits_the_specification_of_filter_in).
  reflexivity.
Qed.

Theorem about_filtering_in_all_of_the_elements :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall ns : list nat,
      filter_in (fun _ => true) ns = ns.
Proof.
  intro filter_in.
  intro S_filter_in.
  intro ns.
  rewrite -> (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in S_filter_in).
  induction ns as [ | n ns' IHns'].
    unfold filter_in_v0.
    rewrite unfold_filter_in_ds_bc.
    reflexivity.
  unfold filter_in_v0.
  rewrite unfold_filter_in_ds_ic.
  unfold filter_in_v0 in IHns'.
  rewrite -> IHns'.
  reflexivity.
Qed.

Theorem about_filtering_in_none_of_the_elements :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall ns : list nat,
      filter_in (fun _ => false) ns = nil.
Proof.
  intro filter_in.
  intro S_filter_in.
  intro ns.
  rewrite -> (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in S_filter_in).
  induction ns as [ | n ns' IHns'].
    unfold filter_in_v0.
    rewrite unfold_filter_in_ds_bc.
    reflexivity.
  unfold filter_in_v0.
  rewrite unfold_filter_in_ds_ic.
  unfold filter_in_v0 in IHns'.
  rewrite -> IHns'.
  reflexivity.
Qed.

Theorem about_filtering_in_incrementally :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    forall (p1 p2 : nat -> bool)
           (ns : list nat),
      filter_in p2 (filter_in p1 ns) =
      filter_in (fun x => andb (p1 x) (p2 x)) ns.
Proof.
  intro filter_in.
  intro S_filter_in.
  intros p1 p2 ns.
  rewrite ->3 (any_filter_in_can_be_rewritten_to_filter_in_v0 filter_in S_filter_in).
  unfold filter_in_v0.
  induction ns as [ | n ns' IHns' ].
    rewrite -> (unfold_filter_in_ds_bc p1).
    rewrite -> (unfold_filter_in_ds_bc p2).
    rewrite -> unfold_filter_in_ds_bc.
    reflexivity.
  destruct (p1 n) as [ | ] eqn:H_p1.
  destruct (p2 n) as [ | ] eqn:H_p2.
      rewrite -> unfold_filter_in_ds_ic.
      rewrite -> H_p1.
      rewrite -> unfold_filter_in_ds_ic.
      rewrite -> H_p2.
      rewrite -> IHns'.
      rewrite -> unfold_filter_in_ds_ic.
      rewrite -> H_p1.
      rewrite -> andb_true_l.
      rewrite -> H_p2.
      reflexivity.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p1.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p2.
    rewrite -> IHns'.
    rewrite -> unfold_filter_in_ds_ic.
    rewrite -> H_p1.
    rewrite -> andb_true_l.
    rewrite -> H_p2.
    reflexivity.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p1.
  rewrite -> unfold_filter_in_ds_ic.
  rewrite -> H_p1.
  rewrite -> andb_false_l.
  rewrite -> IHns'.
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
    forall (filter : (nat -> bool)) (nats : list nat),
      f filter nats = g filter nats.
Proof.
  intros f g S_f S_g.
  unfold specification_of_filter_out in S_f.
  destruct S_f as [H_f_nil [H_f_true H_f_false]].
  unfold specification_of_filter_out in S_g.
  destruct S_g as [H_g_nil [H_g_true H_g_false]].
  intros filter nats.
  induction nats as [ | n nats' IHnats' ].
    rewrite -> H_f_nil.
    rewrite -> H_g_nil.
    reflexivity.
  destruct (filter n) as [ | ] eqn:H_f_filter_true.
    assert (H_g_filter_true := H_f_filter_true).
    apply (H_f_true filter n nats') in H_f_filter_true.
    apply (H_g_true filter n nats') in H_g_filter_true.
    rewrite -> H_f_filter_true.
    rewrite -> H_g_filter_true.
    rewrite -> IHnats'.
    reflexivity.
  rename H_f_filter_true into H_f_filter_false.
  assert (H_g_filter_false := H_f_filter_false).
  apply (H_f_false filter n nats') in H_f_filter_false.
  apply (H_g_false filter n nats') in H_g_filter_false.
  rewrite -> H_f_filter_false.
  rewrite -> H_g_filter_false.
  rewrite -> IHnats'.
  reflexivity.
Qed.

Proposition filter_out_from_filter_in :
  forall filter_in : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_in filter_in ->
    specification_of_filter_out (fun p ns => filter_in (fun x => negb (p x)) ns).
Proof.
Abort.

Proposition filter_in_from_filter_out :
  forall filter_out : (nat -> bool) -> list nat -> list nat,
    specification_of_filter_out filter_out ->
    specification_of_filter_in (fun p ns => filter_out (fun x => negb (p x)) ns).
Proof.
Abort.

(* Which consequences of these propositions can you think of? *)

(* ********** *)

(* What is the result

   * of applying filter_in to the concatenation of two lists?

   * of applying filter_out to the concatenation of two lists?

   * of applying filter_in to a reversed list?

   * of applying filter_out to a reversed list?
*)

(* ********** *)

(* end of filtering_lists.v *)
