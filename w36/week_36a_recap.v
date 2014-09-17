(* week_36a_recap.v *)
(* dIFP 2014-2015, Q1, Week 36 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(* Recap of the most basic Coq commands:

   When there is
     forall x, ...
   in the goal, in the top-right window,
   you should write
     intro x.
   in the left window.
   This will create one new hypothesis.

   When there is
     forall x y z, ...
   in the goal, in the top-right window,
   you can write
     intros x y z.
   in the left window.
   This will create three new hypotheses.

   When there is
     A -> ...
   in the goal, in the top-right window,
   you should write
     intro H_A.
   in the left window.
   This will create one new hypothesis.
 
   When there is
     A -> B -> C -> ...
   in the goal, in the top-right window,
   you can write
     intros H_A H_B H_C.
   in the left window.
   This will create three new hypotheses.
 
   When there is
     A /\ B -> ...
   in the goal, in the top-right window,
   you can write
     intro H_A_and_B.
   to create one new hypothesis,
   or you can write
     intros [H_A H_B].
   to create two new hypotheses.
 
   Conjunctions implicitly parenthesize to the right,
   so when there is
     P1 /\ (P2 /\ P3) -> P3.
   or
     P1 /\ P2 /\ P3 -> P3.
   in the goal, in the top-right window,
   you can write
     intros [H_P1 [H_P2 H_p3]].
   in the left window.
   This will create three new hypotheses.
   Of course you could also write
     intros [H_P1 | H_P2_and_P3].
   in the left window to create two new hypotheses.

   When there is
     A \/ B -> ...
   you can write
     intro H_A_or_B.
   to create one new hypothesis,
   or you can write
     intros [H_A | H_B].
   in the left window.
   This will create one new hypothesis and one new subgoal.
 
   Disjunctions implicitly parenthesize to the right,
   so when there is
     P1 \/ (P2 \/ P3) -> P3.
   or
     P1 \/ P2 \/ P3 -> P3.
   in the goal, in the top-right window,
   you can write
     intros [H_P1 | [H_P2 | H_p3]].
   in the left window.
   This will create one new hypothesis and two new subgoals.
   Of course you could also write
     intros [H_P1 | H_P2_or_P3].
   in the left window to create one new hypothesis
   and one new subgoal.

   When there is
     H_A_and_B : A /\ B
   in your hypotheses, in the top-right window,
   you can write
     destruct H_A_and_B as [H_A H_B].
   to replace the hypothesis about the conjunction
   by two hypotheses about the conjuncts.

   When there is
     H_A_and_B_and_C : A /\ B /\ C
   in your hypotheses, in the top-right window,
   you can write
     destruct H_A_and_B as [H_A [H_B H_C]].
   to replace the hypothesis about the conjunction
   by three hypotheses about the conjuncts.

   When there is
     H_A_or_B : A \/ B
   in your hypotheses, in the top-right window,
   you can write
     destruct H_A_or_B as [H_A | H_B].
   to replace the hypothesis about the disjunction
   by one hypothesis about the first disjunct.
   This will create a subgoal about the second disjunct.

   When there is
     H_A_or_B_or_C : A \/ B \/ C
   in your hypotheses, in the top-right window,
   you can write
     destruct H_A_or_B as [H_A | [H_B | H_C]].
   to replace the hypothesis about the disjunction
   by one hypothesis about the first disjunct.
   This will create two subgoals about the second and third disjunct.
*)

(* ********** *)

(* Applying lemmas and theorems and the creation of subgoals:

   Suppose we have C as a goal,
   and we have
     H_B_implies_C : B -> C
   among our hypotheses.
   Applying H_B_implies_C will replace the goal C
   by a new goal, B.

   Suppose we have C as a goal,
   and we have
     H_A_implies_B_implies_C : A -> B -> C
   among our hypotheses.
   Applying H_A_implies_B_implies_C will replace the goal C
   by a new goal, A, and will create a new subgoal, B.

   Example:
*)

Lemma for_the_sake_of_the_example :
  forall A B C : Prop,
    A -> B -> (A -> B -> C) -> (B -> C) -> C.
Proof.
  intros A B C.
  intros H_A H_B H_A_implies_B_implies_C H_B_implies_C.
  (* The goal is C. *)
  apply H_B_implies_C.
  (* The goal, C, is now replaced by a new goal, B. *)
  apply H_B.

  Restart.  

  intros A B C.
  intros H_A H_B H_A_implies_B_implies_C H_B_implies_C.
  (* The goal is C. *)
  apply H_A_implies_B_implies_C.
  (* The goal, C, is now replaced by a new goal, A,
     and there is a new subgoal, B. *)
    apply H_A.
  apply H_B.  
Qed.

(* ********** *)

(* Recap about applying lemmas and theorems:

   Given a lemma
     Lemma foo :
       forall x y z, ...
   we can apply foo to 0, 1, 2, or 3 arguments.

   Example:
*)

Lemma conjunction_is_commutative_one_way :
  forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q.
  intros [H_P H_Q].
  split.
    apply H_Q.
  apply H_P.
Qed.

Lemma conjunction_is_commutative_two_ways :
  forall P Q : Prop,
    P /\ Q <-> Q /\ P.
Proof.
  intros P Q.
  split.
    apply (conjunction_is_commutative_one_way P Q).
  apply (conjunction_is_commutative_one_way Q P).
Qed.

Require Import Arith.

Check plus_comm.
(*
plus_comm
     : forall n m : nat, n + m = m + n
*)

Lemma comm_a :
  forall a b c : nat,
    (a + b) + c = c + (b + a).
Proof.
  intros a b c.
  rewrite -> (plus_comm a b).
  rewrite -> (plus_comm (b + a) c).
  reflexivity.
Qed.

Lemma comm_b :
  forall x y z : nat,
    (x + y) + z = z + (y + x).
Proof.
  intros x y z.
  Check (comm_a x y z).
  Check (comm_a x y).
  Check (comm_a x).
  Check comm_a.

  Restart.

  intros x y z.
  apply (comm_a x y z).

  Restart.

  intros x y.
  apply (comm_a x y).

  Restart.

  intros x.
  apply (comm_a x).

  Restart.

  apply comm_a.
Qed.

(* ********** *)

(* Recap about applying lemmas and theorems:

   Given a lemma
     Lemma foo :
       forall A B C, A -> ...
   we can apply foo to 0, 1, 2, 3, or 4 arguments.

   Example:
*)

Lemma conjunction_is_commutative_one_way_alt :
  forall A B C: Prop,
    A -> B /\ C -> C /\ B.
Proof.
  intros A B C.
  intros H_A [H_B H_C].
  split.
    apply H_C.
  apply H_B.

  Restart.

  intros A B C.
  intros H_A.
  apply (conjunction_is_commutative_one_way B C).

  Restart.

  intros A B C H_A.
  revert C.  (* the converse of intro (new) *)
  revert B.
  apply conjunction_is_commutative_one_way.
  Restart.

  intros A B C H_A.
  revert B C.  (* both at once *)
  apply conjunction_is_commutative_one_way.
Qed.

Lemma conjunction_is_commutative_two_ways_alt :
  forall A B C: Prop,
    A -> (B /\ C <-> C /\ B).
Proof.
  intros A B C H_A.
  split.
    apply (conjunction_is_commutative_one_way B C).
  apply (conjunction_is_commutative_one_way C B).

  Restart.

  intros A B C H_A.
  revert C.
  revert B.
  apply conjunction_is_commutative_two_ways.
Qed.

(* ********** *)

(* end week_36a_recap.v *)
