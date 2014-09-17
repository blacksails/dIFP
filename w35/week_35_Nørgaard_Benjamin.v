(* week_35_exercises.v *)
(* dIFP 2014-2015, Q1 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* ********** *)

(*

The learning goals of this first lecture are as follows:

* Install Coq on each student's laptop.

* Preferably use Emacs with Proof General,
  because it scales better than CoqIde
  (tick "3 Windows mode layout" in the Coq top menu;
  use the hybrid mode if your screen is not wide enough).

* Understand the basic idea of stepping forward and backwards through
  a Coq file, either with the arrows "Next" and "Undo" in the tool bar,
  or C-c C-n and C-c C-u on the keyboard.

* Visualize that a proof is a tree, similarly to an abstract-syntax tree
  and a typing-derivation tree.  (About that, it would be a good idea
  to read
    http://users-cs.au.dk/danvy/dProgSprog/Lecture-notes/week-22.html
  again.)  When proving a theorem in Coq, we interactively construct
  its proof tree.

* Make formal statements:

    <formal-statement> ::= <keyword> <identifier> : <logical-formula>
             <keyword> ::= Lemma
                         | Theorem
                         | Corollary
          <identifier> ::= ...
     <logical-formula> ::= forall {<identifier>}+, <logical-expression>
  <logical-expression> ::= <identifier>
                         | <logical-expression> -> <logical-expression>
                         | <logical-expression> /\ <logical-expression>
                         | <logical-expression> \/ <logical-expression>

  where
    "A -> B" is an implication,
    "A /\ B" is a conjunction, and
    "A /\ B" is a disjunction.

* Syntactic sugar: "A <-> B" is the conjunction
    "(A -> B) /\ (B -> A)"

* Prove formal statements:

  <proof-script> ::= Proof.  {<coq-commands>}+  Qed.

  At the end of a proof, either write "Qed." to tell Coq that the
  proof script is complete, or write "Admitted." if you can prove it
  but you believe in your heart that it holds, or write "Abort." if
  you can prove it and you don't want to rely on it later in the file.

* Processing goals:

  When the goal is "forall x : blah1, blah2", write "intro x."
  to move x from your goal to your assumptions.

  When the goal is "A -> B", write "intro H_A."
  to declare the hypothesis about A in your assumptions.

  When the goal is "P" and you have an assumption about it, H_P,
  write "apply H_P.".

  Instead of writing "intro X.  intro Y.  intro Z."
  you can more concisely write "intros X Y Z.".

  Instead of writing "intro H_X.  intro H_Y.  intro H_Z."
  you can more concisely write "intros H_X H_Y H_Z.".

  When the goal is "A /\ B -> C", use Coq's pattern-matching facility
  and write "intros [H_A H_B]."
  to directly name the hypotheses about A and B.

  When the goal is "A \/ B -> C", use Coq's pattern-matching facility
  and write "intros [H_A | H_B]."
  to directly name the hypotheses about A and B.
  (This will create a subgoal.)

  When the goal is a conjunction, write "split.".
  (This will create a subgoal.)

  So in particular, when the goal is an equivalence "A <-> B",
  write "split.".

  When the goal is a disjunction, write "left." or "right."
  depending on which disjunct you want to prove.

* Apply lemmas or theorems that were already proved.

* Load a library of lemmas and theorems:

    Require Import Arith.

* Use an equality lemma to rewrite a formula
  (see comm_a et al. below).

* Use "reflexivity." and "symmetry.".

* Restart a proof.

* Simple convention about indentation:
  the number of indentations (two white spaces) matches the number of subgoals.

* Readability:
  don't hesitate to put empty lines in your proofs,
  to delineate conceptual blocks.

*)

(* ********** *)

(* Exercise 1:
   Prove that conjunction and disjunctions are associative.
*)

Theorem conjunction_is_associative_either_way :
  forall P1 P2 P3 : Prop,
    P1 /\ (P2 /\ P3) <-> (P1 /\ P2) /\ P3.
Proof.
  intros P1 P2 P3.
  split.
    (* -> *)
    intros [H_P1 [H_P2 H_P3]].
    split.
      split.
        apply H_P1.
      apply H_P2.
    apply H_P3.
  (* <- *)
  intros [[H_P1 H_P2] H_P3].
  split.
    apply H_P1.
  split.
    apply H_P2.
  apply H_P3.
Qed.

Theorem disjunction_is_associative_either_way :
  forall P1 P2 P3 : Prop,
    P1 \/ (P2 \/ P3) <-> (P1 \/ P2) \/ P3.
Proof.
  split.
    (* -> *)
    intros [H_P1 | [H_P2 | H_P3]].
        left. left. apply H_P1.
      left. right. apply H_P2.
    right. apply H_P3.
  (* <- *)
  intros [[H_P1 | H_P2] | H_P3].
      left. apply H_P1.
    right. left. apply H_P2.
  right. right. apply H_P3.
Qed.

(* ********** *)

(* Exercise 2:
   Prove that conjunction and disjunctions are commutative.
*)

Lemma conjunction_is_commutative :
  forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [H_P H_Q].
  split.
    apply H_Q.
  apply H_P.
Qed.

Lemma conjunction_is_commutative_either_way :
  forall P Q : Prop,
    P /\ Q <-> Q /\ P.
Proof.
  intros P Q.
  split.
    apply (conjunction_is_commutative).
  apply (conjunction_is_commutative).
Qed.

Lemma disjunction_is_commutative :
  forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q [H_P | H_Q].
    right. apply H_P.
  left. apply H_Q.
Qed.

Lemma disjunction_is_commutative_either_way :
  forall P Q : Prop,
    P \/ Q <-> Q \/ P.
Proof.
  intros P Q.
  split.
    apply (disjunction_is_commutative).
  apply (disjunction_is_commutative).
Qed.

(* ********** *)

(* Exercise 3:
   Prove the following lemma, Curry_and_unCurry.
*)

Lemma Curry_and_unCurry :
  forall P Q R : Prop,
    (P /\ Q -> R) <-> P -> Q -> R.
Proof.
  intros P Q R.
  split.
    intros H_P_con_Q_imp_R H_P H_Q.
    apply H_P_con_Q_imp_R.
    split.
      apply H_P.
    apply H_Q.
  intros H_P_imp_Q_imp_R [H_P H_Q].
  apply H_P_imp_Q_imp_R.
    apply H_P.
  apply H_Q.
Qed.

(* ********** *)

(* Here is how to import a Coq library about arithmetic expressions: *)

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

  Restart.

  intros a b c.
  rewrite -> (plus_comm (a + b) c).
  rewrite -> (plus_comm a b).
  reflexivity.

  Restart.

  intros a b c.
  rewrite -> (plus_comm c (b + a)).
  rewrite -> (plus_comm b a).
  reflexivity.

  Restart.

  intros a b c.
  rewrite <- (plus_comm (b + a) c).
  rewrite <- (plus_comm a b).
  reflexivity.

  Restart.

  intros a b c.
  rewrite <- (plus_comm a b).
  rewrite <- (plus_comm (a + b) c).
  reflexivity.

  Restart.

  intros a b c.
  rewrite -> (plus_comm a b).
  rewrite <- (plus_comm (b + a) c).
  reflexivity.

(* Qed. *)

(* Exercise 4:
   Add a couple more proofs for Lemma comm_a.

   For the over-achievers:
   How many distinct proofs are there for Lemma comm_a?
*)
  Restart.
  
  intros a b c.
  rewrite -> (plus_comm (a + b) c).
  rewrite -> (plus_comm b a).
  reflexivity.

  Restart.

  intros a b c.
  rewrite <- (plus_comm b a).
  rewrite <- (plus_comm (b + a) c).
  reflexivity.

Qed.

(* ********** *)

Lemma comm_b :
  forall x y z : nat,
    (x + y) + z = z + (y + x).
Proof.
  intros x y z.
  apply (comm_a x y z).

  Restart.

  apply comm_a.
Qed.

(* ********** *)

(* symmetry *)

Lemma comm_c :
  forall a b c : nat,
    c + (b + a) = (a + b) + c.
Proof.
  intros a b c.
  symmetry.
  apply (comm_a a b c).
Qed.

(* ********** *)

Check plus_assoc.

(*
plus_assoc
     : forall n m p : nat, n + (m + p) = n + m + p
*)

(* Exercise 5, for the over-achievers:
   find a couple of alternative proofs for the following lemma.
*)

Lemma assoc_a :
  forall a b c d : nat,
    a + (b + (c + d)) = ((a + b) + c) + d.
Proof.
  intros a b c d.
  rewrite -> (plus_assoc a b (c + d)).
  rewrite <- (plus_assoc (a + b) c d).
  reflexivity.

  Restart.

  intros a b c d.
  rewrite -> (plus_assoc a b (c + d)).
  rewrite -> (plus_assoc (a + b) c d).
  reflexivity.

  Restart.

  intros a b c d.
  rewrite <- (plus_assoc (a + b) c d).
  rewrite <- (plus_assoc a b (c + d)).
  reflexivity.

Qed.
(* You should replace "Abort." by a proof, if there is one. *)

(* ********** *)

(* Exercise 6:
   Prove the following lemma, mixed_a.
*)

Lemma mixed_a :
forall a b c d : nat,
    (c + (a + b)) + d = (b + (d + c)) + a.
Proof.
  intros a b c d.
  rewrite -> (plus_comm c (a + b)).
  rewrite -> (plus_comm d c).
  rewrite -> (plus_comm (b + (c + d)) a).
  symmetry. apply assoc_a.
Qed.

(* ********** *)

(* end of week_35_exercises.v *)
