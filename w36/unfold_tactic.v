(* unfold_tactic.v *)
(* dIFP 2014-2015, Q1 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

(* end of unfold_tactic.v *)
