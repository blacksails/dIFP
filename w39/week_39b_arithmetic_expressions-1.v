(* week_39b_arithmetic_expressions.v *)
(* dIFP 2014-2015, Q1, Week 38 *)
(* Olivier Danvy <danvy@cs.au.dk> *)

(* Working version, make sure to download
   the updated version after class.
*)

(* ********** *)

Require Import Arith Bool List unfold_tactic.

(* ********** *)

(* Source syntax: *)

Inductive arithmetic_expression : Type :=
  | Lit : nat -> arithmetic_expression
  | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
  | Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Exercise 0:
   Write samples of arithmetic expressions.
*)

Definition ae_0 :=
  Lit 5.

Definition ae_1 :=
  Plus (Lit 2) (Lit 3).

Definition ae_2 :=
  Times (Plus (Lit 1) (Lit 2))
        (Lit 2).

(* ********** *)

Definition specification_of_interpret (interpret : arithmetic_expression -> nat) :=
  (forall n : nat,
     interpret (Lit n) = n)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Plus ae1 ae2) = (interpret ae1) + (interpret ae2))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     interpret (Times ae1 ae2) = (interpret ae1) * (interpret ae2)).

(* Exercise 1:
   Write unit tests.
*)

Definition unit_test_for_interpret (interpret : arithmetic_expression -> nat) :=
  (beq_nat (interpret ae_0) 5)
  &&
  (beq_nat (interpret ae_1) 5)
  &&
  (beq_nat (interpret ae_2) 6)
  &&
  (beq_nat (interpret (Times ae_1 ae_2)) 30).

(* Exercise 2:
   Define an interpreter as a function
   that satisfies the specification above
   and verify that it passes the unit tests.
*)

Theorem there_is_only_one_interpret :
  forall (f g : arithmetic_expression -> nat),
    specification_of_interpret f ->
    specification_of_interpret g ->
    forall (ae : arithmetic_expression),
      f ae = g ae.
Proof.
  intros f g.
  unfold specification_of_interpret.
  intros [H_f_lit [H_f_plus H_f_times]] [H_g_lit [H_g_plus H_g_times]].
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1' IHae1' ae2' IHae2' ].
      rewrite -> H_f_lit.
      rewrite -> H_g_lit.
      reflexivity.
    rewrite -> H_f_plus.
    rewrite -> H_g_plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  rewrite -> H_f_times.
  rewrite -> H_g_times.
  rewrite -> IHae1'.
  rewrite -> IHae2'.
  reflexivity.
Qed.

Fixpoint interpret_ds (ae : arithmetic_expression) :=
  match ae with
  | Lit n => n
  | Plus ae1 ae2 => interpret_ds ae1 + interpret_ds ae2
  | Times ae1 ae2 => interpret_ds ae1 * interpret_ds ae2
  end.

Definition interpret (ae : arithmetic_expression) :=
  interpret_ds ae.

Compute unit_test_for_interpret interpret.

Lemma unfold_interpret_ds_lit :
  forall n : nat,
    interpret_ds (Lit n) = n.
Proof.
  unfold_tactic interpret_ds.
Qed.

Lemma unfold_interpret_ds_plus :
  forall ae1 ae2 : arithmetic_expression,
    interpret_ds (Plus ae1 ae2) = interpret_ds ae1 + interpret_ds ae2.
Proof.
  unfold_tactic interpret_ds.
Qed.

Lemma unfold_interpret_ds_times :
  forall ae1 ae2 : arithmetic_expression,
    interpret_ds (Times ae1 ae2) = interpret_ds ae1 * interpret_ds ae2.
Proof.
  unfold_tactic interpret_ds.
Qed.

Proposition interpret_fits_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret.
  split.
    exact unfold_interpret_ds_lit.
  split.
    exact unfold_interpret_ds_plus.
  exact unfold_interpret_ds_times.
Qed.

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | MUL : byte_code_instruction.

(* ********** *)

(* Byte-code programs: *)

Definition byte_code_program := list byte_code_instruction.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

(* Exercise 3:
   specify a function
     execute_byte_code_instruction : instr -> data_stack -> data_stack
   that executes a byte-code instruction, given a data stack
   and returns this stack after the instruction is executed.

   * Executing (PUSH n) given s has the effect of pushing n on s.

   * Executing ADD given s has the effect of popping two numbers
     from s and then pushing the result of adding them.

   * Executing MUL given s has the effect of popping two numbers
     from s and then pushing the result of multiplying them.

   For now, if the stack underflows, just assume it contains zeroes.
*)

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

Definition beq_nat_list (l1 l2 : list nat) :=
  beq_list nat l1 l2 beq_nat.

Definition s_0 : list nat :=
  nil.
Definition s_1 :=
  2 :: nil.
Definition s_2 :=
  2 :: 3 :: nil.

Compute beq_nat_list s_0 s_0. (* true *)
Compute beq_nat_list s_1 s_1. (* true *)
Compute beq_nat_list s_2 s_2. (* true *)
Compute beq_nat_list s_1 s_2. (* false *)

Definition unit_test_for_execute_byte_code_instruction (exec : byte_code_instruction -> data_stack -> data_stack) :=
  (* Test for push *)
  (beq_nat_list (exec (PUSH 2) s_1)
                (2 :: 2 :: nil))
  &&
  (* Test for add *)
  (beq_nat_list (exec ADD s_0) 
                (0 :: nil))
  &&
  (beq_nat_list (exec ADD s_1)
                s_1)
  &&
  (beq_nat_list (exec ADD s_2)
                (5 :: nil))
  &&
  (* Test for mul *)
  (beq_nat_list (exec MUL s_0)
                (0 :: nil))
  &&
  (beq_nat_list (exec MUL s_1)
                (0 :: nil))
  &&
  (beq_nat_list (exec MUL s_2)
                (6 :: nil)).

Definition specification_of_execute_byte_code_instruction (exec : byte_code_instruction -> data_stack -> data_stack) :=
  (forall (n : nat) (s : data_stack),
    exec (PUSH n) s = n :: s)
  /\
  (forall (s : data_stack),
    exec ADD s = match s with
                 | nil => 0 :: nil
                 | n :: nil => n :: nil
                 | n :: n' :: s' => n + n' :: s'
                 end)
  /\
  (forall (s : data_stack),
    exec MUL s = match s with
                 | nil => 0 :: nil
                 | n :: nil => 0 :: nil
                 | n :: n' :: s' => n * n' :: s'
                 end).

Theorem there_is_only_one_execute_byte_code_instruction :
  forall (f g : byte_code_instruction -> data_stack -> data_stack),
    specification_of_execute_byte_code_instruction f ->
    specification_of_execute_byte_code_instruction g ->
    forall (instr : byte_code_instruction) (s : data_stack),
      f instr s = g instr s.
Proof.
  intros f g.
  unfold specification_of_execute_byte_code_instruction.
  intros [H_f_push [H_f_add H_f_mul]].
  intros [H_g_push [H_g_add H_g_mul]].
  intros instr s.
  case instr as [ n | | ].
      rewrite -> H_f_push.
      rewrite -> H_g_push.
      reflexivity.
    rewrite -> H_f_add.
    rewrite -> H_g_add.
    reflexivity.
  rewrite -> H_f_mul.
  rewrite -> H_g_mul.
  reflexivity.
Qed.

Definition execute_byte_code_instruction (instr : byte_code_instruction) (s : data_stack) :=
  match instr with
  | PUSH n => n :: s
  | ADD =>
      match s with
      | nil => 0 :: nil
      | n :: nil => n :: nil
      | n :: n' :: s' => n + n' :: s'
      end
  | MUL =>
      match s with
      | nil => 0 :: nil
      | n :: nil => 0 :: nil
      | n :: n' :: s' => n * n' :: s'
      end
  end.

Compute unit_test_for_execute_byte_code_instruction execute_byte_code_instruction.

Theorem execute_byte_code_instruction_fits_the_specification :
  specification_of_execute_byte_code_instruction execute_byte_code_instruction.
Proof.
  unfold specification_of_execute_byte_code_instruction.
  unfold execute_byte_code_instruction.
  split.
    intros n s.
    reflexivity.
  split.
    intro s.
    reflexivity.
  intro s.
  reflexivity.
Qed.

(* ********** *)

(* Exercise 4:
   Define a function
     execute_byte_code_program : byte_code_program -> data_stack -> data_stack
   that executes a given byte-code program on a given data stack,
   and returns this stack after the program is executed.
*)

Definition p_0 :=
  ADD :: nil.
Definition p_1 :=
  ADD :: ADD :: nil.
Definition p_2 :=
  ADD :: MUL :: nil.

Definition unit_test_for_execute_byte_code_program (exec_prog : byte_code_program -> data_stack -> data_stack) :=
  (beq_nat_list (exec_prog p_0 nil)
                (0 :: nil))
  &&
  (beq_nat_list (exec_prog p_0 s_2)
                (5 :: nil))
  &&
  (beq_nat_list (exec_prog p_1 (s_1 ++ s_2))
                (7 :: nil))
  &&
  (beq_nat_list (exec_prog p_2 (s_1 ++ s_2))
                (12 :: nil)).

Definition specification_of_execute_byte_code_program (exec_prog : byte_code_program -> data_stack -> data_stack) :=
  (forall s : data_stack,
    exec_prog nil s = s)
  /\
  (forall (instr : byte_code_instruction) (prog : byte_code_program) (s : data_stack),
    exec_prog (instr :: prog) s = exec_prog prog (execute_byte_code_instruction instr s)).

Theorem there_is_only_one_execute_byte_code_program :
  forall (f g : byte_code_program -> data_stack -> data_stack),
    specification_of_execute_byte_code_program f ->
    specification_of_execute_byte_code_program g ->
    forall (prog : byte_code_program) (s : data_stack),
      f prog s = g prog s.
Proof.
  intros f g.
  unfold specification_of_execute_byte_code_program.
  intros [H_f_bc H_f_ic] [H_g_bc H_g_ic].

  intros prog.
  induction prog as [ | x xs IHx ].

  intro s.
  rewrite -> H_f_bc.
  rewrite -> H_g_bc.
  reflexivity.

  intro s.
  rewrite -> H_f_ic.
  rewrite -> H_g_ic.
  rewrite -> IHx.
  reflexivity.
Qed.

Fixpoint execute_byte_code_program (prog : byte_code_program) (s : data_stack) :=
  match prog with
  | nil => s
  | instr :: prog => execute_byte_code_program prog (execute_byte_code_instruction instr s)
  end.

Compute unit_test_for_execute_byte_code_program execute_byte_code_program.

Lemma unfold_execute_byte_code_program_bc :
  forall s : data_stack,
    execute_byte_code_program nil s = s.
Proof.
  unfold_tactic execute_byte_code_program.
Qed.

Lemma unfold_execute_byte_code_program_ic :
  forall (instr : byte_code_instruction) (prog : byte_code_program) (s : data_stack),
    execute_byte_code_program (instr :: prog) s = execute_byte_code_program prog (execute_byte_code_instruction instr s).
Proof.
  unfold_tactic execute_byte_code_program.
Qed.

Theorem execute_byte_code_program_fits_the_specification :
  specification_of_execute_byte_code_program execute_byte_code_program.
Proof.
  unfold specification_of_execute_byte_code_program.
  split.
    exact unfold_execute_byte_code_program_bc.
  exact unfold_execute_byte_code_program_ic.
Qed.

(* ********** *)

(* Exercise 5:
   Prove that for all programs p1, p2 and data stacks s,
   executing (p1 ++ p2) with s
   gives the same result as
   (1) executing p1 with s, and then
   (2) executing p2 with the resulting stack.
*)

Lemma unfold_append_bc :
  forall (bcis : list byte_code_instruction),
    nil ++ bcis = bcis.
Proof.
  apply app_nil_l.
Qed.

Lemma unfold_append_ic :
  forall (bci1 : byte_code_instruction) (bci1s' bci2s : list byte_code_instruction),
    (bci1 :: bci1s') ++ bci2s = bci1 :: (bci1s' ++ bci2s).
Proof.
  intros bci1 bci1s' bci2s.
  symmetry.
  apply app_comm_cons.
Qed.

Lemma about_execute_byte_code_program :
  forall (p1 p2 : byte_code_program) (s : data_stack),
    execute_byte_code_program (p1 ++ p2) s = execute_byte_code_program p2 (execute_byte_code_program p1 s).
Proof.
  intro p1.
  induction p1 as [ | instr prog IHprog ].
    intros p2 s.
    rewrite -> unfold_append_bc.
    rewrite -> unfold_execute_byte_code_program_bc.
    reflexivity.
  intros p2 s.
  rewrite -> unfold_append_ic.
  rewrite ->2 unfold_execute_byte_code_program_ic.
  rewrite -> IHprog.
  reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile (compile : arithmetic_expression -> byte_code_program) :=
  (forall n : nat,
     compile (Lit n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Plus ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile (Times ae1 ae2) = (compile ae1) ++ (compile ae2) ++ (MUL :: nil)).

(* Exercise 6:
   Define a compiler as a function
   that satisfies the specification above
   and uses list concatenation, i.e., ++.
*)

Definition beq_instr (i1 i2 : byte_code_instruction) :=
  match i1 with
  | PUSH n1 =>
      match i2 with
      | PUSH n2 => beq_nat n1 n2
      | _ => false
      end
  | ADD =>
      match i2 with
      | ADD => true
      | _ => false
      end
  | MUL =>
      match i2 with
      | MUL => true
      | _ => false
      end
  end.

Compute beq_instr (PUSH 2) (PUSH 2). (* true *)
Compute beq_instr (PUSH 2) (PUSH 3). (* false *)
Compute beq_instr ADD ADD.           (* true *)
Compute beq_instr MUL ADD.           (* false *) 

Definition beq_instr_list (p1 p2 : byte_code_program) :=
  beq_list byte_code_instruction p1 p2 beq_instr.

Compute beq_instr_list p_0 p_0. (* true *)
Compute beq_instr_list p_1 p_1. (* true *)
Compute beq_instr_list p_2 p_2. (* true *)
Compute beq_instr_list p_1 p_2. (* false *)

Definition unit_test_for_compile (compile : arithmetic_expression -> byte_code_program) :=
  (beq_instr_list (compile ae_0)
                  (PUSH 5 :: nil))
  &&
  (beq_instr_list (compile ae_1)
                  (PUSH 2 :: PUSH 3 :: ADD :: nil))
  &&
  (beq_instr_list (compile ae_2)
                  (PUSH 1 :: PUSH 2 :: ADD :: PUSH 2 :: MUL :: nil)).

Theorem there_is_only_one_compile :
  forall (f g : arithmetic_expression -> byte_code_program),
    specification_of_compile f ->
    specification_of_compile g ->
    forall (ae : arithmetic_expression),
      f ae = g ae.
Proof.
  intros f g.
  unfold specification_of_compile.
  intros [Hf_lit [Hf_plus Hf_times]].
  intros [Hg_lit [Hg_plus Hg_times]].
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1' IHae1' ae2' IHae2' ].
      rewrite -> Hf_lit.
      rewrite -> Hg_lit.
      reflexivity.
    rewrite -> Hf_plus.
    rewrite -> Hg_plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  rewrite -> Hf_times.
  rewrite -> Hg_times.
  rewrite -> IHae1'.
  rewrite -> IHae2'.
  reflexivity.
Qed.

Fixpoint compile_ds (ae : arithmetic_expression) :=
  match ae with
  | Lit n => PUSH n :: nil
  | Plus ae1 ae2 => (compile_ds ae1) ++ (compile_ds ae2) ++ (ADD :: nil)
  | Times ae1 ae2 => (compile_ds ae1) ++ (compile_ds ae2) ++ (MUL :: nil)
  end.

Definition compile_v0 (ae : arithmetic_expression) :=
  compile_ds ae.

Compute unit_test_for_compile compile_v0.

Lemma unfold_compile_ds_lit :
  forall n : nat,
    compile_ds (Lit n) = PUSH n :: nil.
Proof.
  unfold_tactic compile_ds.
Qed.

Lemma unfold_compile_ds_plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ds (Plus ae1 ae2) = (compile_ds ae1) ++ (compile_ds ae2) ++ (ADD :: nil).
Proof.
  unfold_tactic compile_ds.
Qed.

Lemma unfold_compile_ds_times :
  forall (ae1 ae2 : arithmetic_expression),
    compile_ds (Times ae1 ae2) = (compile_ds ae1) ++ (compile_ds ae2) ++ (MUL :: nil).
Proof.
  unfold_tactic compile_ds.
Qed.

Theorem compile_v0_fits_the_specification_of_compile :
  specification_of_compile compile_v0.
Proof.
  unfold specification_of_compile.
  split.
    exact unfold_compile_ds_lit.
  split.
    exact unfold_compile_ds_plus.
  exact unfold_compile_ds_times.
Qed.

(* Exercise 7:
   Write a compiler as a function with an accumulator
   that does not use ++ but :: instead,
   and prove it equivalent to the compiler of Exercise 6.
*)

Fixpoint compile_acc (ae : arithmetic_expression) (prog : byte_code_program) :=
  match ae with
  | Lit n => PUSH n :: prog
  | Plus ae1 ae2 => compile_acc ae1 (compile_acc ae2 (ADD :: prog))
  | Times ae1 ae2 => compile_acc ae1 (compile_acc ae2 (MUL :: prog))
  end.

Definition compile_v1 (ae : arithmetic_expression) :=
  compile_acc ae nil.

Compute unit_test_for_compile compile_v1.

Lemma unfold_compile_acc_lit :
  forall (n : nat) (prog : byte_code_program),
    compile_acc (Lit n) prog = PUSH n :: prog.
Proof.
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_plus :
  forall (ae1 ae2 : arithmetic_expression) (prog : byte_code_program),
    compile_acc (Plus ae1 ae2) prog = compile_acc ae1 (compile_acc ae2 (ADD :: prog)).
Proof.
  unfold_tactic compile_acc.
Qed.

Lemma unfold_compile_acc_times :
  forall (ae1 ae2 : arithmetic_expression) (prog : byte_code_program),
    compile_acc (Times ae1 ae2) prog = compile_acc ae1 (compile_acc ae2 (MUL :: prog)).
Proof.
  unfold_tactic compile_acc.
Qed.

Lemma about_compile_acc :
  forall (ae : arithmetic_expression) (prog : byte_code_program),
    compile_acc ae prog = compile_acc ae nil ++ prog.
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1' IHae1' ae2' IHae2' ].
      intro prog.
      rewrite ->2 unfold_compile_acc_lit.
      rewrite -> unfold_append_ic.
      rewrite -> unfold_append_bc.
      reflexivity.
    intro prog.
    rewrite ->2 unfold_compile_acc_plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    rewrite -> (IHae1 (compile_acc ae2 (ADD :: nil))).
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite ->2 app_assoc_reverse.
    rewrite -> unfold_append_ic.
    rewrite -> unfold_append_bc.
    reflexivity.
  intro prog.
  rewrite ->2 unfold_compile_acc_times.
  rewrite -> IHae1'.
  rewrite -> IHae2'.
  rewrite -> (IHae1' (compile_acc ae2' (MUL :: nil))).
  rewrite -> (IHae2' (MUL :: nil)).
  rewrite ->2 app_assoc_reverse.
  rewrite -> unfold_append_ic.
  rewrite -> unfold_append_bc.
  reflexivity.
Qed.

Theorem compile_v1_fits_the_specification_of_compile :
  specification_of_compile compile_v1.
Proof.
  unfold specification_of_compile.
  unfold compile_v1.
  split.
    intro n.
    apply unfold_compile_acc_lit.
  split.
    intros ae1 ae2.
    rewrite -> unfold_compile_acc_plus.
    rewrite -> about_compile_acc.
    rewrite -> (about_compile_acc ae2 (ADD :: nil)).
    reflexivity.
  intros ae1 ae2.
  rewrite -> unfold_compile_acc_times.
  rewrite -> about_compile_acc.
  rewrite -> (about_compile_acc ae2 (MUL :: nil)).
  reflexivity.
Qed.

Proposition compile_v0_and_compile_v1_are_equivalent :
  forall ae : arithmetic_expression,
    compile_v0 ae = compile_v1 ae.
Proof.
  apply there_is_only_one_compile.
    exact compile_v0_fits_the_specification_of_compile.
  exact compile_v1_fits_the_specification_of_compile.
Qed.

(* ********** *)

(* Exercise 8:
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program
   over an empty data stack.
*)

Definition unit_test_for_run (run : byte_code_program -> nat) :=
  (beq_nat (run (PUSH 5 :: nil))
           5)
  &&
  (beq_nat (run (PUSH 1 :: PUSH 2 :: ADD :: nil))
           3)
  &&
  (beq_nat (run (PUSH 1 :: PUSH 2 :: MUL :: nil))
           2)
  &&
  (beq_nat (run (nil))
           0)
  &&
  (beq_nat (run (PUSH 1 :: MUL :: nil))
           0)
  &&
  (beq_nat (run (PUSH 1 :: ADD :: nil))
           1)
  &&
  (beq_nat (run (ADD :: MUL :: nil))
           0).

Definition specification_of_run (run : byte_code_program -> nat) :=
  forall prog : byte_code_program,
    run prog = 
      match execute_byte_code_program prog nil with
      | result :: nil => result
      | _ => 0
      end.

Theorem there_is_only_one_run :
  forall (f g : byte_code_program -> nat),
    specification_of_run f ->
    specification_of_run g ->
    forall prog : byte_code_program,
      f prog = g prog.
Proof.
  intros f g.
  unfold specification_of_run.
  intros S_f S_g.
  intro prog.
  rewrite -> S_f.
  rewrite -> S_g.
  reflexivity.
Qed.

Definition run (prog : byte_code_program) :=
  match execute_byte_code_program prog nil with
  | result :: nil => result
  | _ => 0
  end.

Compute unit_test_for_run run.

Lemma interpret_exp_cons_datastack_eq_execute_compile_exp_ds :
  forall (ae : arithmetic_expression) (s : data_stack),
    interpret ae :: s = execute_byte_code_program (compile_v0 ae) s.
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1' IHae1' ae2' IHae2' ].
      intro s.
      rewrite -> unfold_interpret_ds_lit.
      rewrite -> unfold_compile_ds_lit.
      rewrite -> unfold_execute_byte_code_program_ic.
      rewrite -> unfold_execute_byte_code_program_bc.
      unfold execute_byte_code_instruction.
      reflexivity.
    intro s.
    unfold interpret.
    rewrite -> unfold_interpret_ds_plus.
    unfold compile_v0.
    rewrite -> unfold_compile_ds_plus.
    rewrite ->2 about_execute_byte_code_program.
    rewrite -> unfold_execute_byte_code_program_ic.
    rewrite -> unfold_execute_byte_code_program_bc.
    rewrite <- IHae1.
    rewrite <- IHae2.
    unfold execute_byte_code_instruction.
    rewrite -> plus_comm.
    reflexivity.
  intro s.
  unfold interpret.
  rewrite -> unfold_interpret_ds_times.
  unfold compile_v0.
  rewrite -> unfold_compile_ds_times.
  rewrite ->2 about_execute_byte_code_program.
  rewrite -> unfold_execute_byte_code_program_ic.
  rewrite -> unfold_execute_byte_code_program_bc.
  rewrite <- IHae1'.
  rewrite <- IHae2'.
  unfold execute_byte_code_instruction.
  rewrite -> mult_comm.
  reflexivity.
Qed.

Theorem interpret_yields_same_result_as_compile_then_execute :
  forall ae : arithmetic_expression,
    interpret ae = run (compile_v0 ae).
Proof.
  intro ae.
  unfold run.
  unfold compile_v0.
  rewrite <- interpret_exp_cons_datastack_eq_execute_compile_exp_ds.
  reflexivity.
Qed.

(* ********** *)

(* Exercise 9:
   Write a Magritte-style execution function for a byte-code program
   that does not operate on natural numbers but on syntactic representations
   of natural numbers:

   Definition data_stack := list arithmetic_expression.

   * Executing (PUSH n) given s has the effect of pushing (Lit n) on s.

   * Executing ADD given s has the effect of popping two arithmetic
     expressions from s and then pushing the syntactic representation of
     their addition.

   * Executing MUL given s has the effect of popping two arithmetic
     expressions from s and then pushing the syntactic representation of
     their multiplication.

   Again, for this week's exercise,
   assume there are enough arithmetic expressions on the data stack.
   If that is not the case, just pad it up with syntactic representations
   of zero.

*)

Definition data_stack2 := list arithmetic_expression.

Fixpoint beq_ae (ae1 ae2 : arithmetic_expression) :=
  match ae1 with
  | (Lit n) =>
      match ae2 with
      | (Lit n') => beq_nat n n'
      | _ => false
      end
  | (Plus ae1' ae2') =>
      match ae2 with
      | (Plus ae1'' ae2'') => (beq_ae ae1' ae1'') && (beq_ae ae2' ae2'')
      | _ => false
      end
  | (Times ae1' ae2') =>
      match ae2 with
      | (Times ae1'' ae2'') => (beq_ae ae1' ae1'') && (beq_ae ae2' ae2'')
      | _ => false
      end
  end.

Compute beq_ae (Plus (Lit 0) (Lit 0)) (Plus (Lit 0) (Lit 0)).
Compute beq_ae (Plus (Lit 1) (Lit 0)) (Plus (Lit 0) (Lit 0)).

Definition beq_ae_list (s1 s2 : data_stack2) :=
  beq_list arithmetic_expression s1 s2 beq_ae.

Definition unit_test_for_magritte (magritte : byte_code_program -> data_stack2) :=
  (beq_ae_list (magritte (PUSH 5 :: nil))
               (Lit 5 :: nil)) 
  &&
  (beq_ae_list (magritte (PUSH 1 :: PUSH 2 :: ADD :: nil))
               (Plus (Lit 2) (Lit 1) :: nil))
  &&
  (beq_ae_list (magritte (PUSH 1 :: PUSH 2 :: MUL :: nil))
               (Times (Lit 2) (Lit 1) :: nil))
  &&
  (beq_ae_list (magritte (nil))
               nil)
  &&
  (beq_ae_list (magritte (PUSH 1 :: MUL :: nil))
               (Times (Lit 1) (Lit 0) :: nil))
  &&
  (beq_ae_list (magritte (PUSH 1 :: ADD :: nil))
               (Plus (Lit 1) (Lit 0) :: nil))
  &&
  (beq_ae_list (magritte (ADD :: MUL :: nil))
               (Times (Plus (Lit 0) (Lit 0)) (Lit 0) :: nil)).

Definition specification_of_magritte (magritte : byte_code_program -> data_stack2 -> data_stack2) :=
  (forall (s : data_stack2),
    magritte nil s = s)
  /\
  (forall (n : nat) (prog : byte_code_program) (s : data_stack2),
    magritte ((PUSH n) :: prog) s = magritte prog ((Lit n) :: s))
  /\
  (forall (prog : byte_code_program),
    magritte (ADD :: prog) nil = magritte prog ((Plus (Lit 0) (Lit 0)) :: nil))
  /\
  (forall (prog : byte_code_program) (ae : arithmetic_expression),
    magritte (ADD :: prog) (ae :: nil) = magritte prog ((Plus (Lit 0) ae) :: nil))
  /\
  (forall (prog : byte_code_program) (ae1 ae2 : arithmetic_expression) (s : data_stack2),
    magritte (ADD :: prog) (ae1 :: ae2 :: s) = magritte prog ((Plus ae2 ae1) :: s))
  /\
  (forall (prog : byte_code_program),
    magritte (MUL :: prog) nil = magritte prog ((Times (Lit 0) (Lit 0)) :: nil))
  /\
  (forall (prog : byte_code_program) (ae : arithmetic_expression),
    magritte (MUL :: prog) (ae :: nil) = magritte prog ((Times (Lit 0) ae) :: nil))
  /\
  (forall (prog : byte_code_program) (ae1 ae2 : arithmetic_expression) (s : data_stack2),
    magritte (MUL :: prog) (ae1 :: ae2 :: s) = magritte prog ((Times ae2 ae1) :: s)).

Theorem there_is_only_one_magritte :
  forall (f g : byte_code_program -> data_stack2 -> data_stack2),
    specification_of_magritte f ->
    specification_of_magritte g ->
    forall (prog : byte_code_program) (s : data_stack2),
      f prog s = g prog s.
Proof.
  intros f g.
  unfold specification_of_magritte.
  intros [H_f_nil [H_f_push [H_f_add_0 [H_f_add_1 [H_f_add_2 [H_f_mul_0 [H_f_mul_1 H_f_mul_2]]]]]]].
  intros [H_g_nil [H_g_push [H_g_add_0 [H_g_add_1 [H_g_add_2 [H_g_mul_0 [H_g_mul_1 H_g_mul_2]]]]]]].
  intro prog.
  induction prog as [ | instr prog IHprog].
    intro s.
    rewrite -> H_f_nil.
    rewrite -> H_g_nil.
    reflexivity.
  intro s.
  case instr as [ n | | ].
      rewrite -> H_f_push.
      rewrite -> H_g_push.
      rewrite -> IHprog.
      reflexivity.
    case s as [ | ae s' ].
      rewrite -> H_f_add_0.
      rewrite -> H_g_add_0.
      rewrite -> IHprog.
      reflexivity.
    case s' as [ | ae' s''].
      rewrite -> H_f_add_1.
      rewrite -> H_g_add_1.
      rewrite -> IHprog.
      reflexivity.
    rewrite -> H_f_add_2.
    rewrite -> H_g_add_2.
    rewrite -> IHprog.
    reflexivity.
  case s as [ | ae s' ].
    rewrite -> H_f_mul_0.
    rewrite -> H_g_mul_0.
    rewrite -> IHprog.
    reflexivity.
  case s' as [ | ae' s''].
    rewrite -> H_f_mul_1.
    rewrite -> H_g_mul_1.
    rewrite -> IHprog.
    reflexivity.
  rewrite -> H_f_mul_2.
  rewrite -> H_g_mul_2.
  rewrite -> IHprog.
  reflexivity.
Qed.

Fixpoint magritte_ds (prog : byte_code_program) (s : data_stack2) :=
  match prog with
  | nil => s
  | (PUSH n) :: prog' => magritte_ds prog' ((Lit n) :: s)
  | ADD :: prog' => 
      match s with
      | nil => magritte_ds prog' ((Plus (Lit 0) (Lit 0)) :: nil)
      | ae :: nil => magritte_ds prog' ((Plus (Lit 0) ae) :: nil)
      | ae1 :: ae2 :: exps => magritte_ds prog' ((Plus ae2 ae1) :: exps)
      end
  | MUL :: prog' => 
      match s with
      | nil => magritte_ds prog' ((Times (Lit 0) (Lit 0)) :: nil)
      | ae :: nil => magritte_ds prog' ((Times (Lit 0) ae) :: nil)
      | ae1 :: ae2 :: s' => magritte_ds prog' ((Times ae2 ae1) :: s')
      end
  end.

Definition magritte_v0 (prog : byte_code_program) :=
  magritte_ds prog nil.

Compute unit_test_for_magritte magritte_v0.

Lemma unfold_magritte_ds_nil_prog :
  forall (s : data_stack2),
    magritte_ds nil s = s.
Proof.
  unfold_tactic magritte_ds.
Qed.

Lemma unfold_magritte_ds_push :
  forall (n : nat) (prog' : byte_code_program) (s : data_stack2),
    magritte_ds ((PUSH n) :: prog') s = magritte_ds prog' ((Lit n) :: s).
Proof.
  unfold_tactic magritte_ds.
Qed.

Lemma unfold_magritte_ds_add_0 :
  forall (prog' : byte_code_program),
    magritte_ds (ADD :: prog') nil = magritte_ds prog' ((Plus (Lit 0) (Lit 0)) :: nil).
Proof.
  unfold_tactic magritte_ds.
Qed.

Lemma unfold_magritte_ds_add_1 :
  forall (prog' : byte_code_program) (ae : arithmetic_expression),
    magritte_ds (ADD :: prog') (ae :: nil) = magritte_ds prog' ((Plus (Lit 0) ae) :: nil).
Proof.
  unfold_tactic magritte_ds.
Qed.

Lemma unfold_magritte_ds_add_2 :
  forall (prog' : byte_code_program) (ae1 ae2 : arithmetic_expression) (s : data_stack2),
    magritte_ds (ADD :: prog') (ae1 :: ae2 :: s) = magritte_ds prog' ((Plus ae2 ae1) :: s).
Proof.
  unfold_tactic magritte_ds.
Qed.

Lemma unfold_magritte_ds_mul_0 :
  forall (prog' : byte_code_program),
    magritte_ds (MUL :: prog') nil = magritte_ds prog' ((Times (Lit 0) (Lit 0)) :: nil).
Proof.
  unfold_tactic magritte_ds.
Qed.

Lemma unfold_magritte_ds_mul_1 :
  forall (prog' : byte_code_program) (ae : arithmetic_expression),
    magritte_ds (MUL :: prog') (ae :: nil) = magritte_ds prog' ((Times (Lit 0) ae) :: nil).
Proof.
  unfold_tactic magritte_ds.
Qed.

Lemma unfold_magritte_ds_mul_2 :
  forall (prog' : byte_code_program) (ae1 ae2 : arithmetic_expression) (s : data_stack2),
    magritte_ds (MUL :: prog') (ae1 :: ae2 :: s) = magritte_ds prog' ((Times ae2 ae1) :: s).
Proof.
  unfold_tactic magritte_ds.
Qed.

Theorem magritte_ds_fits_the_specification_of_magritte :
  specification_of_magritte magritte_ds.
Proof.
  unfold specification_of_magritte.
  split.
    exact unfold_magritte_ds_nil_prog.
  split.
    exact unfold_magritte_ds_push.
  split.
    exact unfold_magritte_ds_add_0.
  split.
    exact unfold_magritte_ds_add_1.
  split.
    exact unfold_magritte_ds_add_2.
  split.
    exact unfold_magritte_ds_mul_0.
  split.
    exact unfold_magritte_ds_mul_1.
  exact unfold_magritte_ds_mul_2.
Qed.

(* Exercise 10:
   Prove that the Magrite-style execution function from Exercise 9
   implements a decompiler that is the left inverse of the compiler
   of Exercise 6.
*)

Compute ae_0.

Definition unit_test_for_run_magritte (candidate : byte_code_program -> arithmetic_expression) :=
  (beq_ae (candidate (compile_v0 ae_0))
          ae_0)
  &&
  (beq_ae (candidate (compile_v0 ae_1))
          ae_1)
  &&
  (beq_ae (candidate (compile_v0 ae_2))
          ae_2).

Definition specification_of_run_magritte (run_magritte : byte_code_program -> arithmetic_expression) :=
  (forall prog : byte_code_program,
    run_magritte prog = 
      match (magritte_v0 prog) with
      | ae :: nil => ae
      | _ => Lit 0
      end).

Theorem there_is_only_one_run_magritte :
  forall (f g : byte_code_program -> arithmetic_expression),
    specification_of_run_magritte f ->
    specification_of_run_magritte g ->
    forall prog : byte_code_program,
      f prog = g prog.
Proof.
  intros f g.
  unfold specification_of_run_magritte.
  intros S_f S_g.
  intro prog.
  rewrite -> S_f.
  rewrite -> S_g.
  reflexivity.
Qed.

Definition run_magritte (prog : byte_code_program) : arithmetic_expression :=
  match (magritte_v0 prog) with
  | ae :: nil => ae
  | _ => Lit 0
  end.

Compute unit_test_for_run_magritte run_magritte.

Proposition run_magritte_fits_the_specification_of_run_magritte :
  specification_of_run_magritte run_magritte.
Proof.
  unfold specification_of_run_magritte.
  intro prog.
  unfold run_magritte.
  reflexivity.
Qed.

Check unfold_append_bc.
Check unfold_append_ic.

Lemma about_magritte_ds_and_append :
  forall (p1 p2 : byte_code_program) (s : data_stack2),
    magritte_ds (p1 ++ p2) s = magritte_ds p2 (magritte_ds p1 s).
Proof.
  intro p1.
  induction p1 as [ | instr prog IHprog ].
    intros p2 s.
    rewrite -> unfold_append_bc.
    rewrite -> unfold_magritte_ds_nil_prog.
    reflexivity.
  intros p2 s.
  rewrite -> unfold_append_ic.
  case instr as [ n | | ].
      rewrite ->2 unfold_magritte_ds_push.
      rewrite -> IHprog.
      reflexivity.
    case s as [ | ae s'].
      rewrite ->2 unfold_magritte_ds_add_0.
      rewrite -> IHprog.
      reflexivity.
    case s' as [ | ae' s''].
      rewrite ->2 unfold_magritte_ds_add_1.
      rewrite -> IHprog.
      reflexivity.
    rewrite ->2 unfold_magritte_ds_add_2.
    rewrite -> IHprog.
    reflexivity.
  case s as [ | ae s'].
    rewrite ->2 unfold_magritte_ds_mul_0.
    rewrite -> IHprog.
    reflexivity.
  case s' as [ | ae' s''].
    rewrite ->2 unfold_magritte_ds_mul_1.
    rewrite -> IHprog.
    reflexivity.
  rewrite ->2 unfold_magritte_ds_mul_2.
  rewrite -> IHprog.
  reflexivity.
Qed.

Lemma magritte_on_compiled_ae_eq_ae_cons_data_stack :
  forall (ae : arithmetic_expression) (s : data_stack2),
    magritte_ds (compile_v0 ae) s = ae :: s.
Proof.
  intro ae.
  unfold compile_v0.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1' IHae1' ae2' IHae2' ].
      intro s.
      rewrite -> unfold_compile_ds_lit.
      rewrite -> unfold_magritte_ds_push.
      rewrite -> unfold_magritte_ds_nil_prog.
      reflexivity.
    intro s.
    rewrite -> unfold_compile_ds_plus.
    rewrite ->2 about_magritte_ds_and_append.
    rewrite -> IHae1.
    rewrite -> IHae2.
    rewrite -> unfold_magritte_ds_add_2.
    rewrite -> unfold_magritte_ds_nil_prog.
    reflexivity.
  intro s.
  rewrite -> unfold_compile_ds_times.
  rewrite ->2 about_magritte_ds_and_append.
  rewrite -> IHae1'.
  rewrite -> IHae2'.
  rewrite -> unfold_magritte_ds_mul_2.
  rewrite -> unfold_magritte_ds_nil_prog.
  reflexivity.
Qed.

Theorem run_magritte_implements_a_decompiler :
  forall ae : arithmetic_expression,
    run_magritte(compile_v0 ae) = ae.
Proof.
  intro ae.
  unfold run_magritte.
  unfold magritte_v0.
  rewrite -> magritte_on_compiled_ae_eq_ae_cons_data_stack.
  reflexivity.
Qed.

(* ********** *)

(* end of week_39b_arithmetic_expressions.v *)
