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

Definition arth_0 :=
  Lit 5.

Definition arth_1 :=
  Plus (Lit 4) (Lit 2).

Definition arth_2 :=
  Plus (Times (Lit 4) (Lit 9)) (Lit 2).

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

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

Definition unit_test_for_arithmetic_expression (interpret : arithmetic_expression -> nat) :=
  (interpret arth_0 =n= 5)
  &&
  (interpret arth_1 =n= 6)
  &&
  (interpret arth_2 =n= 38)
  .

(* Exercise 2:
   Define an interpreter as a function
   that satisfies the specification above
   and verify that it passes the unit tests.
*)

Fixpoint interpret_arithmetic (exp : arithmetic_expression) : nat :=
  match exp with
    | Lit n => n
    | Plus a b => interpret_arithmetic a + interpret_arithmetic b
    | Times a b => interpret_arithmetic a * interpret_arithmetic b
  end.

Compute unit_test_for_arithmetic_expression interpret_arithmetic.

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

Fixpoint f_on_stack (f : nat -> nat -> nat) (l : data_stack) :=
  match l with
    | nil => 0 :: nil
    | a :: y => 
      match y with
        | nil => (f a 0) :: nil
        | b :: x => (f a b) :: x
      end
  end.

Lemma unfold_f_on_stack_zero :
  (forall f : nat -> nat -> nat,
  f_on_stack f nil = 0 :: nil).
Proof.
  unfold_tactic f_on_stack.
Qed.

Lemma unfold_f_on_stack_one :
  (forall (f : nat -> nat -> nat) (n : nat),
  f_on_stack f (n :: nil) = (f n 0) :: nil).
Proof.
  unfold_tactic f_on_stack.
Qed.

Lemma unfold_f_on_stack_two :
  (forall (f : nat -> nat -> nat) (x y : nat) (xy : list nat),
  f_on_stack f (x :: y :: xy) = (f x y) :: xy).
Proof.
  unfold_tactic f_on_stack.
Qed.

Definition specification_of_execute_byte_code_instruction
           (instr : byte_code_instruction -> data_stack -> data_stack) :=
  (forall (n : nat) (s : data_stack),
     instr (PUSH n) s = n :: s)
  /\
  (forall (s : data_stack),
     instr ADD s = (f_on_stack plus s))
  /\
  (forall (s : data_stack),
     instr MUL s = (f_on_stack mult s))
.

Fixpoint execute_byte_code_instruction (inst : byte_code_instruction) (s : data_stack): data_stack :=
    match inst with
      | PUSH n => n :: s
      | ADD => f_on_stack plus s
      | MUL => f_on_stack mult s
  end.

Lemma unfold_execute_byte_code_instruction_push :
  forall (n : nat) (s : data_stack),
    execute_byte_code_instruction (PUSH n) s = n :: s.
Proof.
  unfold_tactic execute_byte_code_instruction.
Qed.

Lemma unfold_execute_byte_code_instruction_add :
  forall (s : data_stack),
    execute_byte_code_instruction ADD s = f_on_stack plus s.
Proof.
  unfold_tactic execute_byte_code_instruction.
Qed.

Lemma unfold_execute_byte_code_instruction_mul :
  forall (s : data_stack),
    execute_byte_code_instruction MUL s = f_on_stack mult s.
Proof.
  unfold_tactic execute_byte_code_instruction.
Qed.

Proposition execute_byte_code_instruction_fits_the_specification_of_execute_byte_code_instruction :
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

Fixpoint execute_byte_code_program (prog : byte_code_program) (s : data_stack): data_stack :=
  match prog with
    | nil => s
    | x :: y => (execute_byte_code_program y (execute_byte_code_instruction x s))
  end.

Lemma unfold_execute_byte_code_program_bc :
  forall (s : data_stack),
    (execute_byte_code_program nil s) = s.
Proof.
  unfold_tactic execute_byte_code_program.
Qed.

Lemma unfold_execute_byte_code_program_ic :
  forall (x : byte_code_instruction) (xs : byte_code_program) (s : data_stack),
    (execute_byte_code_program (x :: xs) s) = (execute_byte_code_program xs (execute_byte_code_instruction x s)).
Proof.
  unfold_tactic execute_byte_code_program.
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

Theorem append_before_execute_yields_same_result :
  (forall (p1 p2 : byte_code_program) (s : data_stack),
     (execute_byte_code_program (p1 ++ p2) s) =
     (execute_byte_code_program p2 (execute_byte_code_program p1 s))).
Proof.
  intro p1.
  induction p1 as [| x xs IHx].
    intros p2 s.
    rewrite -> unfold_execute_byte_code_program_bc.
    rewrite -> app_nil_l.
    reflexivity.
  intros p2 s.
  rewrite -> unfold_append_ic.
  rewrite -> (unfold_execute_byte_code_program_ic x (xs ++ p2) s).
  rewrite -> IHx.
  rewrite -> unfold_execute_byte_code_program_ic.
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
     compile (Times ae1 ae2) = (compile ae1) ++ (compile ae2)++ (MUL :: nil)).

(* Exercise 6:
   Define a compiler as a function
   that satisfies the specification above
   and uses list concatenation, i.e., ++.
*)

Fixpoint compile_expression_v0 (exp : arithmetic_expression) : byte_code_program :=
  match exp with
  | Lit n => PUSH n :: nil
  | Plus ae1 ae2 => compile_expression_v0 ae1 ++ compile_expression_v0 ae2 ++ ADD :: nil
  | Times ae1 ae2 => compile_expression_v0 ae1 ++ compile_expression_v0 ae2 ++ MUL :: nil
  end.

Lemma unfold_compile_expression_lit :
  forall n : nat,
    compile_expression_v0 (Lit n) = PUSH n :: nil.
Proof.
  unfold_tactic compile_expression_v0.
Qed.

Lemma unfold_compile_expression_plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_expression_v0 (Plus ae1 ae2) = compile_expression_v0 ae1 ++ compile_expression_v0 ae2 ++ ADD :: nil.
Proof.
  unfold_tactic compile_expression_v0.
Qed.

Lemma unfold_compile_expression_times :
  forall ae1 ae2 : arithmetic_expression,
    compile_expression_v0 (Times ae1 ae2) = compile_expression_v0 ae1 ++ compile_expression_v0 ae2 ++ MUL :: nil.
Proof.
  unfold_tactic compile_expression_v0.
Qed.


Proposition compile_expression_v0_fits_the_specification_of_compile :
  specification_of_compile compile_expression_v0.
Proof.
  unfold specification_of_compile.
  split.
    exact unfold_compile_expression_lit.
  split.
    exact unfold_compile_expression_plus.
  exact unfold_compile_expression_times.
Qed.

(* Exercise 7:
   Write a compiler as a function with an accumulator
   that does not use ++ but :: instead,
   and prove it equivalent to the compiler of Exercise 6.
*)

Fixpoint compile_expression_acc (exp : arithmetic_expression) (prog : byte_code_program) : byte_code_program :=
  match exp with
  | Lit n => PUSH n :: prog
  | Plus ae1 ae2 => (compile_expression_acc ae1 (compile_expression_acc ae2 (ADD :: prog)))  
  | Times ae1 ae2 => (compile_expression_acc ae1 (compile_expression_acc ae2 (MUL :: prog)))
  end.
    
Lemma unfold_compile_expression_acc_lit :
  forall (n : nat) (prog : byte_code_program),
    compile_expression_acc (Lit n) prog = PUSH n :: prog.
Proof.
  unfold_tactic compile_expression_acc.
Qed.

Lemma unfold_compile_expression_acc_plus :
  forall (ae1 ae2 : arithmetic_expression) (prog : byte_code_program),
    compile_expression_acc (Plus ae1 ae2) prog = (compile_expression_acc ae1 (compile_expression_acc ae2 (ADD :: prog))).
Proof.
  unfold_tactic compile_expression_acc.
Qed.

Lemma unfold_compile_expression_acc_times :
  forall (ae1 ae2 : arithmetic_expression) (prog : byte_code_program),
    compile_expression_acc (Times ae1 ae2) prog = (compile_expression_acc ae1 (compile_expression_acc ae2 (MUL :: prog))).
Proof.
  unfold_tactic compile_expression_acc.
Qed.

Definition compile_expression_v1 (exp : arithmetic_expression) : byte_code_program :=
  compile_expression_acc exp nil.

Lemma about_compile_expression_acc :
  forall (exp : arithmetic_expression) (prog : byte_code_program),
    compile_expression_acc exp prog = compile_expression_acc exp nil ++ prog.
Proof.
  intros exp.
  induction exp as [ | exp1' IHexp1' exp2' IHexp2' | exp1'' IHexp1'' exp2'' IHexp2'' ].
      intro prog.
      rewrite ->2 unfold_compile_expression_acc_lit.
      rewrite -> unfold_append_ic.
      rewrite -> app_nil_l.
      reflexivity.
    intro prog.
    rewrite ->2 unfold_compile_expression_acc_plus.
    rewrite -> IHexp1'.
    rewrite -> IHexp2'.
    rewrite -> (IHexp1' (compile_expression_acc exp2' (ADD :: nil))).
    rewrite -> (IHexp2' (ADD :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> app_assoc_reverse.
    rewrite -> unfold_append_ic.
    rewrite -> app_nil_l.
    reflexivity.
  intro prog.  
  rewrite ->2 unfold_compile_expression_acc_times.
  rewrite -> IHexp1''.
  rewrite -> IHexp2''.
  rewrite -> (IHexp1'' (compile_expression_acc exp2'' (MUL :: nil))).
  rewrite -> (IHexp2'' (MUL :: nil)).
  rewrite -> app_assoc_reverse.
  rewrite -> app_assoc_reverse.
  rewrite -> unfold_append_ic.
  rewrite -> app_nil_l.
  reflexivity.
Qed.

Proposition compile_expression_v1_fits_the_specification_of_compile :
  specification_of_compile compile_expression_v1.
Proof.
  unfold specification_of_compile.
  split.
    intro n.
    unfold compile_expression_v1.
    rewrite -> unfold_compile_expression_acc_lit.
    reflexivity.
  split.
    intros ae1 ae2.
    unfold compile_expression_v1.
    rewrite -> unfold_compile_expression_acc_plus.
    rewrite -> about_compile_expression_acc.
    rewrite -> (about_compile_expression_acc ae2 (ADD :: nil)).
    reflexivity.
  intros ae1 ae2.
  unfold compile_expression_v1.
  rewrite -> unfold_compile_expression_acc_times.
  rewrite -> about_compile_expression_acc.
  rewrite -> (about_compile_expression_acc ae2 (MUL :: nil)).
  reflexivity.
Qed.

Theorem there_is_only_one_compile_expression :
  forall (compiler1 compiler2 : arithmetic_expression -> byte_code_program),
    specification_of_compile compiler1 ->
    specification_of_compile compiler2 ->
    forall (exp : arithmetic_expression),
      compiler1 exp = compiler2 exp.
Proof.
  intros compiler1 compiler2.
  unfold specification_of_compile.
  intros [H_c1_lit [H_c1_plus H_c1_times]].
  intros [H_c2_lit [H_c2_plus H_c2_times]].
  intro exp.
  induction exp as [ | exp1' IHexp1' exp2' IHexp2' | exp1'' IHexp1'' exp2'' IHexp2'' ].
      rewrite -> H_c1_lit.
      rewrite -> H_c2_lit.
      reflexivity.
    rewrite -> H_c1_plus.
    rewrite -> H_c2_plus.
    rewrite -> IHexp1'.
    rewrite -> IHexp2'.
    reflexivity.
  rewrite -> H_c1_times.
  rewrite -> H_c2_times.
  rewrite -> IHexp1''.
  rewrite -> IHexp2''.
  reflexivity.
Qed.

(* ********** *)

(* Exercise 8:
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program
   over an empty data stack.
*)

Definition run (prog : byte_code_program) : nat :=
  match execute_byte_code_program prog nil with
  | nil => 0
  | result :: _ => result
  end.

Lemma unfold_interpret_lit :
  forall n : nat,
    interpret_arithmetic (Lit n) = n.
Proof.
  unfold_tactic interpret_arithmetic.
Qed.

Lemma unfold_interpret_plus :
  forall a b : arithmetic_expression,
    interpret_arithmetic (Plus a b) = interpret_arithmetic a + interpret_arithmetic b.
Proof.
  unfold_tactic interpret_arithmetic.
Qed.

Lemma unfold_interpret_times :
  forall a b : arithmetic_expression,
    interpret_arithmetic (Times a b) = interpret_arithmetic a * interpret_arithmetic b.
Proof.
  unfold_tactic interpret_arithmetic.
Qed.

Lemma interpret_cons_datastack_eq_compile_execute :
  forall (exp : arithmetic_expression) (ds : data_stack),
    interpret_arithmetic exp :: ds = execute_byte_code_program (compile_expression_v0 exp) ds.
Proof.
  intro exp.
  induction exp as [ n | exp1' IHexp1' exp2' IHexp2' | exp1'' IHexp1'' exp2'' IHexp2''].
      intro ds.
      rewrite -> unfold_interpret_lit.
      rewrite -> unfold_compile_expression_lit.
      rewrite -> unfold_execute_byte_code_program_ic.
      rewrite -> unfold_execute_byte_code_instruction_push.
      rewrite -> unfold_execute_byte_code_program_bc.
      reflexivity.
    intro ds.
    rewrite -> unfold_interpret_plus.
    rewrite -> unfold_compile_expression_plus.
    rewrite ->2 append_before_execute_yields_same_result.
    rewrite -> unfold_execute_byte_code_program_ic.
    rewrite -> unfold_execute_byte_code_instruction_add.
    rewrite -> unfold_execute_byte_code_program_bc.
    rewrite <- IHexp1'.
    rewrite <- IHexp2'.
    rewrite -> unfold_f_on_stack_two.
    rewrite -> plus_comm.
    reflexivity.
  intro ds.
  rewrite -> unfold_interpret_times.
  rewrite -> unfold_compile_expression_times.
  rewrite ->2 append_before_execute_yields_same_result.
  rewrite -> unfold_execute_byte_code_program_ic.
  rewrite -> unfold_execute_byte_code_instruction_mul.
  rewrite -> unfold_execute_byte_code_program_bc.
  rewrite <- IHexp1''.
  rewrite <- IHexp2''.
  rewrite -> unfold_f_on_stack_two.
  rewrite -> mult_comm.
  reflexivity.
Qed.

Theorem interpret_exp_eq_run_compile_exp :
  forall (exp : arithmetic_expression),
    interpret_arithmetic exp = run (compile_expression_v0 exp).
Proof.
  intro exp.
  unfold run.
  rewrite <- interpret_cons_datastack_eq_compile_execute.
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

Fixpoint magritte_v0 (prog : byte_code_program) (s : data_stack2) :=
  match prog with
  | nil => s
  | (PUSH n) :: prog' => magritte_v0 prog' ((Lit n) :: s)
  | ADD :: prog' => 
      match s with
      | nil => magritte_v0 prog' ((Plus (Lit 0) (Lit 0)) :: nil)
      | exp :: nil => magritte_v0 prog' ((Plus (Lit 0) exp) :: nil)
      | exp1 :: exp2 :: exps => magritte_v0 prog' ((Plus exp2 exp1) :: exps)
      end
  | MUL :: prog' => 
      match s with
      | nil => magritte_v0 prog' ((Times (Lit 0) (Lit 0)) :: nil)
      | exp :: nil => magritte_v0 prog' ((Times (Lit 0) exp) :: nil)
      | exp1 :: exp2 :: exps => magritte_v0 prog' ((Times exp2 exp1) :: exps)
      end
  end.

Lemma unfold_magritte_v0_nil_prog :
  forall (s : data_stack2),
    magritte_v0 nil s = s.
Proof.
  unfold_tactic magritte_v0.
Qed.

Lemma unfold_magritte_v0_push :
  forall (n : nat) (prog' : byte_code_program) (s : data_stack2),
    magritte_v0 ((PUSH n) :: prog') s = magritte_v0 prog' ((Lit n) :: s).
Proof.
  unfold_tactic magritte_v0.
Qed.

Lemma unfold_magritte_v0_add_nil :
  forall (prog' : byte_code_program) (s : data_stack2),
    magritte_v0 (ADD :: prog') nil = magritte_v0 prog' ((Plus (Lit 0) (Lit 0)) :: nil).
Proof.
  unfold_tactic magritte_v0.
Qed.

Lemma unfold_magritte_v0_add_1 :
  forall (prog' : byte_code_program) (exp : arithmetic_expression) (s : data_stack2),
    magritte_v0 (ADD :: prog') (exp :: nil) = magritte_v0 prog' ((Plus (Lit 0) exp) :: nil).
Proof.
  unfold_tactic magritte_v0.
Qed.

Lemma unfold_magritte_v0_add_2 :
  forall (prog' : byte_code_program) (exp1 exp2 : arithmetic_expression) (s : data_stack2),
    magritte_v0 (ADD :: prog') (exp1 :: exp2 :: s) = magritte_v0 prog' ((Plus exp2 exp1) :: s).
Proof.
  unfold_tactic magritte_v0.
Qed.

Lemma unfold_magritte_v0_mul_nil :
  forall (prog' : byte_code_program) (s : data_stack2),
    magritte_v0 (MUL :: prog') nil = magritte_v0 prog' ((Times (Lit 0) (Lit 0)) :: nil).
Proof.
  unfold_tactic magritte_v0.
Qed.

Lemma unfold_magritte_v0_mul_1 :
  forall (prog' : byte_code_program) (exp : arithmetic_expression) (s : data_stack2),
    magritte_v0 (MUL :: prog') (exp :: nil) = magritte_v0 prog' ((Times (Lit 0) exp) :: nil).
Proof.
  unfold_tactic magritte_v0.
Qed.

Lemma unfold_magritte_v0_mul_2 :
  forall (prog' : byte_code_program) (exp1 exp2 : arithmetic_expression) (s : data_stack2),
    magritte_v0 (MUL :: prog') (exp1 :: exp2 :: s) = magritte_v0 prog' ((Times exp2 exp1) :: s).
Proof.
  unfold_tactic magritte_v0.
Qed.

Definition run_magritte (prog : byte_code_program) : arithmetic_expression :=
  match (magritte_v0 prog nil) with
  | nil => Lit 0
  | exp :: _ => exp
  end.

Compute arth_2.
Compute compile_expression_v0 arth_2.
Compute run_magritte (compile_expression_v0 arth_2).

(* Exercise 10:
   Prove that the Magrite-style execution function from Exercise 9
   implements a decompiler that is the left inverse of the compiler
   of Exercise 6.
*)

Lemma append_before_magritte_yields_same_result :
  forall (p1 p2 : byte_code_program) (s : data_stack2),
       magritte_v0 (p1 ++ p2) s =
       magritte_v0 p2 (magritte_v0 p1 s).
Proof.
  intro p1.
  induction p1 as [ | x xs' IHxs'].
    intros p2 s.
    rewrite -> unfold_magritte_v0_nil_prog.
    rewrite -> app_nil_l.
    reflexivity.
  intros p2 s.
  Check unfold_append_ic.
  rewrite -> unfold_append_ic.
  induction x.
      rewrite ->2 unfold_magritte_v0_push.
      rewrite -> IHxs'.
      reflexivity.
    induction s.
    rewrite ->2 unfold_magritte_v0_add_nil.
    rewrite ->2 unfold_magritte_v0_add_1.

Lemma exp_cons_exps_eq_magritte_compile_exp :
  forall (exp : arithmetic_expression) (s : data_stack2),
    exp :: s = magritte_v0 (compile_expression_v0 exp) s.
Proof.
  intro exp.
  induction exp as [ | exp1' IHexp1' exp2' IHexp2' | exp1'' IHexp1'' exp2'' IHexp2''].
      intro s.
      rewrite -> unfold_compile_expression_lit.
      rewrite -> unfold_magritte_v0_push.
      rewrite -> unfold_magritte_v0_nil_prog.
      reflexivity.
    intro s.
    rewrite -> unfold_compile_expression_plus.
    rewrite ->2 append_before_magritte_yields_same_result.
    rewrite <- IHexp1'.
    rewrite <- IHexp2'.
    rewrite -> unfold_magritte_v0_add_2.
    rewrite -> unfold_magritte_v0_nil_prog.
    reflexivity.
  intro s.
  rewrite -> unfold_compile_expression_times.
  rewrite ->2 append_before_magritte_yields_same_result.
  rewrite <- IHexp1''.
  rewrite <- IHexp2''.
  rewrite -> unfold_magritte_v0_mul_2.
  rewrite -> unfold_magritte_v0_nil_prog.
  reflexivity.
Qed.

Theorem compile_exp_and_run_magritte_gives_exp :
  forall exp : arithmetic_expression,
    exp = run_magritte (compile_expression_v0 exp).
Proof.
  intro exp.
  unfold run_magritte.
  rewrite <- exp_cons_exps_eq_magritte_compile_exp.
  reflexivity.
Qed.

(* ********** *)

(* end of week_39b_arithmetic_expressions.v *)
