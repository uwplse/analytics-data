Require Import POCS.
Require Import POCS.
Require Import Lab0.HeapVariablesAPI.
Require Import VariablesAPI.
Extraction Language Haskell.
Module Vars<: VarsAPI.
Axiom (init : proc InitResult).
Axiom (read : var -> proc nat).
Axiom (write : var -> nat -> proc unit).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (read_ok : forall v, proc_spec (read_spec v) (read v) recover abstr).
Axiom
  (write_ok :
     forall v val, proc_spec (write_spec v val) (write v val) recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_crash).
End Vars.
Extract Constant Vars.init =>  "Variables.Ops.init".
Module HeapExamples (vars: VarsAPI).
Definition swapXY : proc unit :=
  x <- vars.read VarX;
  y <- vars.read VarY; _ <- vars.write VarX y; _ <- vars.write VarY x; Ret tt.
Theorem swapXY_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' = mkState (StateY state) (StateX state) (StateZ state);
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(unfold swapXY).
step_proc.
Extract Constant Vars.read =>  "Variables.Ops.read".
Extract Constant Vars.write =>  "Variables.Ops.write".
step_proc.
step_proc.
step_proc.
step_proc.
Qed.
Theorem swapXY_ok2 :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState y x z;
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(unfold swapXY).
step_proc.
(destruct a' as ((x, y), z); simplify).
step_proc.
step_proc.
step_proc.
step_proc.
Qed.
Definition swapYZ : proc unit :=
  y <- vars.read VarY;
  z <- vars.read VarZ; _ <- vars.write VarY z; _ <- vars.write VarZ y; Ret tt.
Theorem swapYZ_ok :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState x z y;
     recovered := fun _ state' => True |}) swapYZ vars.recover vars.abstr.
Proof.
(unfold swapYZ).
step_proc.
(destruct a' as ((x, y), z); simplify).
step_proc.
step_proc.
step_proc.
step_proc.
Qed.
Definition swapXZ : proc unit :=
  _ <- swapXY; _ <- swapYZ; _ <- swapXY; Ret tt.
Hint Resolve swapXY_ok2 swapYZ_ok: core.
Theorem swapXZ_ok :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState z y x;
     recovered := fun _ state' => True |}) swapXZ vars.recover vars.abstr.
Proof.
(unfold swapXZ).
(spec_intros; simplify).
(destruct a as ((x, y), z); simplify).
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
step_proc.
Qed.
Definition swapVars (v1 v2 : var) : proc unit :=
  v1_val <- vars.read v1;
  v2_val <- vars.read v2;
  _ <- vars.write v1 v2_val; _ <- vars.write v2 v1_val; Ret tt.
Theorem swapVars_ok v1 v2 :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             forall v,
             StateVar v state' =
             (if v == v1
              then StateVar v2 state
              else if v == v2 then StateVar v1 state else StateVar v state);
     recovered := fun _ state' => True |}) (swapVars v1 v2) vars.recover
    vars.abstr.
Proof.
(unfold swapVars).
step_proc.
step_proc.
step_proc.
step_proc.
step_proc.
(destruct v, v1, v2; intuition).
Qed.
Definition inc1 (v1 : var) : proc unit :=
  v <- vars.read v1; _ <- vars.write v1 (1 + v); Ret tt.
Definition inc1X_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (1 + StateX state) (StateY state) (StateZ state);
     recovered := fun _ state' => True |}) (inc1 VarX) vars.recover
    vars.abstr.
Proof.
(unfold inc1).
step_proc.
step_proc.
step_proc.
Qed.
Hint Resolve inc1X_ok: core.
Fixpoint increment (v1 : var) (n : nat) : proc unit :=
  match n with
  | 0 => Ret tt
  | S n' => _ <- inc1 v1; increment v1 n'
  end.
Theorem incrementX_ok n :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (n + StateX state) (StateY state) (StateZ state);
     recovered := fun _ state' => True |}) (increment VarX n) vars.recover
    vars.abstr.
Proof.
(induction n; simpl).
-
step_proc.
(destruct state; auto).
-
step_proc.
step_proc.
(simpl).
f_equal.
lia.
Qed.
End HeapExamples.
