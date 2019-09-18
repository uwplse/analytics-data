Require Import POCS.
Require Import ThreeVariablesAPI.
Module Exercises (vars: VarsAPI).
Check vars.read.
Check vars.write.
Definition incX : proc unit :=
  x <- vars.read VarX; _ <- vars.write VarX (x + 1); Ret tt.
Theorem incX_test :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := state = mkState 1 2 3;
     post := fun r state' => state' = mkState 2 2 3;
     recovered := fun _ state' => False |}) incX vars.recover vars.abstr.
Proof.
(unfold incX).
step_proc.
(simpl).
step_proc.
(simpl).
step_proc.
Qed.
Theorem incX_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (StateX state + 1) (StateY state) (StateZ state);
     recovered := fun _ state' => False |}) incX vars.recover vars.abstr.
Proof.
(unfold incX).
(repeat step_proc).
Qed.
Hint Resolve incX_ok: core.
Opaque incX.
Theorem incX_ok_seems_good :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := state = mkState 5 5 5;
     post := fun r state' => state' = mkState 6 5 5;
     recovered := fun _ state' => False |}) incX vars.recover vars.abstr.
Proof.
(repeat step_proc).
Qed.
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
     recovered := fun _ state' => False |}) swapXY vars.recover vars.abstr.
Proof.
(repeat step_proc).
Qed.
Hint Resolve swapXY_ok: core.
Opaque swapXY.
Theorem swapXY_ok_seems_good :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := state = mkState 2 3 4;
     post := fun r state' => state' = mkState 3 2 4;
     recovered := fun _ state' => False |}) swapXY vars.recover vars.abstr.
Proof.
step_proc.
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
End Exercises.
