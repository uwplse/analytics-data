From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Lib.
Require Export Maybe Disk.
Require Export Maybe Disk.
Module TxnD.
Definition State : Type := disk * disk.
Inductive WriteStatus :=
  | WriteOK : _
  | WriteErr : _.
Inductive Op : Type -> Type :=
  | op_commit : Op unit
  | op_read : forall a : addr, Op block
  | op_write : forall (a : addr) (b : block), Op WriteStatus
  | op_size : Op nat.
Module D.
Definition State := disk.
Inductive Op : Type -> Type :=
  | op_read : forall a : addr, Op block
  | op_write : forall (a : addr) (b : block), Op unit
  | op_size : Op nat.
Inductive op_step : OpSemantics Op State :=
  | step_commit : forall d_old d, op_step op_commit (d_old, d) (d, d) tt
  | step_read :
      forall a r d_old d,
      match index d_old a with
      | Some b0 => r = b0
      | None => exists b, r = b
      end -> op_step (op_read a) (d_old, d) (d_old, d) r
  | step_write_success :
      forall a b d_old d d',
      d' = assign d a b ->
      op_step (op_write a b) (d_old, d) (d_old, d') WriteOK
  | step_write_fail :
      forall a b d_old d,
      op_step (op_write a b) (d_old, d) (d_old, d) WriteErr
  | step_size :
      forall d_old d, op_step op_size (d_old, d) (d_old, d) (length d).
Inductive op_step : OpSemantics Op State :=
  | step_read :
      forall a r state,
      match index state a with
      | Some b0 => r = b0
      | None => exists b, r = b
      end -> op_step (op_read a) state state r
  | step_write :
      forall a b state state',
      state' = assign state a b -> op_step (op_write a b) state state' tt
  | step_size : forall state, op_step op_size state state (length state).
Inductive one_disk_failure : CrashSemantics State :=
    step_id : forall state : State, one_disk_failure state state tt.
Definition ODBaseDynamics : Dynamics Op State :=
  {| step := op_step; crash_step := one_disk_failure |}.
Definition ODLayer : Layer Op :=
  {| Layer.State := State; sem := ODBaseDynamics; initP := fun _ => True |}.
End D.
Definition read_spec (a : addr) : Specification block unit D.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' r => state' = state /\ index state a ?|= eq r;
  alternate := fun state' r => state' = state |}.
Definition write_spec (a : addr) (v : block) :
  Specification _ unit D.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' r => r = tt /\ state' = assign state a v;
  alternate := fun state' r => state' = state \/ state' = assign state a v |}.
Definition size_spec : Specification nat unit D.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' r => state' = state /\ r = length state;
  alternate := fun state' r => state' = state |}.
Definition txn_crash : State -> State -> unit -> Prop :=
  fun '(d_old, d) '(d_old', d') r => d_old' = d_old /\ d' = d_old.
Definition dyn : Dynamics Op State :=
  {| step := op_step; crash_step := txn_crash |}.
Definition l : Layer Op :=
  {|
  Layer.State := State;
  sem := dyn;
  initP := fun '(d_old, d) => d_old = d |}.
End TxnD.
