Require Import Examples.StatDb.Impl.
Require Import Examples.StatDb.Impl.
From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Lib.
From Transitions Require Import Relations Rewriting.
Import RelationNotations.
From Transitions Require Import NonError.
Require Import Spec.Hoare.
Require Export Maybe Disk.
Require Export Maybe Disk.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.
Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l res =>
  match res with
  | Val s _ => fst s = fold_right plus 0 l /\ snd s = length l
  | Err _ _ => False
  end.
Instance absr_non_error : (NonError absr).
Proof.
(compute; auto).
Qed.
Definition init_hspec : Specification InitStatus unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' _ => state' = (0, 0);
  alternate := fun state' (_ : unit) => True |}.
Definition add_hspec n : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\ snd state' = S (snd state);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Definition add_rspec n : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\ snd state' = S (snd state);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Definition avg_hspec : Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => state = state' /\ v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition avg_rspec : Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => state = state' /\ v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition recover_spec : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' (_ : unit) => state' = (0, 0);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Lemma read_op_ok :
  forall i,
  proc_hspec Var.dynamics (read i) (op_spec Var.dynamics (Var.Read i)).
Proof.
(intros).
(eapply op_spec_sound).
Qed.
Module D.
Definition State := disk.
Module TxnD.
Definition State : Type := disk * disk.
Inductive WriteStatus :=
  | WriteOK : _
  | WriteErr : _.
Inductive Op : Type -> Type :=
  | op_read : forall a : addr, Op block
  | op_write : forall (a : addr) (b : block), Op unit
  | op_size : Op nat.
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
Inductive Op : Type -> Type :=
  | op_commit : Op unit
  | op_read : forall a : addr, Op block
  | op_write : forall (a : addr) (b : block), Op WriteStatus
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
