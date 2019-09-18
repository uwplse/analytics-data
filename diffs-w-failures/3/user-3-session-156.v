Require Import Examples.StatDb.Impl.
Require Import Examples.StatDb.Impl.
From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Import Lib.
Require Export Maybe Disk.
Require Import Helpers.RelationRewriting.
From Transitions Require Import Relations Rewriting.
Import RelationNotations.
Require Export Maybe Disk.
Module TxnD.
Definition State : Type := disk * disk.
Module D.
Definition State := disk.
Inductive Op : Type -> Type :=
  | op_read : forall a : addr, Op block
  | op_write : forall (a : addr) (b : block), Op unit
  | op_size : Op nat.
Inductive WriteStatus :=
  | WriteOK : _
  | WriteErr : _.
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
