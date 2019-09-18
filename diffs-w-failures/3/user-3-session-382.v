From RecoveryRefinement Require Import Lib.
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
