Time From Coq Require Import List.
Time From Perennial Require Export Lib.
Time Require Import ExMach.ExMachAPI.
Time Module DB.
Time
Inductive Op : Type -> Type :=
  | Add : forall n : nat, Op unit
  | Avg : Op nat.
Time Definition State := list nat.
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Add n => puts (cons n)
          | Avg => reads (fun l => fold_right plus 0 l / length l)
          end;
  crash_step := puts (fun _ => nil);
  finish_step := puts (fun _ => nil) |}.
Time
Lemma crash_total_ok (s : State) :
  exists s', dynamics.(crash_step) s (Val s' tt).
Time Proof.
Time (eexists; econstructor).
Time Qed.
Time
Lemma crash_non_err_ok (s : State) ret :
  dynamics.(crash_step) s ret -> ret \226\137\160 Err.
Time Proof.
Time (inversion 1; congruence).
Time Qed.
Time
Definition l : Layer Op :=
  {|
  Layer.OpState := State;
  sem := dynamics;
  trace_proj := fun _ => nil;
  crash_preserves_trace := fun _ _ _ => eq_refl;
  crash_total := crash_total_ok;
  finish_total := crash_total_ok;
  crash_non_err := crash_non_err_ok;
  finish_non_err := crash_non_err_ok;
  initP := fun s => s = nil |}.
Time End DB.
Time Definition sum_addr := 0.
Time Definition count_addr := 1.
Time Definition lock_addr := 2.
Time
Definition add n :=
  (_ <- lock lock_addr;
   sum <- read_mem sum_addr;
   _ <- write_mem sum_addr (n + sum)%nat;
   count <- read_mem count_addr;
   _ <- write_mem count_addr (1 + count)%nat; unlock lock_addr)%proc.
Time
Definition avg :=
  (_ <- lock lock_addr;
   sum <- read_mem sum_addr;
   count <- read_mem count_addr; _ <- unlock lock_addr; Ret (sum / count)%nat)%proc.
Time
Definition impl : LayerImpl ExMach.Op DB.Op :=
  {|
  compile_op := fun T (op : DB.Op T) =>
                match op with
                | DB.Add n => add n
                | DB.Avg => avg
                end;
  recover := Seq_Cons (Ret tt) Seq_Nil |}.
