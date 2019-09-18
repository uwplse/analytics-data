Time Require Import AtomicPair.AtomicPairAPI.
Time From Coq Require Import List.
Time Require Import AtomicPair.AtomicPairAPI.
Time From Armada Require Export Lib.
Time Require Import ExMach.ExMachAPI.
Time Definition ptr_addr := 0.
Time Definition copy0_fst := 1.
Time Definition copy0_snd := 2.
Time Definition copy1_fst := 3.
Time Definition copy1_snd := 4.
Time Definition lock_addr := 0.
Time
Definition read_addrs (ptr_val : nat) : nat * nat :=
  match ptr_val with
  | O => (copy0_fst, copy0_snd)
  | _ => (copy1_fst, copy1_snd)
  end.
Time
Definition write_addrs (ptr_val : nat) : nat * nat :=
  match ptr_val with
  | 0 => (copy1_fst, copy1_snd)
  | _ => (copy0_fst, copy0_snd)
  end.
Time
Definition swap_ptr (ptr_val : nat) : nat :=
  match ptr_val with
  | O => 1
  | _ => O
  end.
Time
Definition write (p : nat * nat) :=
  (_ <- lock lock_addr;
   ptr <- read_disk ptr_addr;
   _ <- write_disk (fst (write_addrs ptr)) (fst p);
   _ <- write_disk (snd (write_addrs ptr)) (snd p);
   _ <- write_disk ptr_addr (swap_ptr ptr); unlock lock_addr)%proc.
Time
Definition read :=
  (_ <- lock lock_addr;
   ptr <- read_disk ptr_addr;
   fst_val <- read_disk (fst (read_addrs ptr));
   snd_val <- read_disk (snd (read_addrs ptr));
   _ <- unlock lock_addr; Ret (fst_val, snd_val))%proc.
Time Definition recv : proc ExMach.Op _ := Ret tt.
Time Require Import ExMach.ExMachAPI.
Time Module DB.
Time
Inductive Op : Type -> Type :=
  | Add : forall n : nat, Op unit
  | Avg : Op nat.
Time
Definition impl : LayerImpl ExMach.Op AtomicPair.Op :=
  {|
  compile_op := fun T (op : AtomicPair.Op T) =>
                match op with
                | AtomicPair.Write n => write n
                | AtomicPair.Read => read
                end;
  recover := Seq_Cons recv Seq_Nil |}.
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
Time Require Import ExMach.ExMachAPI.
Time Definition log_commit := 0.
Time Definition main_fst := 1.
Time Definition main_snd := 2.
Time Definition log_fst := 3.
Time Definition log_snd := 4.
Time Definition main_lock := 0.
Time Definition log_lock := 1.
Time
Definition write (p : nat * nat) :=
  (_ <- lock log_lock;
   _ <- write_disk log_fst (fst p);
   _ <- write_disk log_snd (snd p);
   _ <- write_disk log_commit 1;
   _ <- lock main_lock;
   _ <- write_disk main_fst (fst p);
   _ <- write_disk main_snd (snd p);
   _ <- write_disk log_commit 0; _ <- unlock log_lock; unlock main_lock)%proc.
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
Time
Definition read :=
  (_ <- lock main_lock;
   fst_val <- read_disk main_fst;
   snd_val <- read_disk main_snd;
   _ <- unlock main_lock; Ret (fst_val, snd_val))%proc.
Time
Definition recv :=
  (is_commit <- read_disk log_commit;
   match is_commit with
   | O => Ret tt
   | _ =>
       fst_val <- read_disk log_fst;
       snd_val <- read_disk log_snd;
       _ <- write_disk main_fst fst_val;
       _ <- write_disk main_snd snd_val; write_disk log_commit 0
   end)%proc.
Time
Definition impl : LayerImpl ExMach.Op AtomicPair.Op :=
  {|
  compile_op := fun T (op : AtomicPair.Op T) =>
                match op with
                | AtomicPair.Write n => write n
                | AtomicPair.Read => read
                end;
  recover := Seq_Cons recv Seq_Nil |}.
