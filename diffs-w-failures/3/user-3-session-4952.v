Time From Coq Require Import List.
Time From stdpp Require Import gmap.
Time From Perennial Require Export Lib.
Time From Perennial Require Import TwoDiskAPI.
Time Module OneDisk.
Time Definition disk := gmap addr nat.
Time
Inductive Op : Type -> Type :=
  | Read_Disk : forall i : addr, Op nat
  | Write_Disk : forall (i : addr) (v : nat), Op unit.
Time Record State := mkState {disk_state : disk}.
Time Definition state_wf s := wf_range (disk_state s).
Time
Definition lookup_default (i : addr) (s : gmap addr nat) : nat :=
  match s !! i with
  | Some n => n
  | None => 0
  end.
Time
Definition upd_default (i : addr) (v : nat) (s : gmap addr nat) :
  gmap addr nat := match s !! i with
                   | Some _ => <[i:=v]> s
                   | None => s
                   end.
Time
Definition lookup_disk (i : addr) : State -> nat :=
  fun s => lookup_default i (disk_state s).
Time
Definition upd_disk (i : addr) (v : nat) :=
  fun s => {| disk_state := upd_default i v (disk_state s) |}.
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Read_Disk i => reads (lookup_disk i)
          | Write_Disk i v => puts (upd_disk i v)
          end;
  crash_step := pure tt;
  finish_step := pure tt |}.
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
Time Definition init_state := {| disk_state := init_zero |}.
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
  initP := fun s => s = init_state |}.
Time End OneDisk.
