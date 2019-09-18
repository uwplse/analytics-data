Time From Coq Require Import List.
Time From Armada Require Export Lib.
Time Module AtomicPair.
Time
Inductive Op : Type -> Type :=
  | Write : forall p : nat * nat, Op unit
  | Read : Op (nat * nat).
Time Definition State : Set := nat * nat.
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Write p => puts (fun _ => p)
          | Read => reads (fun l => l)
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
  initP := fun s => s = (0, 0) |}.
Time End AtomicPair.
