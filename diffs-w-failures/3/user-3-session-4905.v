Time From stdpp Require Import base.
Time From RecordUpdate Require Import RecordUpdate.
Time From Tactical Require Import ProofAutomation.
Time From Transitions Require Import Relations.
Time From Perennial Require Import Helpers.RecordZoom.
Time From Perennial Require Import Spec.Proc.
Time From Perennial Require Import Spec.InjectOp.
Time From Perennial Require Import Spec.Layer.
Time From Perennial.Goose Require Export Machine Heap Filesys Globals.
Time
Inductive Op `{GoModel} : Type -> Type :=
  | FilesysOp : forall T, FS.Op T -> Op T
  | DataOp : forall T, Data.Op T -> Op T
  | LockGlobalOp : forall T, Globals.Op (slice.t LockRef) T -> Op T.
Time Instance data_inj  `{GoModel}: (Injectable Data.Op Op) := DataOp.
Time Instance fs_inj  `{GoModel}: (Injectable FS.Op Op) := FilesysOp.
Time
Instance lock_global_inj  `{GoModel}:
 (Injectable (Globals.Op (slice.t LockRef)) Op) := LockGlobalOp.
Time Module Go.
Time Section GoModel.
Time Context `{model_wf : GoModelWf}.
Time
Record State : Type :={fs : FS.State;
                       maillocks : Globals.State (slice.t LockRef)}.
Time #[global]
Instance etaState : (Settable _) := settable! Build_State < fs; maillocks >.
Time
Definition step T (op : Op T) : relation State State T :=
  match op with
  | FilesysOp op => _zoom fs (FS.step op)
  | DataOp op => _zoom fs (_zoom FS.heap (Data.step op))
  | LockGlobalOp op => _zoom maillocks (Globals.step op)
  end.
Time Import RelationNotations.
Time
Definition crash_step : relation State State unit :=
  _zoom fs FS.crash_step;; _zoom maillocks (puts (fun _ => Globals.init)).
Time
Theorem crash_step_non_err : forall s res, crash_step s res -> res <> Err.
Time Proof.
Time (unfold crash_step, and_then, puts; intros).
Time (destruct res; cbn[_zoom zoom] in *; eauto).
Time intuition eauto.
Time -
Time (apply FS.crash_step_non_err in H1; congruence).
Time -
Time (propositional; congruence).
Time Qed.
Time
Definition sem : Dynamics Op State :=
  {|
  Proc.step := step;
  Proc.crash_step := crash_step;
  Proc.finish_step := crash_step |}.
Time
Ltac
 t :=
  repeat
   match goal with
   | |- exists _ : State, _ => eexists (Build_State _ _)
   | |- exists _, _ => eexists
   | _ =>
       progress propositional
   | |- _ /\ _ => split
   | |- _ => solve [ eauto ]
   end.
Time Definition l : Layer Op.
Time
(refine
  {|
  OpState := State;
  Layer.sem := sem;
  trace_proj := fun _ => nil;
  initP := fun s => s = \226\136\133 |}; simpl; unfold puts, pure; propositional).
Time -
Time auto.
Time -
Time t.
Time -
Time t.
Time -
Time (apply crash_step_non_err in H; auto).
Time -
Time (apply crash_step_non_err in H; auto).
Time Defined.
Time End GoModel.
Time End Go.
