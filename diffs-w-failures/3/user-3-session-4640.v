Time From Coq Require Export List.
Time From stdpp Require Import base.
Time From Transitions Require Import Relations Rewriting.
Time From Coq Require Export Omega.
Time From RecordUpdate Require Import RecordUpdate.
Time From Tactical Require Import ProofAutomation.
Time From Transitions Require Import Relations.
Time Require Import Spec.Proc.
Time From Classes Require Export Classes.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time From iris.base_logic.lib Require Export fancy_updates.
Time From Transitions Require Export Relations.
Time Require Export Tactical.ProofAutomation.
Time Require Export Spec.Proc.
Time Require Export Spec.ProcTheorems.
Time Require Export Spec.Layer.
Time Export ProcNotations.
Time From iris.proofmode Require Export tactics.
Time From Armada Require Import Helpers.RecordZoom.
Time From Armada Require Import Spec.Proc.
Time From Armada Require Import Spec.InjectOp.
Time From Armada Require Import Spec.Layer.
Time From Armada.Goose Require Export Machine Heap Filesys Globals.
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
Time From iris.program_logic Require weakestpre.
Time From iris.proofmode Require Import base tactics classes.
Time Set Default Proof Using "Type".
Time Unset Implicit Arguments.
Time Import uPred.
Time
Definition reducible {OpT} {T} {\206\155} (e : proc OpT T) 
  (\207\131 : State \206\155) := \226\136\131 e' \207\131' efs, exec_step \206\155.(sem) e \207\131 (Val \207\131' (e', efs)).
Time
Definition non_errorable {OpT} {T} {\206\155} (e : proc OpT T) 
  (\207\131 : State \206\155) := \194\172 exec_step \206\155.(sem) e \207\131 Err.
Time
Definition to_val {OpT} {T} (e : proc OpT T) : option T :=
  match e in (proc _ T0) return (option T0) with
  | @Ret _ T0 v => Some v
  | @Call _ T0 _ | @Bind _ T0 _ _ _ | @Loop _ T0 _ _ _ => None
  | @Unregister _ => None
  | @Wait _ => None
  | @Spawn _ _ _ => None
  end.
Time Definition of_val {OpT} {T} (v : T) : proc OpT T := Ret v.
Time Lemma to_of_val {OpT} {T} (v : T) : to_val (@of_val OpT _ v) = Some v.
Time Proof.
Time auto.
Time Qed.
Time
Lemma of_to_val {OpT} {T} (e : proc OpT T) (v : T) :
  to_val e = Some v \226\134\146 of_val v = e.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct e =>//=).
Time rewrite /of_val //=.
Time congruence.
Time Qed.
Time
Lemma val_non_errorable {OpT} {T} {\206\155} (e : proc OpT T) 
  \207\131 v : to_val e = Some v \226\134\146 @non_errorable _ _ \206\155 e \207\131.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct e =>//= _ Hexec).
Time (inversion Hexec).
Time Qed.
Time
Class IntoVal {OpT} {T} (e : proc OpT T) (v : T) :=
    into_val : of_val v = e.
Time
Definition irreducible {OpT} {T} {\206\155} (e : proc OpT T) 
  (\207\131 : State \206\155) := is_Some (to_val e) \226\136\168 exec_step \206\155.(sem) e \207\131 Err.
Time Inductive atomicity :=
       | StronglyAtomic : _
       | WeaklyAtomic : _.
Time
Class Atomic {OpT} {T} \206\155 (a : atomicity) (e : proc OpT T) : Prop :=
    atomic :
      forall \207\131 e' \207\131' efs,
      exec_step \206\155.(sem) e \207\131 (Val \207\131' (e', efs))
      \226\134\146 match a with
        | WeaklyAtomic => irreducible e' \207\131'
        | _ => is_Some (to_val e')
        end.
Time Inductive stuckness :=
       | NotStuck : _
       | MaybeStuck : _.
Time
Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Time Instance stuckness_le : (SqSubsetEq stuckness) := stuckness_leb.
Time Instance stuckness_le_po : (PreOrder stuckness_le).
Time Proof.
Time (split; by repeat intros []).
Time Qed.
Time
Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  match s with
  | MaybeStuck => StronglyAtomic
  | _ => WeaklyAtomic
  end.
Time
Class LanguageCtx {OpT : Type \226\134\146 Type} {T1} {T2} \206\155
(K : proc OpT T1 \226\134\146 proc OpT T2) :={fill_not_val :
                                    forall e : proc OpT T1,
                                    to_val e = None \226\134\146 to_val (K e) = None;
                                   fill_step_valid :
                                    forall e1 \207\1311 e2 \207\1312 efs,
                                    exec_step \206\155.(sem) e1 \207\1311
                                      (Val \207\1312 (e2, efs))
                                    \226\134\146 exec_step \206\155.(sem) 
                                        (K e1) \207\1311 
                                        (Val \207\1312 (K e2, efs));
                                   fill_step_err :
                                    forall e1 \207\1311,
                                    exec_step \206\155.(sem) e1 \207\1311 Err
                                    \226\134\146 exec_step \206\155.(sem) (K e1) \207\1311 Err;
                                   fill_step_inv_valid :
                                    forall e1' \207\1311 e2 \207\1312 efs,
                                    to_val e1' = None
                                    \226\134\146 exec_step \206\155.(sem) 
                                        (K e1') \207\1311 
                                        (Val \207\1312 (e2, efs))
                                      \226\134\146 \226\136\131 e2',
                                          e2 = K e2'
                                          \226\136\167 exec_step 
                                              \206\155.(sem) e1' \207\1311
                                              (Val \207\1312 (e2', efs));
                                   fill_step_inv_err :
                                    forall e1' \207\1311,
                                    to_val e1' = None
                                    \226\134\146 exec_step \206\155.(sem) (K e1') \207\1311 Err
                                      \226\134\146 exec_step \206\155.(sem) e1' \207\1311 Err}.
Time
Lemma reducible_fill {OpT} {T1} {T2} K `{LanguageCtx OpT T1 T2 \206\155 K} 
  e (\207\131 : State \206\155) : to_val e = None \226\134\146 reducible (K e) \207\131 \226\134\146 reducible e \207\131.
Time Proof.
Time (intros ? (e', (\207\131', (efs, Hstep))); unfold reducible).
Time (apply fill_step_inv_valid in Hstep as (e2', (_, Hstep)); eauto).
Time Qed.
Time
Lemma non_errorable_fill_inv {OpT} {T1} {T2} K `{LanguageCtx OpT T1 T2 \206\155 K} 
  e (\207\131 : State \206\155) :
  to_val e = None \226\134\146 non_errorable (K e) \207\131 \226\134\146 non_errorable e \207\131.
Time Proof.
Time (intros ? Hnon Hstep; unfold non_errorable).
Time (eapply Hnon).
Time (apply fill_step_err; eauto).
Time Qed.
Time
Lemma non_errorable_fill {OpT} {T1} {T2} K `{LanguageCtx OpT T1 T2 \206\155 K} 
  e (\207\131 : State \206\155) :
  to_val e = None \226\134\146 non_errorable e \207\131 \226\134\146 non_errorable (K e) \207\131.
Time Proof.
Time (intros ? Hnon Hstep; unfold non_errorable).
Time (eapply Hnon).
Time (apply fill_step_inv_err; eauto).
Time Qed.
Time
Class irisG' (OpT : Type -> Type) (\206\155state : Type) (\206\163 : gFunctors) :=
 IrisG {iris_invG :> invG \206\163; state_interp : \206\155state \226\134\146 iProp \206\163}.
Time Notation irisG OpT \206\155 \206\163:= (irisG' OpT (State \206\155) \206\163).
Time #[global]Opaque iris_invG.
Time
Definition wp_pre {OpT} `{\206\155 : Layer OpT} `{irisG OpT \206\155 \206\163} 
  (s : stuckness)
  (wp : ofe_funC (\206\187 T, coPset -d> proc OpT T -d> (T -d> iProp \206\163) -d> iProp \206\163))
  : ofe_funC (\206\187 T, coPset -d> proc OpT T -d> (T -d> iProp \206\163) -d> iProp \206\163) :=
  \206\187 T E e1 \206\166,
    match to_val e1 with
    | Some v => |={E}=> \206\166 v
    | None =>
        \226\136\128 \207\1311,
          state_interp \207\1311
          ={E,\226\136\133}=\226\136\151 \226\140\156match s with
                    | NotStuck => non_errorable e1 \207\1311
                    | _ => True
                    end\226\140\157
                   \226\136\151 (\226\136\128 e2 \207\1312 efs,
                        \226\140\156exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2, efs))\226\140\157
                        ={\226\136\133,\226\136\133,E}\226\150\183=\226\136\151 state_interp \207\1312
                                    \226\136\151 wp T E e2 \206\166
                                      \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, 
                                         wp (projT1 ef) \226\138\164 
                                           (projT2 ef) 
                                           (\206\187 _, True)))
    end%I.
