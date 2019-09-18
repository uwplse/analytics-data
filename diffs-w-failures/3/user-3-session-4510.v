Time From Transitions Require Import Relations.
Time From Transitions Require Import Relations.
Time From RecordUpdate Require Import RecordSet.
Time Generalizable Variables all.
Time
Definition _zoom `{Setter A C proj} T (r : relation C C T) :
  relation A A T := zoom proj (fun c => set proj (fun _ => c)) r.
Time Arguments _zoom {A} {C} proj {H} {T} r.
Time Require Import List.
Time #[global]Set Implicit Arguments.
Time #[global]Generalizable Variables all.
Time #[global]Set Printing Projections.
Time Set Warnings "-undeclared-scope".
Time Import RelationNotations.
Time Definition Event : Type := {T : Type & T}.
Time
Inductive LoopOutcome (T R : Type) : Type :=
  | ContinueOutcome : forall x : T, _
  | DoneWithOutcome : forall r : R, _.
Time Arguments ContinueOutcome {_} {_} _.
Time Arguments DoneWithOutcome {_} {_} _.
Time Section Proc.
Time Variable (Op : Type -> Type).
Time
Inductive proc : Type -> Type :=
  | Call : forall T (op : Op T), proc T
  | Ret : forall T (v : T), proc T
  | Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
  | Loop : forall T R (body : T -> proc (LoopOutcome T R)) (init : T), proc R
  | Unregister : proc unit
  | Wait : proc unit
  | Spawn : forall T (p : proc T), proc unit.
Time End Proc.
Time Arguments Call {Op} {T}.
Time Arguments Ret {Op} {T} v.
Time Arguments Loop {Op} {T} {R} _ _.
Time Arguments Spawn {Op} {_} _.
Time Arguments Err {_} {_}.
Time Arguments Unregister {_}.
Time Arguments Wait {_}.
Time
Definition Continue {Op} {T} {R} (x : T) : proc Op (LoopOutcome T R) :=
  Ret (ContinueOutcome x).
Time
Definition LoopRet {Op} {T} {R} (x : R) : proc Op (LoopOutcome T R) :=
  Ret (DoneWithOutcome x).
Time
Inductive rec_seq (Op : Type -> Type) : Type :=
  | Seq_Nil : _
  | Seq_Cons : forall (T : Type) (p : proc Op T) (ps : rec_seq Op), _.
Time Arguments Seq_Nil {Op}.
Time Arguments Seq_Cons {Op} {T}.
Time
Inductive ExecOutcome : Type :=
  | Normal : {T : Type & T} -> ExecOutcome
  | Recovered : {T : Type & T} -> ExecOutcome.
Time
Inductive proc_seq (Op : Type -> Type) (T : Type) : Type :=
  | Proc_Seq_Nil : forall v : T, _
  | Proc_Seq_Bind :
      forall (T0 : Type) (p : proc Op T0) (rx : ExecOutcome -> proc_seq Op T),
      _.
Time Arguments Proc_Seq_Nil {Op} {_}.
Time Arguments Proc_Seq_Bind {Op} {_} {_}.
Time
Fixpoint rec_seq_append Op (ps1 ps2 : rec_seq Op) :=
  match ps1 with
  | Seq_Nil => ps2
  | Seq_Cons p ps1' => Seq_Cons p (rec_seq_append ps1' ps2)
  end.
Time
Definition rec_seq_snoc Op T (ps : rec_seq Op) (p : proc Op T) :=
  rec_seq_append ps (Seq_Cons p Seq_Nil).
Time
Definition thread_pool (Op : Type -> Type) := list {T : Type & proc Op T}.
Time
Definition OpSemantics Op State := forall T, Op T -> relation State State T.
Time Definition CrashSemantics State := relation State State unit.
Time Definition FinishSemantics State := relation State State unit.
Time
Record Dynamics Op State :={step : OpSemantics Op State;
                            crash_step : CrashSemantics State;
                            finish_step : FinishSemantics State}.
Time Section Dynamics.
Time Context `(sem : Dynamics Op OpState).
Time Definition State : Type := nat * OpState.
Time
Definition lifted_crash_step : CrashSemantics State :=
  fst_lift (puts (fun x => 1));; snd_lift sem.(crash_step).
Time
Definition lifted_finish_step : FinishSemantics State :=
  fst_lift (puts (fun x => 1));; snd_lift sem.(finish_step).
Time
Definition loop1 T R (body : T -> proc Op (LoopOutcome T R)) 
  (init : T) :=
  Bind (body init)
    (fun out =>
     match out with
     | ContinueOutcome x => Loop body x
     | DoneWithOutcome r => Ret r
     end).
Time
Fixpoint exec_step {T} (p : proc Op T) {struct p} :
relation State State (proc Op T * thread_pool Op) :=
  match p with
  | Ret v => none
  | Call op => v <- snd_lift (step sem op); pure (Ret v, nil)
  | @Bind _ T0 _ p p' =>
      match
        p in (proc _ T1)
        return
          ((T1 -> proc _ T0) ->
           relation State State (proc _ T0 * thread_pool _))
      with
      | Ret v => fun p' => pure (p' v, nil)
      | _ => fun _ => vp <- exec_step p; pure (Bind (fst vp) p', snd vp)
      end p'
  | Loop b init => pure (loop1 b init, nil)
  | Unregister => fst_lift (puts pred);; pure (Ret tt, nil)
  | Wait =>
      fst_lift (such_that (fun x (_ : unit) => x = 1));; pure (Ret tt, nil)
  | @Spawn _ _ p' =>
      fst_lift (puts S);;
      pure (Ret tt, existT _ _ (Bind p' (fun _ => Unregister)) :: nil)
  end.
Time Notation proc := (proc Op).
Time Notation rec_seq := (rec_seq Op).
Time Notation proc_seq := (proc_seq Op).
Time Notation thread_pool := (thread_pool Op).
Time Notation step := sem.(step).
Time Notation crash_step := lifted_crash_step.
Time
Definition exec_pool_hd {T} (p : proc T) (ps : thread_pool) :
  relation State State thread_pool := pps <- exec_step p;
  pure (existT _ T (fst pps) :: ps ++ snd pps).
Time
Fixpoint exec_pool (ps : list {T & proc T}) :
relation State State thread_pool :=
  match ps with
  | nil => none
  | existT _ T p :: ps' =>
      exec_pool_hd p ps' + ps'_upd <- exec_pool ps';
      pure (existT _ T p :: ps'_upd)
  end.
Time
Inductive exec_pool_alt (ps1 : thread_pool) (\207\1311 : State)
(ret : Return State thread_pool) : Prop :=
  | step_atomic_valid :
      forall {T} (e1 e2 : proc T) ps2 efs \207\1312 t1 t2,
      ps1 = t1 ++ existT _ _ e1 :: t2 ->
      ps2 = t1 ++ existT _ _ e2 :: t2 ++ efs ->
      ret = Val \207\1312 ps2 ->
      exec_step e1 \207\1311 (Val \207\1312 (e2, efs)) -> exec_pool_alt ps1 \207\1311 ret
  | step_atomic_error :
      forall {T} (e1 : proc T) t1 t2,
      ps1 = t1 ++ existT _ _ e1 :: t2 ->
      ret = Err -> exec_step e1 \207\1311 Err -> exec_pool_alt ps1 \207\1311 ret.
Time
Lemma exec_pool_alt_cons_valid {T} ps1 \207\1311 \207\1312 ps2 e :
  exec_pool_alt ps1 \207\1311 (Val \207\1312 ps2) ->
  exec_pool_alt (existT _ T e :: ps1) \207\1311 (Val \207\1312 (existT _ T e :: ps2)).
Time Proof.
Time (inversion 1; [  | congruence ]).
Time subst.
Time
(inversion H2; subst; econstructor; eauto; rewrite app_comm_cons; f_equal).
Time Qed.
Time
Lemma exec_pool_alt_cons_err {T} ps1 \207\1311 e :
  exec_pool_alt ps1 \207\1311 Err -> exec_pool_alt (existT _ T e :: ps1) \207\1311 Err.
Time Proof.
Time (inversion 1; [ congruence |  ]).
Time subst.
Time (subst; econstructor; eauto; rewrite app_comm_cons; f_equal).
Time Qed.
Time
Lemma exec_pool_equiv_alt_val ps1 \207\1311 \207\1312 ps2 :
  exec_pool ps1 \207\1311 (Val \207\1312 ps2) <-> exec_pool_alt ps1 \207\1311 (Val \207\1312 ps2).
Time Proof.
Time split.
Time -
Time revert \207\1312 ps2.
Time (induction ps1 as [| [T e] ps1]; intros \207\1312 ps2).
Time *
Time (simpl).
Time (inversion 1).
Time *
Time (simpl).
Time (intros [H| H]).
Time **
Time (destruct H as ((e', efs), (?, (?, Hp)))).
Time (inversion Hp; subst).
Time (eapply (step_atomic_valid _ e e' efs nil ps1); simpl; eauto).
Time **
Time (inversion H as (ps2', (?, (?, Hpure)))).
Time (inversion Hpure; subst).
Time (eapply exec_pool_alt_cons_valid; eauto).
Time -
Time (inversion 1; subst).
Time clear H.
Time (inversion_clear H2; subst).
Time (induction t1 as [| [T' e] ps1]).
Time *
Time (simpl).
Time left.
Time (do 2 econstructor; split; eauto).
Time econstructor.
Time *
Time (simpl).
Time right.
Time (do 2 eexists; split; eauto).
Time (econstructor; eauto).
Time *
Time congruence.
Time Qed.
Time
Lemma exec_pool_equiv_alt_err ps1 \207\1311 :
  exec_pool ps1 \207\1311 Err <-> exec_pool_alt ps1 \207\1311 Err.
Time Proof.
Time split.
Time -
Time (induction ps1 as [| [T e] ps1]).
Time *
Time (simpl).
Time (inversion 1).
Time *
Time (simpl).
Time {
Time (intros [H| H]).
Time **
Time (destruct H as [?| (?, (?, (?, Hpure)))]).
Time (eapply (step_atomic_error _ e nil ps1); simpl; eauto).
Time (inversion Hpure).
Time **
Time (apply bind_pure_no_err in H).
Time (eapply exec_pool_alt_cons_err; eauto).
Time }
Time -
Time (inversion 1; subst; clear H; induction t1 as [| [T' e] ps1]).
Time *
Time congruence.
Time *
Time congruence.
Time *
Time (simpl).
Time left.
Time left.
Time eauto.
Time *
Time (simpl).
Time right.
Time left.
Time intuition eauto.
Time Qed.
Time
Definition exec_partial {T} (p : proc T) :=
  bind_star exec_pool (existT _ T p :: nil).
Time
Definition exec_halt {T} (p : proc T) : relation State State unit :=
  exec_partial p;; pure tt.
Time
Definition exec {T} (p : proc T) : relation State State {T : Type & T} :=
  ps <- exec_partial p;
  match ps with
  | existT _ _ (Ret v) :: _ => pure (existT _ _ v)
  | _ => @none _ _ {T : Type & T}
  end.
Time
Fixpoint exec_seq_partial (ps : rec_seq) : relation State State unit :=
  match ps with
  | Seq_Nil => pure tt
  | Seq_Cons p ps =>
      (exec p;; exec_seq_partial ps) + (exec_partial p;; pure tt)
  end.
Time
Fixpoint exec_seq (ps : rec_seq) : relation State State unit :=
  match ps with
  | Seq_Nil => pure tt
  | Seq_Cons p ps => exec p;; exec_seq ps
  end.
Time
Definition exec_recover1 T (rec : proc T) : relation State State unit :=
  seq_star (exec_partial rec;; crash_step);; exec rec;; pure tt.
Time
Definition exec_recover (rec : rec_seq) : relation State State unit :=
  seq_star (exec_seq_partial rec;; crash_step);; exec_seq rec.
Time
Definition exec_recover_partial (rec : rec_seq) :
  relation State State unit :=
  seq_star (exec_seq_partial rec;; crash_step);; exec_seq_partial rec.
Time
Definition exec_recover_unfold (rec : rec_seq) :
  exec_recover rec =
  (seq_star (exec_seq_partial rec;; crash_step);; exec_seq rec) := eq_refl.
Time
Definition exec_recover_partial_unfold (rec : rec_seq) :
  exec_recover_partial rec =
  (seq_star (exec_seq_partial rec;; crash_step);; exec_seq_partial rec) :=
  eq_refl.
Time
Definition rexec {T} (p : proc T) (rec : rec_seq) :=
  exec_partial p;; crash_step;; exec_recover rec.
Time
Definition rexec_unfold {T} (p : proc T) (rec : rec_seq) :
  rexec p rec = (exec_partial p;; crash_step;; exec_recover rec) := eq_refl.
Time
Definition rexec_partial {T} (p : proc T) (rec : rec_seq) :=
  exec_partial p;; crash_step;; exec_recover_partial rec.
Time
Definition rexec_seq (ps : rec_seq) (rec : rec_seq) :=
  exec_seq_partial ps;; crash_step;; exec_recover rec.
Time
Definition rexec_seq_partial (ps : rec_seq) (rec : rec_seq) :=
  exec_seq_partial ps;; crash_step;; exec_recover_partial rec.
Time
Definition rexec_seq_unfold (ps : rec_seq) (rec : rec_seq) :
  rexec_seq ps rec = (exec_seq_partial ps;; crash_step;; exec_recover rec) :=
  eq_refl.
Time
Definition exec_or_rexec {T} (p : proc T) (rec : rec_seq) :
  relation State State ExecOutcome :=
  v <- exec p; _ <- lifted_finish_step; pure (Normal v) + 
  v <- rexec p rec; _ <- fst_lift (puts (fun _ => 1));
  pure (Recovered (existT (fun T => T) _ v)).
Time
Fixpoint proc_exec_seq {T} (p : proc_seq T) (rec : rec_seq) :
relation State State _ :=
  match p with
  | Proc_Seq_Nil v => pure v
  | Proc_Seq_Bind p f => v <- exec_or_rexec p rec; proc_exec_seq (f v) rec
  end.
Time
Lemma proc_exec_seq_unfold {T} (p : proc_seq T) (rec : rec_seq) :
  proc_exec_seq p rec =
  match p with
  | Proc_Seq_Nil v => pure v
  | Proc_Seq_Bind p f => v <- exec_or_rexec p rec; proc_exec_seq (f v) rec
  end.
Time Proof.
Time (destruct p; auto).
Time Qed.
Time
Fixpoint wf_client {T} (p : proc T) :=
  match p with
  | Unregister => False
  | Wait => False
  | Loop body _ => forall t, wf_client (body t)
  | Spawn e => wf_client e
  | Call _ => True
  | Ret _ => True
  | Bind e rx => wf_client e /\ (forall x, wf_client (rx x))
  end.
Time
Fixpoint wf_client_seq {T} (p : proc_seq T) :=
  match p with
  | Proc_Seq_Nil _ => True
  | Proc_Seq_Bind p f => wf_client p /\ (forall v, wf_client_seq (f v))
  end.
Time End Dynamics.
Time Module ProcNotations.
Time Delimit Scope proc_scope with proc.
Time
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 20, p1  at level 100, p2  at level 200, right associativity) :
  proc_scope.
Time
Notation "'let!' x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 20, x pattern, p1  at level 100, p2  at level 200,
   right associativity) : proc_scope.
Time End ProcNotations.
Time
Definition LoopWhileVoid Op R (body : proc Op (LoopOutcome unit R)) :
  proc Op R := Loop (fun _ => body) tt.
