Time
Inductive LockStatus :=
  | Locked : _
  | ReadLocked : forall num : nat, _
  | Unlocked : _.
Time Inductive LockMode :=
       | Reader : _
       | Writer : _.
Time
Definition lock_acquire (m : LockMode) (s : LockStatus) :
  option LockStatus :=
  match m, s with
  | Reader, ReadLocked n => Some (ReadLocked (S n))
  | Reader, Unlocked => Some (ReadLocked 0)
  | Writer, Unlocked => Some Locked
  | _, _ => None
  end.
Time
Definition lock_release (m : LockMode) (s : LockStatus) :
  option LockStatus :=
  match m, s with
  | Reader, ReadLocked 0 => Some Unlocked
  | Reader, ReadLocked (S n) => Some (ReadLocked n)
  | Writer, Locked => Some Unlocked
  | _, _ => None
  end.
Time From Transitions Require Import Relations.
Time From iris.algebra Require Import proofmode_classes.
Time
From iris.algebra Require Import auth gmap frac agree namespace_map excl.
Time
Definition lock_available (m : LockMode) (s : LockStatus) : 
  option unit :=
  match m, s with
  | Reader, ReadLocked _ => Some tt
  | _, Unlocked => Some tt
  | _, _ => None
  end.
Time
Definition force_read_lock (s : LockStatus) : LockStatus :=
  match s with
  | ReadLocked n => ReadLocked (S n)
  | _ => ReadLocked 0
  end.
Time
Definition force_read_unlock (s : LockStatus) : LockStatus :=
  match s with
  | ReadLocked (S n) => ReadLocked n
  | _ => Unlocked
  end.
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
Time From iris.base_logic Require Import base_logic.
Time Set Default Proof Using "Type".
Time Inductive counting :=
       | Count : forall z : Z, _
       | CountBot : _.
Time #[local]Open Scope Z.
Time
Instance counting_valid : (Valid counting) :=
 (\206\187 x, match x with
       | Count _ => True
       | CountBot => False
       end).
Time
Instance counting_validN : (ValidN counting) :=
 (\206\187 n x, match x with
         | Count _ => True
         | CountBot => False
         end).
Time Instance counting_pcore : (PCore counting) := (\206\187 x, None).
Time
Instance counting_op : (Op counting) :=
 (\206\187 x y,
    match x, y with
    | Count z1, Count z2 =>
        if decide (z1 >= 0 \226\136\167 z2 >= 0) then CountBot
        else if decide ((z1 >= 0 \226\136\168 z2 >= 0) \226\136\167 z1 + z2 < 0) then CountBot
             else Count (z1 + z2)
    | _, _ => CountBot
    end).
Time Canonical Structure countingC := leibnizO counting.
Time #[local]
Ltac
 by_cases :=
  repeat <ssreflect_plugin::ssrtclintros@0>
   match goal with
   | H:counting |- _ => destruct H
   end =>//=; repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=;
   try lia.
Time Lemma counting_ra_mixin : RAMixin counting.
Time Proof.
Time (split; try apply _; try done).
Time -
Time (intros x y z).
Time rewrite /op /counting_op.
Time by_cases.
Time From stdpp Require Export namespaces.
Time From iris.base_logic.lib Require Export own.
Time From iris.base_logic.lib Require Import gen_heap.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Class leased_heapG (L V : Type) (\206\163 : gFunctors) `{Countable L} :=
 LeasedHeapG {leased_heap_heapG :> gen_heapG L V \206\163;
              leased_heap_exclG :>
               inG \206\163 (authR (optionUR (exclR (leibnizO V))));
              leased_heap_gen : namespace}.
Time Arguments leased_heap_heapG {_} {_} {_} {_} {_} _ : assert.
Time Arguments leased_heap_exclG {_} {_} {_} {_} {_} _ : assert.
Time Arguments leased_heap_gen {_} {_} {_} {_} {_} _ : assert.
Time
Class leased_heapPreG (L V : Type) (\206\163 : gFunctors) `{Countable L} :={
 leased_heap_heapPreG :> gen_heapPreG L V \206\163;
 leased_heap_exclPreG :> inG \206\163 (authR (optionUR (exclR (leibnizO V))))}.
Time
Definition leased_heap\206\163 (L V : Type) `{Countable L} : gFunctors :=
  #[ gen_heap\206\163 L V; GFunctor (authR (optionUR (exclR (leibnizO V))))].
Time
Instance subG_leased_heapPreG  {\206\163} {L} {V} `{Countable L}:
 (subG (leased_heap\206\163 L V) \206\163 \226\134\146 leased_heapPreG L V \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Definition current_gen (N : namespace) := ndot N 0.
Time Definition next_gen (N : namespace) := ndot N 1.
Time Lemma split_gen_disj N : current_gen N ## next_gen N.
Time Proof.
Time solve_ndisj.
Time Qed.
Time
Definition next_leased_heapG `{hG : leased_heapG L V \206\163} :=
  LeasedHeapG _ _ _ _ _ (@leased_heap_heapG _ _ _ _ _ hG)
    (@leased_heap_exclG _ _ _ _ _ hG) (next_gen (leased_heap_gen hG)).
Time Section definitions.
Time Context {L} {V} `{Countable L} `{hG : !leased_heapG L V \206\163}.
Time
Definition lease (l : L) (v : V) :=
  (\226\136\131 \206\179 : gname,
     meta l (current_gen (leased_heap_gen hG)) \206\179
     \226\136\151 own \206\179 (\226\151\175 Excl' (v : leibnizO V)))%I.
Time
Definition master (l : L) (v : V) :=
  (\226\136\131 \206\179 : gname,
     meta l (current_gen (leased_heap_gen hG)) \206\179
     \226\136\151 meta_token l (\226\134\145next_gen (leased_heap_gen hG))
       \226\136\151 own \206\179 (\226\151\143 Excl' (v : leibnizO V)))%I.
Time End definitions.
Time #[local]
Notation "l \226\134\166{ q } v" := (mapsto l q v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
Time #[local]Notation "l \226\134\166 v" := (mapsto l 1 v) (at level 20) : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
Time #[local]Notation "l \226\134\166 -" := (l \226\134\166{1} -)%I (at level 20) : bi_scope.
Time
Definition next_lease `{hG : leased_heapG L V \206\163} (l : L) 
  (v : V) := lease (hG:=next_leased_heapG) l v.
Time
Definition next_master `{hG : leased_heapG L V \206\163} 
  (l : L) (v : V) := master (hG:=next_leased_heapG) l v.
Time Section lease_heap.
Time Context {L} {V} `{Countable L} `{hG : !leased_heapG L V \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \206\166 : V \226\134\146 iProp \206\163.
Time Implicit Type \207\131 : gmap L V.
Time Implicit Type m : gmap L gname.
Time Implicit Types h g : gen_heapUR L V.
Time Implicit Type l : L.
Time Implicit Type v : V.
Time #[global]Instance lease_timeless  l v: (Timeless (lease l v)).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance master_timeless  l v: (Timeless (master l v)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma master_lease_agree l (v1 v2 : V) :
  master l v1 -\226\136\151 lease l v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time
(iDestruct 1 as ( \206\179m1 ) "(H\206\1791&_&Hown1)"; iDestruct 1 as ( \206\179m2 ) "(H\206\1792&Hown2)").
Time iDestruct (meta_agree with "H\206\1791 H\206\1792") as % ->.
Time iDestruct (own_valid_2 with "Hown1 Hown2") as "H".
Time iDestruct "H" as % [<-%leibniz_equiv%Excl_included _]%auth_both_valid.
Time done.
Time Qed.
Time
Lemma meta_lease_init N l (\206\179 : gname) :
  meta_token l (\226\134\145N) ==\226\136\151 meta l (current_gen N) \206\179 \226\136\151 meta_token l (\226\134\145next_gen N).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (union_difference_L (\226\134\145next_gen N) (\226\134\145N)) ; last  by solve_ndisj).
Time iIntros "H".
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (meta_token_union with "H") as
 "($&?)" ; first  set_solver).
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op.
Time by_cases.
Time
by <ssreflect_plugin::ssrtclseq@0> iMod
 (meta_set _ _ \206\179 (current_gen N) with "[$]") as "$" ; first  solve_ndisj.
Time Qed.
Time Lemma master_next l v : master l v ==\226\136\151 next_master l v \226\136\151 next_lease l v.
Time Proof.
Time iDestruct 1 as ( \206\179 ) "(H\206\179&Hrest&Hown)".
Time
iMod (own_alloc (\226\151\143 Excl' (v : leibnizO V) \226\139\133 \226\151\175 Excl' (v : leibnizO V))) as (
 \206\179' ) "[H1 H2]".
Time {
Time (apply auth_both_valid; split; eauto).
Time econstructor.
Time }
Time iMod (meta_lease_init _ _ \206\179' with "Hrest") as "(#Hset&Hrest)".
Time iModIntro.
Time f_equal.
Time (iSplitL "Hrest H1"; by iExists _; iFrame).
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op /valid.
Time by_cases.
Time Qed.
Time Qed.
Time Canonical Structure countingR := discreteR counting counting_ra_mixin.
Time #[global]Instance counting_cmra_discrete : (CmraDiscrete countingR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma counting_op' (x y : countingR) : x \226\139\133 y = counting_op x y.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_valid' (x : countingR) : \226\156\147 x \226\134\148 counting_valid x.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_validN' n (x : countingR) : \226\156\147{n} x \226\134\148 counting_validN n x.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance is_op_counting  z:
 (z >= 0 \226\134\146 IsOp' (Count z) (Count (z + 1)) (Count (- 1))).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp counting_op' =>?).
Time rewrite //=.
Time by_cases.
Time
Lemma master_lease_alloc l v : meta_token l \226\138\164 ==\226\136\151 master l v \226\136\151 lease l v.
Time Proof.
Time iIntros "H".
Time
iMod (own_alloc (\226\151\143 Excl' (v : leibnizO V) \226\139\133 \226\151\175 Excl' (v : leibnizO V))) as ( \206\179
 ) "[H1 H2]".
Time {
Time (apply auth_both_valid; split; eauto).
Time f_equal.
Time lia.
Time econstructor.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (union_difference_L (\226\134\145leased_heap_gen hG) \226\138\164) ; last  by solve_ndisj).
Time Qed.
Time #[global]
Instance is_op_counting'  (n : nat):
 (IsOp' (Count n) (Count (S n)) (Count (- 1))).
Time Proof.
Time rewrite /IsOp' /IsOp counting_op' //=.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (meta_token_union with "H") as
 "(H&_)" ; first  set_solver).
Time by_cases.
Time f_equal.
Time lia.
Time Qed.
Time #[global]Instance counting_id_free  (z : counting): (IdFree z).
Time Proof.
Time (intros y).
Time rewrite counting_op' counting_validN'.
Time by_cases.
Time iMod (meta_lease_init _ _ \206\179 with "H") as "(#Hset&Hrest)".
Time (destruct y; by_cases; intros _; inversion 1).
Time iModIntro.
Time lia.
Time (iSplitL "Hrest H1"; by iExists _; iFrame).
Time Qed.
Time #[global]Instance counting_full_exclusive : (Exclusive (Count 0)).
Time Proof.
Time (intros y).
Time rewrite counting_validN' counting_op'.
Time (<ssreflect_plugin::ssrtclintros@0> destruct y =>//=; by_cases).
Time Qed.
Time Qed.
Time
Lemma big_sepM_master_lease_alloc \207\131 :
  ([\226\136\151 map] l\226\134\166v \226\136\136 \207\131, meta_token l \226\138\164)
  ==\226\136\151 [\226\136\151 map] l\226\134\166v \226\136\136 \207\131, master l v \226\136\151 lease l v.
Time Proof.
Time iIntros "H".
Time (iApply (big_opM_forall (\206\187 P Q, P ==\226\136\151 Q)); auto using bupd_intro).
Time {
Time (intros P1 P2 HP Q1 Q2 HQ).
Time by rewrite HP HQ -bupd_sep.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  by eauto).
Time (intros; by iApply master_lease_alloc).
Time Qed.
Time
Lemma master_lease_update l v v0 v' :
  master l v -\226\136\151 lease l v0 ==\226\136\151 master l v' \226\136\151 lease l v'.
Time Proof.
Time
(iDestruct 1 as ( \206\179m1 ) "(H\206\1791&Hrest&Hown1)"; iDestruct 1 as ( \206\179m2 )
  "(H\206\1792&Hown2)").
Time iDestruct (meta_agree with "H\206\1791 H\206\1792") as % ->.
Time
iMod
 (own_update_2 _ _ _ (\226\151\143 Excl' (v' : leibnizO V) \226\139\133 \226\151\175 Excl' (v' : leibnizO V))
 with "Hown1 Hown2") as "[Hown1 Hown2]".
Time {
Time by apply auth_update, option_local_update, exclusive_local_update.
Time }
Time iModIntro.
Time (iSplitL "H\206\1791 Hrest Hown1"; iExists _; iFrame).
Time Qed.
Time
Lemma leased_heap_alloc \207\131 l v :
  \207\131 !! l = None
  \226\134\146 gen_heap_ctx \207\131
    ==\226\136\151 gen_heap_ctx (<[l:=v]> \207\131) \226\136\151 l \226\134\166 v \226\136\151 master l v \226\136\151 lease l v.
Time Proof.
Time iIntros ( H\207\131l ) "H".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (gen_heap_alloc \207\131 l v with "H") as
 "($&$&H)" ; first  done).
Time by iApply master_lease_alloc.
Time Qed.
Time End lease_heap.
Time
Lemma heap_init_to_bigOp `{hG : leased_heapG L V \206\163} 
  (\207\131 : gmap L V) :
  own (i:=@gen_heap_inG _ _ _ _ _ (leased_heap_heapG hG))
    (gen_heap_name (leased_heap_heapG hG)) (\226\151\175 to_gen_heap \207\131)
  -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 \207\131, i \226\134\166 v.
Time Proof.
Time (induction \207\131 as [| ? ? ? ? IH] using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time
iAssert
 (own (i:=@gen_heap_inG _ _ _ _ _ (leased_heap_heapG hG))
    (gen_heap_name (leased_heap_heapG hG)) (\226\151\175 to_gen_heap m) \226\136\151 
  i \226\134\166 x)%I with "[Hown]" as "[Hrest $]".
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite to_gen_heap_insert
 insert_singleton_op ; last  by apply lookup_to_gen_heap_None).
Time rewrite auth_frag_op.
Time iDestruct "Hown" as "(?&?)".
Time iFrame.
Time }
Time by iApply IH.
Time Qed.
Time
Lemma leased_heap_strong_init `{H : leased_heapPreG L V \206\163} 
  \207\131 :
  (|==> \226\136\131 (H0 : leased_heapG L V \206\163) (Hpf : @gen_heap_inG _ _ _ _ _
                                             (leased_heap_heapG H0) =
                                           gen_heap_preG_inG),
          gen_heap_ctx \207\131 \226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, i \226\134\166 v \226\136\151 master i v \226\136\151 lease i v))%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \226\136\133)) as ( \206\179 ) "Hg".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iMod (own_alloc (\226\151\143 to_gen_meta \226\136\133)) as ( \206\179m ) "Hm".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_meta_valid {}.
Time }
Time (set (hG := GenHeapG L V \206\163 _ _ _ _ _ \206\179 \206\179m)).
Time (set (hL := LeasedHeapG L V \206\163 _ _ hG _ (1%positive :: nil))).
Time iAssert (gen_heap_ctx (hG:=hG) \226\136\133) with "[-]" as "H".
Time {
Time iExists \226\136\133.
Time iFrame.
Time eauto.
Time }
Time iMod (gen_heap_alloc_gen \226\136\133 \207\131 with "H") as "(Hctx&Hheap&Hmeta)".
Time {
Time (apply map_disjoint_empty_r).
Time }
Time rewrite right_id_L.
Time iMod (big_sepM_master_lease_alloc \207\131 with "Hmeta").
Time iModIntro.
Time iExists hL , eq_refl.
Time iFrame.
Time iApply big_sepM_sep.
Time iFrame.
Time Qed.
