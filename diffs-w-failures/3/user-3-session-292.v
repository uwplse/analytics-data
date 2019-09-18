Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
From Classes Require Import Default.
From Transitions Require Import Relations Rewriting.
From Tactical Require Import ProofAutomation.
Import RelationNotations.
Record Layer Op :={State : Type;
                   sem : Dynamics Op State;
                   initP : State -> Prop}.
Inductive InitStatus :=
  | Initialized : _
  | InitFailed : _.
Record LayerImpl C_Op Op :={compile_op : forall `(op : Op T), proc C_Op T;
                            recover : proc C_Op unit;
                            init : proc C_Op InitStatus}.
Fixpoint compile Op C_Op `(impl : LayerImpl C_Op Op) 
T (p : proc Op T) : proc C_Op T :=
  match p with
  | Call op => impl.(compile_op) op
  | Ret v => Ret v
  | Bind p p' => Bind (impl.(compile) p) (fun v => impl.(compile) (p' v))
  end.
Fixpoint compile_seq Op C_Op `(impl : LayerImpl C_Op Op) 
R (p : proc_seq Op R) : proc_seq C_Op R :=
  match p with
  | Seq_Nil => Seq_Nil
  | Seq_Bind p p' =>
      Seq_Bind (compile impl p) (fun v => impl.(compile_seq) (p' v))
  end.
Definition compile_rec Op C_Op `(impl : LayerImpl C_Op Op) 
  R (rec : proc Op R) : proc C_Op R :=
  Bind impl.(recover) (fun _ => compile impl rec).
Definition initOutput {A} `(L : Layer Op)
  (r : relation (State L) (State L) A) (v : A) : Prop :=
  exists s1 s2, L.(initP) s1 /\ r s1 (Val s2 v).
Hint Unfold refines: relation_rewriting.
Section Layers.
Context C_Op (c_layer : Layer C_Op).
Notation CState := c_layer.(State).
Notation c_proc := (proc C_Op).
Notation c_initP := c_layer.(initP).
Notation c_sem := c_layer.(sem).
Notation c_exec := (exec c_layer.(sem)).
Notation c_exec_recover := (exec_recover c_layer.(sem)).
Notation c_output := (initOutput c_layer).
Context Op (a_layer : Layer Op).
Notation AState := a_layer.(State).
Notation a_proc := (proc Op).
Notation a_proc_seq := (proc_seq Op).
Notation a_initP := a_layer.(initP).
Notation a_sem := a_layer.(sem).
Notation a_exec_recover := (exec_recover a_layer.(sem)).
Notation a_output := (initOutput a_layer).
Definition compile_op_refines_step (impl : LayerImpl C_Op Op)
  (absr : relation AState CState unit) :=
  forall T (op : Op T),
  crash_refines absr c_sem (impl.(compile_op) op) 
    impl.(recover) (a_sem.(step) op)
    (a_sem.(crash_step) + (a_sem.(step) op;; a_sem.(crash_step))).
Definition recovery_refines_crash_step (impl : LayerImpl C_Op Op)
  (absr : relation AState CState unit) :=
  refines absr (c_sem.(crash_step);; c_exec_recover impl.(recover))
    a_sem.(crash_step).
Record LayerRefinement :={impl : LayerImpl C_Op Op;
                          absr : relation AState CState unit;
                          compile_op_ok : compile_op_refines_step impl absr;
                          recovery_noop_ok :
                           recovery_refines_crash_step impl absr;
                          init_ok :
                           (test c_initP;; c_exec impl.(init))
                           --->
                            (any (T:=unit);;
                             test a_initP;; absr;; pure Initialized) +
                            (any (T:=unit);; pure InitFailed)}.
Context (rf : LayerRefinement).
Notation compile_op := rf.(impl).(compile_op).
Notation compile_rec := (compile_rec rf.(impl)).
Notation compile_seq := (compile_seq rf.(impl)).
Notation compile := (compile rf.(impl)).
Notation recover := (recover rf.(impl)).
Opaque exec_recover.
Theorem compile_exec_ok :
  forall T (p : a_proc T),
  refines rf.(absr) (c_exec (compile p)) (exec a_sem p).
Proof.
(induction p; simpl; intros).
-
pose unfolded rf.(compile_op_ok) op fun H => hnf in H.
propositional.
-
(unfold refines; norm).
-
(unfold refines in *; norm).
left_assoc rew IHp.
(rel_congruence; norm).
rew<- H.
Qed.
Theorem crash_step_refinement :
  refines rf.(absr) (c_sem.(crash_step);; c_exec_recover recover)
    a_sem.(crash_step).
Proof.
exact rf.(recovery_noop_ok).
Qed.
Theorem rexec_rec R (rec : a_proc R) :
  refines rf.(absr) (rexec c_sem (compile rec) recover)
    (exec_crash a_sem rec).
Proof.
(unfold refines, rexec).
(induction rec; simpl; norm).
-
pose unfolded rf.(compile_op_ok) op
 fun H => red in H; unfold rexec, refines in H.
rew H0.
-
rew crash_step_refinement.
-
(Split; [ Left | Right ]).
+
rew IHrec.
+
left_assoc rew compile_exec_ok rec.
rew H.
Qed.
Theorem rexec_star_rec R (rec : a_proc R) :
  refines rf.(absr)
    (seq_star (rexec c_sem (compile rec) recover);; c_exec (compile rec))
    (a_exec_recover rec).
Proof.
(unfold refines).
rew @exec_recover_unfold.
pose unfolded rexec_rec rec fun H => red in H.
(apply simulation_seq_value in H).
left_assoc rew H.
rel_congruence.
rew compile_exec_ok.
typeclasses eauto.
Qed.
Lemma recover_ret R (rec : a_proc R) :
  refines rf.(absr)
    (_ <- c_sem.(crash_step); c_exec_recover (compile_rec rec))
    (a_sem.(crash_step);; a_exec_recover rec).
Proof.
(unfold refines).
rew @exec_recover_bind.
rew bind_star_unit.
left_assoc rew crash_step_refinement.
rel_congruence.
rew rexec_star_rec.
Qed.
Theorem compile_rexec_ok T (p : a_proc T) R (rec : a_proc R) :
  refines rf.(absr) (rexec c_sem (compile p) (compile_rec rec))
    (rexec a_sem p rec).
Proof.
(unfold refines, rexec).
(induction p; simpl; norm).
-
pose unfolded rf.(compile_op_ok) op
 fun H => hnf in H; unfold rexec, refines in H.
(match goal with
 | H:context [ c_exec (compile_op _) ] |- _ => clear H
 end).
rew @exec_recover_bind.
left_assoc rew H0.
rew bind_star_unit.
rew rexec_star_rec.
-
rew recover_ret.
-
(Split; [ Left | Right ]).
+
rew IHp.
+
left_assoc rew compile_exec_ok.
rew H.
Qed.
Theorem compile_exec_seq_ok R (p : a_proc_seq R) (rec : a_proc R) :
  refines rf.(absr) (exec_seq c_sem (compile_seq p) (compile_rec rec))
    (exec_seq a_sem p rec).
Proof.
(unfold refines).
(induction p as [| ? ? ? IH1]; do 2 rewrite exec_seq_unfold; simpl;
  [ norm |  ]).
(repeat setoid_rewrite bind_dist_r).
(repeat setoid_rewrite bind_dist_l).
(eapply or_respects_impl).
-
(left_assoc rew compile_exec_ok; repeat rel_congruence).
left_assoc rew IH1.
-
(left_assoc rew compile_rexec_ok; repeat rel_congruence).
left_assoc rew IH1.
Qed.
Theorem compile_ok :
  forall T (p : a_proc T) R (rec : a_proc R),
  crash_refines rf.(absr) c_sem (compile p) (compile_rec rec) 
    (exec a_sem p) (rexec a_sem p rec).
Proof.
(intros).
(split; [ now apply compile_exec_ok | now apply compile_rexec_ok ]).
Qed.
Definition ifInit (inited : InitStatus) A `(r : relation A A T) :
  relation A A (option T) :=
  if inited then v <- r; pure (Some v) else pure None.
Theorem complete_exec_ok :
  forall T (p : a_proc T),
  (test c_initP;; inited <- c_exec rf.(impl).(init);
   ifInit inited (c_exec (compile p)))
  --->
   (any (T:=unit);;
    test a_initP;; v <- exec a_sem p; any (T:=unit);; pure (Some v)) +
   (any (T:=unit);; pure None).
Proof.
(intros).
left_assoc rew rf.(init_ok).
(repeat rew bind_dist_r).
(simpl).
Split.
-
Left.
rel_congruence.
rel_congruence.
left_assoc rew compile_exec_ok p.
(repeat rel_congruence).
(apply to_any).
-
Right.
Qed.
Theorem complete_rexec_ok :
  forall T (p : a_proc T) R (rec : a_proc R),
  (test c_initP;; inited <- c_exec rf.(impl).(init);
   ifInit inited (rexec c_sem (compile p) (compile_rec rec)))
  --->
   (any (T:=unit);;
    test a_initP;; v <- rexec a_sem p rec; any (T:=unit);; pure (Some v)) +
   (any (T:=unit);; pure None).
Proof.
(intros).
left_assoc rew rf.(init_ok).
(repeat rew bind_dist_r).
(simpl).
