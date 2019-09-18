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
Split.
-
Left.
rel_congruence.
rel_congruence.
left_assoc rew compile_rexec_ok.
(repeat rel_congruence).
(apply to_any).
-
Right.
Qed.
Theorem complete_exec_seq_ok_tests :
  forall R (p : a_proc_seq R) (rec : a_proc R),
  (test c_initP;; inited <- c_exec rf.(impl).(init);
   ifInit inited (exec_seq c_sem (compile_seq p) (compile_rec rec)))
  --->
   (any (T:=unit);;
    test a_initP;; v <- exec_seq a_sem p rec; any (T:=unit);; pure (Some v)) +
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
left_assoc rew compile_exec_seq_ok.
(repeat rel_congruence).
(apply to_any).
-
Right.
Qed.
Theorem complete_exec_seq_ok_unfolded R (p : a_proc_seq R) 
  (rec : a_proc R) (cs1 cs2 : CState) mv :
  c_initP cs1 ->
  (inited <- c_exec rf.(impl).(init);
   match inited with
   | InitFailed => pure None
   | Initialized => v <- exec_seq c_sem (compile_seq p) (compile_rec rec);
       pure (Some v)
   end) cs1 (Val cs2 mv) ->
  match mv with
  | None => True
  | Some v =>
      exists as1 as2, a_initP as1 /\ (exec_seq a_sem p rec) as1 (Val as2 v)
  end.
Proof.
(intros).
(pose proof (complete_exec_seq_ok_tests p rec)).
(unfold ifInit in H1).
(edestruct (H1 cs1 (Val cs2 mv))).
{
exists tt,cs1.
(split; [ firstorder |  ]).
(destruct H0 as (i, (cs1', (?, ?)))).
exists i,cs1'.
(split; intuition).
}
Admitted.
Theorem complete_exec_seq_ok R (p : a_proc_seq R) 
  (rec : a_proc R) v :
  c_output
    (inited <- c_exec rf.(impl).(init);
     match inited with
     | InitFailed => pure None
     | Initialized => v <- exec_seq c_sem (compile_seq p) (compile_rec rec);
         pure (Some v)
     end) (Some v) -> a_output (exec_seq a_sem p rec) v.
Proof.
(unfold c_output, a_output).
(intros (s1, (s2, (?, ?)))).
(eapply complete_exec_seq_ok_unfolded with (mv := Some v); eauto).
Qed.
End Layers.
Coercion impl : LayerRefinement >-> LayerImpl.
Coercion sem : Layer >-> Dynamics.
Definition layer_impl_compose Op1 Op2 Op3 (impl1 : LayerImpl Op1 Op2)
  (impl2 : LayerImpl Op2 Op3) : LayerImpl Op1 Op3.
Proof.
refine
 {|
 compile_op := fun T op => compile impl1 (impl2.(compile_op) op);
 recover := Bind impl1.(recover)
              (fun _ : unit => compile impl1 impl2.(recover));
 init := Bind impl1.(init)
           (fun inited =>
            if inited then compile impl1 impl2.(init) else Ret InitFailed) |}.
Defined.
Lemma compose_compile_op :
  forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
    (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3)
    (rf1 : LayerRefinement l1 l2) (rf2 : LayerRefinement l2 l3),
  compile_op_refines_step l1 l3 (layer_impl_compose rf1 rf2)
    (_ <- rf2.(absr); rf1.(absr)).
Proof.
(intros Op1 l1 Op2 l2 Op3 l3 rf1 rf2).
(red; unfold layer_impl_compose; simpl).
(split; simpl; unfold refines; norm).
-
rew compile_exec_ok rf1.
pose unfolded compile_op_ok rf2 _ op fun H => hnf in H.
left_assoc rew H.
-
rew compile_rexec_ok rf1.
pose unfolded compile_op_ok rf2 _ op fun H => hnf in H.
left_assoc rew H0.
Qed.
Lemma compile_recovery_crash_step :
  forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
    (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3)
    (rf1 : LayerRefinement l1 l2) (rf2 : LayerRefinement l2 l3),
  recovery_refines_crash_step l1 l3 (layer_impl_compose rf1 rf2)
    (_ <- rf2.(absr); rf1.(absr)).
Proof.
(intros Op1 l1 Op2 l2 Op3 l3 rf1 rf2).
(red; unfold refines, layer_impl_compose; simpl; norm).
rew @exec_recover_bind.
rew bind_star_unit.
pose unfolded crash_step_refinement rf1 fun H => unfold refines in H.
setoid_rewrite  <- bind_assoc at 3.
setoid_rewrite  <- bind_assoc at 2.
rew H.
rew rexec_star_rec rf1.
left_assoc rew crash_step_refinement rf2.
Qed.
Lemma compile_init_ok :
  forall (Op1 : Type -> Type) (l1 : Layer Op1) (Op2 : Type -> Type)
    (l2 : Layer Op2) (Op3 : Type -> Type) (l3 : Layer Op3)
    (rf1 : LayerRefinement l1 l2) (rf2 : LayerRefinement l2 l3),
  _ <- test l1.(initP);
  exec l1 (layer_impl_compose rf1 rf2).(init)
  --->
   _ <- any (T:=unit); _ <- test l3.(initP);
   _ <- _ <- rf2.(absr);
            rf1.(absr); pure Initialized + _ <- any (T:=unit);
   pure InitFailed.
Proof.
(intros Op1 l1 Op2 l2 Op3 l3 rf1 rf2).
(unfold layer_impl_compose; simpl).
(rewrite <- bind_assoc).
rew rf1.(init_ok).
Split.
-
rew compile_exec_ok rf1.
setoid_rewrite  <- bind_assoc at 2.
rew rf2.(init_ok).
(repeat setoid_rewrite bind_dist_r || setoid_rewrite bind_dist_l; norm).
left_assoc rew any_idem.
Split.
+
Left.
+
Right.
(rewrite <- bind_assoc).
rel_congruence.
(apply to_any).
-
Right.
Qed.
Definition refinement_transitive Op1 (l1 : Layer Op1) 
  Op2 (l2 : Layer Op2) Op3 (l3 : Layer Op3) (rf1 : LayerRefinement l1 l2)
  (rf2 : LayerRefinement l2 l3) : LayerRefinement l1 l3.
Proof.
refine
 {|
 impl := layer_impl_compose rf1.(impl) rf2.(impl);
 absr := rf2.(absr);; rf1.(absr) |}.
-
(apply compose_compile_op).
-
(apply compile_recovery_crash_step).
-
(apply compile_init_ok).
Defined.
