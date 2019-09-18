Require Import Spec.Proc.
Require Import Spec.Proc Spec.ProcTheorems.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.
Require Import Tactical.Propositional.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Helpers.RelationTheorems.
Import RelationNotations.
Record SpecProps T R State :={pre : Prop;
                              post : State -> T -> Prop;
                              alternate : State -> R -> Prop}.
Require Import Spec.ProcTheorems.
Require Import Tactical.ProofAutomation.
Import RelationNotations.
Section Dynamics.
Context `(sem : Dynamics Op State).
Notation proc := (proc Op).
Notation step := sem.(step).
Notation exec := (exec sem).
Notation crash_step := sem.(crash_step).
Notation exec_crash := (exec_crash sem).
Definition precondition T := forall post : T -> State -> Prop, State -> Prop.
Record WPSetup :={op_wp : forall T, Op T -> precondition T;
                  op_wp_ok :
                   forall T (op : Op T) post s,
                   op_wp op post s ->
                   forall s' v, step op s s' v -> post v s'}.
Definition Specification T R State := State -> SpecProps T R State.
Definition spec_exec T R State (spec : Specification T R State) :
  relation State State T :=
  fun s s' r => (spec s).(pre) -> (spec s).(post) s' r.
Definition spec_aexec T R State (spec : Specification T R State) :
  relation State State R :=
  fun s s' r => (spec s).(pre) -> (spec s).(alternate) s' r.
Definition spec_impl `(spec1 : Specification T R State)
  `(spec2 : Specification T R State) :=
  forall s,
  (spec2 s).(pre) ->
  (spec1 s).(pre) /\
  (forall s' v, (spec1 s).(post) s' v -> (spec2 s).(post) s' v) /\
  (forall s' rv, (spec1 s).(alternate) s' rv -> (spec2 s).(alternate) s' rv).
Require Import Spec.Abstraction.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Tactical.ProofAutomation.
Import RelationNotations.
Record Layer Op :={State : Type;
                   sem : Dynamics Op State;
                   initP : State -> Prop}.
Ltac
 cleanup :=
  simpl in *; unfold pure, and_then, test, rel_or in *; propositional.
Context (wp : WPSetup).
Fixpoint precond T (p : proc T) : precondition T :=
  fun post =>
  match p with
  | Ret v => post v
  | Call op => wp.(op_wp) op post
  | Bind p rx => precond p (fun v s' => precond (rx v) post s')
  end.
Theorem wp_ok :
  forall T (p : proc T) (post : T -> State -> Prop),
  forall s, precond p post s -> forall s' v, exec p s s' v -> post v s'.
Proof.
(intros Hop_wp).
(induction p; cleanup; eauto).
Definition op_spec `(sem : Dynamics Op State) `(op : Op T) :
  Specification T unit State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => sem.(step) op state state' v;
  alternate := fun state' r =>
               r = tt /\
               (crash_step sem state state' r \/
                (exists smid v,
                   sem.(step) op state smid v /\ crash_step sem smid state' r)) |}.
Section Hoare.
Context `(sem : Dynamics Op State).
Notation proc := (proc Op).
Notation exec := (exec sem).
Notation exec_crash := (exec_crash sem).
Notation crash_step := sem.(crash_step).
Notation rexec := (rexec sem).
Definition proc_rspec T R (p : proc T) (rec : proc R)
  (spec : Specification T R State) :=
  exec p ---> spec_exec spec /\ rexec p rec ---> spec_aexec spec.
Inductive InitStatus :=
  | Initialized : _
  | InitFailed : _.
Record LayerImpl C_Op Op :={compile_op : forall `(op : Op T), proc C_Op T;
                            recover : proc C_Op unit;
                            init : proc C_Op InitStatus}.
Definition proc_hspec T (p : proc T) (spec : Specification T unit State) :=
  exec p ---> spec_exec spec /\ exec_crash p ---> spec_aexec spec.
Theorem proc_rspec_expand T R (p : proc T) (rec : proc R)
  (spec : Specification T R State) :
  proc_rspec p rec spec <->
  (forall s,
   (spec s).(pre) ->
   (forall s' v, exec p s s' v -> (spec s).(post) s' v) /\
   (forall s' rv, rexec p rec s s' rv -> (spec s).(alternate) s' rv)).
Proof.
(unfold proc_rspec, rimpl, spec_exec, spec_aexec; split; intros).
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
-
(eapply wp.(op_wp_ok) in H; eauto).
-
(eapply IHp in H1; eauto; cleanup).
-
intuition eauto  10.
Definition compile_rec Op C_Op `(impl : LayerImpl C_Op Op) 
  R (rec : proc Op R) : proc C_Op R :=
  Bind impl.(recover) (fun _ => compile impl rec).
Definition initOutput {A} `(L : Layer Op)
  (r : relation (State L) (State L) A) (v : A) : Prop :=
  exists s1 s2, L.(initP) s1 /\ r s1 s2 v.
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
(eapply H in H1; eauto).
Qed.
Definition crashpre := forall crash : State -> Prop, State -> Prop.
Definition after_crash (crash : State -> Prop) : State -> Prop :=
  fun s => forall s', crash_step s s' tt -> crash s'.
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
Theorem after_crash_unfold :
  forall crash s,
  after_crash crash s -> forall s' u, crash_step s s' u -> crash s'.
Proof.
(destruct u; firstorder).
Qed.
Ltac
 after_crash :=
  try
   match goal with
   | H:after_crash ?crash _
     |- _ => eauto using (@after_crash_unfold crash _ H)
   end.
Fixpoint crashcond T (p : proc T) : crashpre :=
  fun crash s =>
  match p with
  | Ret v => after_crash crash s
  | Call op =>
      after_crash crash s /\ wp.(op_wp) op (fun v s => after_crash crash s) s
  | Bind p rx =>
      crashcond p crash s /\
      precond p (fun v s' => crashcond (rx v) crash s') s
  end.
-
(split; intros x y ?).
(specialize (H x); intuition eauto).
(specialize (H x); intuition eauto).
Record LayerRefinement :={impl : LayerImpl C_Op Op;
                          absr : relation AState CState unit;
                          compile_op_ok : compile_op_refines_step impl absr;
                          recovery_noop_ok :
                           recovery_refines_crash_step impl absr;
                          init_ok :
                           test c_initP;; c_exec impl.(init)
                           --->
                            (any (T:=unit);;
                             test a_initP;; absr;; pure Initialized) +
                            (any (T:=unit);; pure InitFailed)}.
Theorem wp_crash_ok T (p : proc T) (crash : State -> Prop) :
  forall s,
  crashcond p crash s -> forall s' v, exec_crash p s s' v -> crash s'.
Proof.
(induction p; cleanup; after_crash).
Qed.
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
Theorem proc_hspec_expand T (p : proc T) (spec : Specification T unit State)
  :
  proc_hspec p spec <->
  (forall s,
   (spec s).(pre) ->
   (forall s' v, exec p s s' v -> (spec s).(post) s' v) /\
   (forall s' rv, exec_crash p s s' rv -> (spec s).(alternate) s' rv)).
Proof.
(unfold proc_hspec, rimpl, spec_exec, spec_aexec; split; intros).
-
intuition eauto  10.
Proof.
(induction p; simpl; intros).
-
pose unfolded rf.(compile_op_ok) op fun H => hnf in H.
-
(repeat
  match goal with
  | H:_ \/ _ |- _ => destruct H; propositional; after_crash
  end).
-
(split; intros x y ?).
propositional.
-
(unfold refines; norm).
(eapply wp.(op_wp_ok) in H1; eauto; after_crash).
(specialize (H x); intuition eauto).
(specialize (H x); intuition eauto).
-
(repeat
  match goal with
  | H:_ \/ _ |- _ => destruct H; propositional; after_crash
  end).
Qed.
-
(unfold refines in *; norm).
+
(eapply IHp; eauto).
+
(eapply wp_ok in H2; eauto).
Theorem proc_rspec_impl `(spec1 : Specification T R State)
  `(spec2 : Specification T R State) p rec :
  spec_impl spec1 spec2 -> proc_rspec p rec spec1 -> proc_rspec p rec spec2.
Proof.
(unfold spec_impl; intros).
(pose proof (proj1 (proc_rspec_expand _ _ _) H0); clear H0).
(apply proc_rspec_expand; intros).
(specialize (H s); propositional).
Qed.
(specialize (H1 s); propositional).
eauto  10.
End Dynamics.
Qed.
Arguments precondition State T : clear implicits.
Arguments crashpre State : clear implicits.
Theorem proc_hspec_impl `(spec1 : Specification T unit State)
  `(spec2 : Specification T unit State) p :
  spec_impl spec1 spec2 -> proc_hspec p spec1 -> proc_hspec p spec2.
Proof.
(unfold spec_impl; intros).
(pose proof (proj1 (proc_hspec_expand _ _) H0); clear H0).
(apply proc_hspec_expand; intros).
firstorder.
Qed.
Theorem proc_rspec_exec_equiv T `(spec : Specification T R State)
  (p p' : proc T) `(rec : proc R) :
  exec_equiv sem p p' -> proc_rspec p' rec spec -> proc_rspec p rec spec.
Proof.
(unfold proc_rspec).
(intros ->; auto).
left_assoc rew IHp.
Qed.
Theorem proc_hspec_exec_equiv T `(spec : Specification T unit State)
  (p p' : proc T) :
  exec_equiv sem p p' -> proc_hspec p' spec -> proc_hspec p spec.
Proof.
(unfold proc_hspec).
(intros ->; auto).
Qed.
Theorem proc_rspec_rx T T' R `(spec : Specification T R State) 
  `(p : proc T) `(rec : proc R) `(rx : T -> proc T')
  `(spec' : Specification T' R State) :
  proc_rspec p rec spec ->
  (forall state,
   pre (spec' state) ->
   pre (spec state) /\
   (forall r,
    proc_rspec (rx r) rec
      (fun state' =>
       {|
       pre := post (spec state) state' r;
       post := fun (state'' : State) r => post (spec' state) state'' r;
       alternate := fun (state'' : State) r =>
                    alternate (spec' state) state'' r |})) /\
   (forall (r : R) (state' : State),
    alternate (spec state) state' r -> alternate (spec' state) state' r)) ->
  proc_rspec (Bind p rx) rec spec'.
Proof.
(unfold proc_rspec at 3).
(intros (Hp_ok, Hp_rec) Hrx).
split.
-
(simpl; rew Hp_ok).
(intros state state' t' (t, (state_mid, (Hspec_mid, Hexec_mid))) Hpre').
specialize (Hrx _ Hpre') as (Hpre, (Hok, Hrec)).
specialize (Hok t).
(rewrite proc_rspec_expand in Hok).
(destruct (Hok state_mid) as (Hrx_ok, Hrx_rec); simpl; eauto).
-
(rewrite rexec_unfold).
(rewrite rexec_unfold in Hp_rec).
(simpl).
(rewrite bind_dist_r).
(apply rel_or_elim).
+
(rewrite Hp_rec; auto).
(intros state state' r Hspec_aexec Hpre').
(specialize (Hrx _ Hpre') as (Hpre, (?, Hrec)); eauto).
+
(rewrite bind_assoc, Hp_ok).
(intros state state' t' (t, (state_mid, (Hspec_mid, Hcrash_mid))) Hpre').
specialize (Hrx _ Hpre') as (Hpre, (Hok, Hrec)).
specialize (Hok t).
(rewrite proc_rspec_expand in Hok).
(destruct (Hok state_mid) as (Hrx_ok, Hrx_rec); simpl; eauto).
Qed.
Theorem proc_hspec_rx T T' `(spec : Specification T unit State) 
  `(p : proc T) `(rx : T -> proc T') `(spec' : Specification T' unit State) :
  proc_hspec p spec ->
  (forall state,
   pre (spec' state) ->
   pre (spec state) /\
   (forall r,
    proc_hspec (rx r)
      (fun state' =>
       {|
       pre := post (spec state) state' r;
       post := fun (state'' : State) r => post (spec' state) state'' r;
       alternate := fun (state'' : State) r =>
                    alternate (spec' state) state'' r |})) /\
   (forall (r : unit) (state' : State),
    alternate (spec state) state' r -> alternate (spec' state) state' r)) ->
  proc_hspec (Bind p rx) spec'.
Proof.
(unfold proc_hspec at 3).
(intros (Hp_ok, Hp_rec) Hrx).
split.
-
(simpl; rew Hp_ok).
(intros state state' t' (t, (state_mid, (Hspec_mid, Hexec_mid))) Hpre').
specialize (Hrx _ Hpre') as (Hpre, (Hok, Hrec)).
specialize (Hok t).
(rewrite proc_hspec_expand in Hok).
(destruct (Hok state_mid) as (Hrx_ok, Hrx_rec); simpl; eauto).
-
(simpl).
(apply rel_or_elim).
+
(rewrite Hp_rec; auto).
(intros state state' r Hspec_aexec Hpre').
(specialize (Hrx _ Hpre') as (Hpre, (?, Hrec)); eauto).
+
(rewrite Hp_ok).
(intros state state' t' (t, (state_mid, (Hspec_mid, Hcrash_mid))) Hpre').
specialize (Hrx _ Hpre') as (Hpre, (Hok, Hrec)).
specialize (Hok t).
(rewrite proc_hspec_expand in Hok).
(destruct (Hok state_mid) as (Hrx_ok, Hrx_rec); simpl; eauto).
Qed.
Definition rec_noop `(rec : proc R) (wipe : State -> State -> Prop) :=
  forall T (v : T),
  proc_rspec (Ret v) rec
    (fun state =>
     {|
     pre := True;
     post := fun state' r => r = v /\ state' = state;
     alternate := fun state' _ => wipe state state' |}).
Theorem ret_rspec T R (wipe : State -> State -> Prop)
  `(spec : Specification T R State) (v : T) (rec : proc R) :
  rec_noop rec wipe ->
  (forall state,
   pre (spec state) ->
   post (spec state) state v /\
   (forall state',
    wipe state state' -> forall r : R, alternate (spec state) state' r)) ->
  proc_rspec (Ret v) rec spec.
Proof.
(unfold proc_rspec; intros Hnoop Himpl; split).
-
(intros state state' t Hexec Hpre).
(inversion Hexec; subst).
specialize (Himpl _ Hpre).
intuition.
-
(destruct (Hnoop _ v) as (?, ->)).
(unfold spec_aexec).
firstorder.
Qed.
Theorem ret_hspec T `(spec : Specification T unit State) 
  (v : T) :
  (forall state,
   pre (spec state) ->
   post (spec state) state v /\
   (forall state',
    crash_step state state' tt -> alternate (spec state) state' tt)) ->
  proc_hspec (Ret v) spec.
Proof.
(unfold proc_hspec, spec_exec, spec_aexec; simpl).
(unfold "--->", pure; split; propositional).
(specialize (H _ H1); propositional).
(specialize (H _ H1); propositional).
(destruct o; eauto).
Qed.
Definition idempotent A T R `(spec : A -> Specification T R State) :=
  forall a state,
  pre (spec a state) ->
  forall v state',
  alternate (spec a state) state' v ->
  exists a',
    pre (spec a' state') /\
    (forall rv state'',
     post (spec a' state') state'' rv -> post (spec a state) state'' rv).
Theorem rspec_intros T R `(spec : Specification T R State) 
  `(p : proc T) `(rec : proc R) :
  (forall state0,
   pre (spec state0) ->
   proc_rspec p rec
     (fun state =>
      {|
      pre := state = state0;
      post := fun state' r => post (spec state) state' r;
      alternate := fun state' r => alternate (spec state) state' r |})) ->
  proc_rspec p rec spec.
Proof.
(unfold proc_rspec at 2; intros H).
(split; intros s s' r Hexec Hpre; eapply H; simpl; eauto).
Qed.
Theorem hspec_intros T `(spec : Specification T unit State) 
  `(p : proc T) :
  (forall state0,
   pre (spec state0) ->
   proc_hspec p
     (fun state =>
      {|
      pre := state = state0;
      post := fun state' r => post (spec state) state' r;
      alternate := fun state' r => alternate (spec state) state' r |})) ->
  proc_hspec p spec.
Proof.
(unfold proc_hspec at 2; intros H).
(split; intros s s' r Hexec Hpre; eapply H; simpl; eauto using tt).
Qed.
Theorem op_spec_sound T (op : Op T) : proc_hspec (Call op) (op_spec sem op).
Proof.
(unfold proc_hspec; split).
-
(intros state state' t Hexec Hpre; eauto).
-
(simpl).
(apply rel_or_elim).
*
(intros s s' [] Hl Hpre).
(simpl).
(split; auto).
*
(intros s s' [] Hl Hpre).
(inversion Hl as (?, (?, (?, Hrest)))).
firstorder.
Qed.
Theorem op_spec_complete T (op : Op T) :
  spec_exec (op_spec sem op) ---> exec (Call op) /\
  spec_aexec (op_spec sem op) ---> exec_crash (Call op).
Proof.
(split; firstorder).
Qed.
Theorem op_spec_complete1 T (op : Op T) :
  spec_exec (op_spec sem op) ---> exec (Call op).
Proof.
firstorder.
Qed.
Theorem op_spec_complete2 T (op : Op T) :
  spec_aexec (op_spec sem op) ---> crash_step + (sem.(step) op;; crash_step).
Proof.
firstorder.
Qed.
Lemma spec_aexec_cancel T R1 R2 (spec1 : Specification T R1 State)
  (spec2 : Specification T R2 State) (r : relation State State R2) :
  (forall s, (spec2 s).(pre) -> (spec1 s).(pre)) ->
  (forall s r1,
   _ <- test (fun s' => (spec1 s).(pre) /\ (spec1 s).(alternate) s' r1);
   r
   --->
    (fun s2a s2b r => (spec2 s).(pre) -> (spec2 s).(alternate) s2b r)) ->
  _ <- spec_aexec spec1; r ---> spec_aexec spec2.
Proof.
(intros Hpre_impl Hrest s1 s2 r2 Hl Hpre').
(destruct Hl as (r1, (smid, (?, ?)))).
(eapply (Hrest s1 r1); eauto).
exists tt,smid.
(split; simpl; eauto).
(unfold test).
firstorder.
(rel_congruence; norm).
Qed.
Theorem proc_hspec_to_rspec A' T R (p_hspec : Specification T unit State)
  `(rec_hspec : A' -> Specification R unit State)
  `(p_rspec : Specification T R State) `(p : proc T) 
  `(rec : proc R) :
  proc_hspec p p_hspec ->
  (forall a, proc_hspec rec (rec_hspec a)) ->
  idempotent rec_hspec ->
  (forall s,
   (p_rspec s).(pre) ->
   (p_hspec s).(pre) /\
   (forall s' v, (p_hspec s).(post) s' v -> (p_rspec s).(post) s' v)) ->
  (forall state state' v,
   pre (p_hspec state) ->
   alternate (p_hspec state) state' v -> exists a, pre (rec_hspec a state')) ->
  (forall a s sc,
   (p_rspec s).(pre) ->
   forall sfin rv,
   (rec_hspec a sc).(post) sfin rv -> (p_rspec s).(alternate) sfin rv) ->
  proc_rspec p rec p_rspec.
Proof.
(intros (Hpe, Hpc) Hc).
(unfold idempotent).
(intros Hidemp).
(intros Himpl1 Hc_crash_r Hr_alt).
split.
-
(rew Hpe; auto).
rew<- H.
(intros s1 s2 t Hl Hpre).
(eapply Himpl1; eauto).
(eapply Hl).
(eapply Himpl1; eauto).
-
(unfold rexec).
(rewrite Hpc).
Qed.
(unfold exec_recover).
(eapply spec_aexec_cancel).
{
(eapply Himpl1).
}
(intros s1 []).
setoid_rewrite  <- bind_assoc.
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
(assert
  (HCI :
   test
     (fun s' : State => (p_hspec s1).(pre) /\ (p_hspec s1).(alternate) s' tt)
   --->
    @any _ _ unit;;
    test (fun s' : State => exists a', (rec_hspec a' s').(pre)))).
{
(unfold test, rimpl, any; propositional).
-
pose unfolded rf.(compile_op_ok) op
 fun H => red in H; unfold rexec, refines in H.
(exists tt; eexists; intuition eauto).
rew H0.
}
rew HCI.
-
rew crash_step_refinement.
-
(Split; [ Left | Right ]).
setoid_rewrite  <- bind_assoc at 2.
setoid_rewrite  <- bind_assoc.
(rewrite seq_star_mid_invariant).
*
(rewrite bind_assoc).
(intros sa sb r Hl Hpre_s1).
(destruct Hl as ([], (smid, (_, Hl)))).
(destruct Hl as ([], (?, (Htest, ?)))).
(destruct Htest as ((a', ?), ?)).
subst.
(eapply Hr_alt; eauto).
(eapply Hc; eauto).
*
(intros s s' [] Hl).
(destruct Hl as ([], (?, (((a', Hhspec), <-), Hexec_crash)))).
(unfold any; exists tt; eexists; split; auto).
(split; [  | eauto ]).
(edestruct Hidemp as (a'', ?); eauto).
(eapply Hc; eauto).
(eexists; intuition eauto).
*
(apply any_seq_star_any).
Qed.
End Hoare.
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
  test c_initP;; inited <- c_exec rf.(impl).(init);
  ifInit inited (c_exec (compile p))
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
  test c_initP;; inited <- c_exec rf.(impl).(init);
  ifInit inited (rexec c_sem (compile p) (compile_rec rec))
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
  test c_initP;; inited <- c_exec rf.(impl).(init);
  ifInit inited (exec_seq c_sem (compile_seq p) (compile_rec rec))
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
   end) cs1 cs2 mv ->
  match mv with
  | None => True
  | Some v => exists as1 as2, a_initP as1 /\ (exec_seq a_sem p rec) as1 as2 v
  end.
Proof.
(intros).
(pose proof (complete_exec_seq_ok_tests p rec)).
(unfold ifInit in H1).
(edestruct (H1 cs1 cs2 mv)).
{
exists tt,cs1.
(split; [ firstorder |  ]).
(destruct H0 as (i, (cs1', (?, ?)))).
exists i,cs1'.
(split; intuition).
}
(destruct H2 as ([], (as1, (?, ?)))).
-
(edestruct H3 as ([], (?, ((?, <-), ?)))).
(destruct H5 as (v, (as2, (?, (?, (?, (?, ?))))))).
(inversion H7; subst; exists as1,as2).
(subst; split; auto).
-
(repeat destruct H2).
(inversion H3; subst; eauto).
Qed.
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
   (_ <- any (T:=unit); _ <- test l3.(initP);
    _ <- _ <- rf2.(absr);
             rf1.(absr); pure Initialized) +
   (_ <- any (T:=unit); pure InitFailed).
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
