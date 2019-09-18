Require Import Spec.Proc.
Require Import Spec.Proc Spec.ProcTheorems.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.
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
Require Import Tactical.Propositional.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Helpers.RelationTheorems.
Import RelationNotations.
Record SpecProps T R State :={pre : Prop;
                              post : State -> T -> Prop;
                              alternate : State -> R -> Prop}.
Proof.
(intros Hop_wp).
(induction p; cleanup; eauto).
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
-
(eapply wp.(op_wp_ok) in H; eauto).
-
(eapply IHp in H1; eauto; cleanup).
(eapply H in H1; eauto).
Qed.
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
Definition proc_hspec T (p : proc T) (spec : Specification T unit State) :=
  exec p ---> spec_exec spec /\ exec_crash p ---> spec_aexec spec.
Theorem proc_rspec_expand T R (p : proc T) (rec : proc R)
  (spec : Specification T R State) :
  proc_rspec p rec spec <->
  (forall s,
   (spec s).(pre) ->
   (forall s' v, exec p s s' v -> (spec s).(post) s' v) /\
   (forall s' rv, rexec p rec s s' rv -> (spec s).(alternate) s' rv)).
Definition crashpre := forall crash : State -> Prop, State -> Prop.
Definition after_crash (crash : State -> Prop) : State -> Prop :=
  fun s => forall s', crash_step s s' tt -> crash s'.
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
Proof.
(unfold proc_rspec, rimpl, spec_exec, spec_aexec; split; intros).
-
intuition eauto  10.
Theorem wp_crash_ok T (p : proc T) (crash : State -> Prop) :
  forall s,
  crashcond p crash s -> forall s' v, exec_crash p s s' v -> crash s'.
Proof.
(induction p; cleanup; after_crash).
-
(split; intros x y ?).
-
(repeat
  match goal with
  | H:_ \/ _ |- _ => destruct H; propositional; after_crash
  end).
(specialize (H x); intuition eauto).
(specialize (H x); intuition eauto).
(eapply wp.(op_wp_ok) in H1; eauto; after_crash).
Qed.
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
-
(repeat
  match goal with
  | H:_ \/ _ |- _ => destruct H; propositional; after_crash
  end).
+
(eapply IHp; eauto).
+
(eapply wp_ok in H2; eauto).
-
(split; intros x y ?).
(specialize (H x); intuition eauto).
(specialize (H x); intuition eauto).
Qed.
Qed.
Theorem proc_rspec_impl `(spec1 : Specification T R State)
  `(spec2 : Specification T R State) p rec :
  spec_impl spec1 spec2 -> proc_rspec p rec spec1 -> proc_rspec p rec spec2.
Proof.
(unfold spec_impl; intros).
(pose proof (proj1 (proc_rspec_expand _ _ _) H0); clear H0).
End Dynamics.
Arguments precondition State T : clear implicits.
Arguments crashpre State : clear implicits.
(apply proc_rspec_expand; intros).
(specialize (H s); propositional).
(specialize (H1 s); propositional).
eauto  10.
Qed.
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
(intros s1 s2 t Hl Hpre).
(eapply Himpl1; eauto).
(eapply Hl).
(eapply Himpl1; eauto).
-
(unfold rexec).
(rewrite Hpc).
(unfold exec_recover).
(eapply spec_aexec_cancel).
{
(eapply Himpl1).
}
(intros s1 []).
setoid_rewrite  <- bind_assoc.
(assert
  (HCI :
   test
     (fun s' : State => (p_hspec s1).(pre) /\ (p_hspec s1).(alternate) s' tt)
   --->
    @any _ _ unit;;
    test (fun s' : State => exists a', (rec_hspec a' s').(pre)))).
{
(unfold test, rimpl, any; propositional).
(exists tt; eexists; intuition eauto).
}
rew HCI.
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
