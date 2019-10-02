Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2yTafL"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Spec.Proc Spec.ProcTheorems.
From Tactical Require Import ProofAutomation.
From Transitions Require Import Relations Rewriting NonError.
Import RelationNotations.
Set Default Goal Selector "!".
Record SpecProps T R State :={pre : Prop; post : State -> T -> Prop; alternate : State -> R -> Prop}.
Definition Specification T R State := State -> SpecProps T R State.
Definition ret_matches B T (f : B -> T -> Prop) (ret : Return B T) :=
  match ret with
  | Val s' r => f s' r
  | Err _ _ => False
  end.
Definition spec_exec T R State (spec : Specification T R State) : relation State State T :=
  fun s ret => (spec s).(pre) -> ret_matches (spec s).(post) ret.
Definition spec_aexec T R State (spec : Specification T R State) : relation State State R :=
  fun s ret => (spec s).(pre) -> ret_matches (spec s).(alternate) ret.
Theorem impl_spec_exec `(spec : Specification T R State) (r : relation _ _ _) :
  (forall s, (spec s).(pre) -> forall ret, r s ret -> ret_matches (spec s).(post) ret) <->
  r ---> spec_exec spec.
Proof.
firstorder.
Qed.
Theorem impl_spec_aexec `(spec : Specification T R State) (r : relation _ _ _) :
  (forall s, (spec s).(pre) -> forall ret, r s ret -> ret_matches (spec s).(alternate) ret) <->
  r ---> spec_aexec spec.
Proof.
firstorder.
Qed.
Definition spec_impl `(spec1 : Specification T R State) `(spec2 : Specification T R State) :=
  forall s,
  (spec2 s).(pre) ->
  (spec1 s).(pre) /\
  (forall s' v, (spec1 s).(post) s' v -> (spec2 s).(post) s' v) /\
  (forall s' rv, (spec1 s).(alternate) s' rv -> (spec2 s).(alternate) s' rv).
Theorem spec_impl_rel `(spec1 : Specification T R State) spec2 :
  spec_impl spec1 spec2 ->
  spec_exec spec1 ---> spec_exec spec2 /\ spec_aexec spec1 ---> spec_aexec spec2.
Proof.
(unfold spec_impl; intros).
split.
-
(apply impl_spec_exec; intros).
(eapply H in H0; propositional).
(destruct ret; simpl in H1; firstorder).
-
(apply impl_spec_aexec; intros).
(eapply H in H0; propositional).
(destruct ret; simpl in H1; firstorder).
Qed.
Definition op_spec `(sem : Dynamics Op State) `(op : Op T) : Specification T unit State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => sem.(step) op state (Val state' v);
  alternate := fun state' r =>
               r = tt /\
               (crash_step sem state (Val state' r) \/
                (exists smid v, sem.(step) op state (Val smid v) /\ crash_step sem smid (Val state' r))) |}.
Section Hoare.
Context `(sem : Dynamics Op State).
Notation proc := (proc Op).
Notation exec := (exec sem).
Notation exec_crash := (exec_crash sem).
Notation crash_step := sem.(crash_step).
Notation rexec := (rexec sem).
Definition proc_rspec T R (p : proc T) (rec : proc R) (spec : Specification T R State) :=
  exec p ---> spec_exec spec /\ rexec p rec ---> spec_aexec spec.
Definition proc_hspec T (p : proc T) (spec : Specification T unit State) :=
  exec p ---> spec_exec spec /\ exec_crash p ---> spec_aexec spec.
Theorem proc_rspec_expand T R (p : proc T) (rec : proc R) (spec : Specification T R State) :
  proc_rspec p rec spec <->
  (forall s,
   (spec s).(pre) ->
   (forall ret, exec p s ret -> ret_matches (spec s).(post) ret) /\
   (forall ret, rexec p rec s ret -> ret_matches (spec s).(alternate) ret)).
Proof.
(unfold proc_rspec).
(split; propositional).
-
(split; intros;
  match goal with
  | H:?exec _ ---> _, H':?exec _ _ _ |- _ => apply H in H'; intuition eauto
  end).
+
(apply H3 in H0; simpl in *; contradiction).
+
(apply H3 in H0; simpl in *; contradiction).
-
(split; unfold rimpl; intros; right).
+
(hnf; intros).
firstorder.
+
(hnf; intros).
firstorder.
Qed.
Theorem proc_hspec_expand T (p : proc T) (spec : Specification T unit State) :
  proc_hspec p spec <->
  (forall s,
   (spec s).(pre) ->
   (forall ret, exec p s ret -> ret_matches (spec s).(post) ret) /\
   (forall ret, exec_crash p s ret -> ret_matches (spec s).(alternate) ret)).
Proof.
(unfold proc_hspec).
(split; propositional).
-
(split; intros;
  match goal with
  | H:?exec _ ---> _, H':?exec _ _ _ |- _ => apply H in H'; intuition eauto
  end).
+
(apply H3 in H0; simpl in *; contradiction).
+
(apply H3 in H0; simpl in *; contradiction).
-
(split; unfold rimpl; intros; right).
+
(hnf; intros).
firstorder.
+
(hnf; intros).
firstorder.
Qed.
Theorem proc_rspec_impl `(spec1 : Specification T R State) `(spec2 : Specification T R State) 
  p rec : spec_impl spec1 spec2 -> proc_rspec p rec spec1 -> proc_rspec p rec spec2.
Proof.
(unfold proc_rspec; propositional).
(apply spec_impl_rel in H; propositional).
split.
-
(etransitivity; eauto).
-
(etransitivity; eauto).
Qed.
Theorem proc_hspec_impl `(spec1 : Specification T unit State) `(spec2 : Specification T unit State) 
  p : spec_impl spec1 spec2 -> proc_hspec p spec1 -> proc_hspec p spec2.
Proof.
(unfold proc_hspec; propositional).
(apply spec_impl_rel in H; propositional).
split.
-
(etransitivity; eauto).
-
(etransitivity; eauto).
Qed.
Theorem proc_rspec_exec_equiv T `(spec : Specification T R State) (p p' : proc T) 
  `(rec : proc R) : exec_equiv sem p p' -> proc_rspec p' rec spec -> proc_rspec p rec spec.
Proof.
(unfold proc_rspec).
(intros ->; auto).
Qed.
Theorem proc_hspec_exec_equiv T `(spec : Specification T unit State) (p p' : proc T) :
  exec_equiv sem p p' -> proc_hspec p' spec -> proc_hspec p spec.
Proof.
(unfold proc_hspec).
(intros ->; auto).
Qed.
Theorem proc_rspec_rx T T' R `(spec : Specification T R State) `(p : proc T) 
  `(rec : proc R) `(rx : T -> proc T') `(spec' : Specification T' R State) :
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
       alternate := fun (state'' : State) r => alternate (spec' state) state'' r |})) /\
   (forall (r : R) (state' : State),
    alternate (spec state) state' r -> alternate (spec' state) state' r)) ->
  proc_rspec (Bind p rx) rec spec'.
Proof.
(unfold proc_rspec at 3).
(intros (Hp_ok, Hp_rec) Hrx).
split.
-
clear Hp_rec.
(simpl; rew Hp_ok).
(apply impl_spec_exec).
(intros s Hpre).
(specialize (Hrx _ Hpre); propositional).
(destruct ret; simpl in *; propositional).
+
(specialize (H H0); simpl in *).
(eapply H1 in H3).
intuition eauto.
*
(specialize (H4 H); simpl in *; contradiction).
*
(specialize (H4 H); simpl in *; auto).
+
intuition propositional.
*
(specialize (H3 H0); simpl in *; contradiction).
*
(specialize (H H0); simpl in *; auto).
(eapply H1 in H3).
intuition eauto.
--
(specialize (H4 H); simpl in *; contradiction).
--
(specialize (H4 H); simpl in *; auto).
-
(rewrite rexec_unfold).
(rewrite rexec_unfold in Hp_rec).
(simpl).
Split.
+
rew Hp_rec.
(apply impl_spec_aexec).
(unfold spec_aexec; propositional).
(destruct ret; simpl in *; firstorder).
+
rew Hp_ok.
(change_no_check (let! v <- spec_exec spec; let! _ <- exec_crash (rx v); exec_recover sem rec) with
  (let! v <- spec_exec spec; rexec (rx v) rec)).
(apply impl_spec_aexec; intros s Hpre).
(specialize (Hrx _ Hpre); propositional).
(destruct ret; cbn[and_then ret_matches] in *; propositional).
*
(specialize (H H0); simpl in H).
(eapply H1 in H3; intuition eauto).
--
(specialize (H4 H); simpl in *; contradiction).
--
(specialize (H4 H); simpl in *; auto).
*
intuition propositional.
--
(specialize (H3 H0); simpl in *; contradiction).
--
(specialize (H H0); simpl in H).
(eapply H1 in H3; intuition eauto).
++
(specialize (H4 H); simpl in *; contradiction).
++
(specialize (H4 H); simpl in *; auto).
Qed.
Theorem proc_hspec_rx T T' `(spec : Specification T unit State) `(p : proc T) 
  `(rx : T -> proc T') `(spec' : Specification T' unit State) :
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
       alternate := fun (state'' : State) r => alternate (spec' state) state'' r |})) /\
   (forall (r : unit) (state' : State),
    alternate (spec state) state' r -> alternate (spec' state) state' r)) ->
  proc_hspec (Bind p rx) spec'.
Proof.
(unfold proc_hspec at 3).
(intros (Hp_ok, Hp_rec) Hrx).
split.
-
clear Hp_rec.
(simpl; rew Hp_ok).
(apply impl_spec_exec).
(intros s Hpre).
(specialize (Hrx _ Hpre); propositional).
(destruct ret; simpl in *; propositional).
+
(specialize (H H0); simpl in *).
(eapply H1 in H3).
intuition eauto.
*
(specialize (H4 H); simpl in *; contradiction).
*
(specialize (H4 H); simpl in *; auto).
+
intuition propositional.
*
(specialize (H3 H0); simpl in *; contradiction).
*
(specialize (H H0); simpl in *; auto).
(eapply H1 in H3).
intuition eauto.
--
(specialize (H4 H); simpl in *; contradiction).
--
(specialize (H4 H); simpl in *; auto).
-
(simpl).
Split.
+
rew Hp_rec.
(apply impl_spec_aexec).
(unfold spec_aexec; propositional).
(destruct ret; simpl in *; firstorder).
+
rew Hp_ok.
(apply impl_spec_aexec; intros s Hpre).
(specialize (Hrx _ Hpre); propositional).
(destruct ret; cbn[and_then ret_matches] in *; propositional).
*
(specialize (H H0); simpl in H).
(eapply H1 in H3; intuition eauto).
--
(specialize (H4 H); simpl in *; contradiction).
--
(specialize (H4 H); simpl in *; auto).
*
intuition propositional.
--
(specialize (H3 H0); simpl in *; contradiction).
--
(specialize (H H0); simpl in H).
(eapply H1 in H3; intuition eauto).
++
(specialize (H4 H); simpl in *; contradiction).
++
(specialize (H4 H); simpl in *; auto).
Qed.
Definition rec_noop `(rec : proc R) (wipe : State -> State -> Prop) :=
  forall T (v : T),
  proc_rspec (Ret v) rec
    (fun state =>
     {|
     pre := True;
     post := fun state' r => r = v /\ state' = state;
     alternate := fun state' _ => wipe state state' |}).
Theorem ret_rspec T R (wipe : State -> State -> Prop) `(spec : Specification T R State) 
  (v : T) (rec : proc R) :
  rec_noop rec wipe ->
  (forall state,
   pre (spec state) ->
   post (spec state) state v /\
   (forall state', wipe state state' -> forall r : R, alternate (spec state) state' r)) ->
  proc_rspec (Ret v) rec spec.
Proof.
(unfold proc_rspec; intros Hnoop Himpl; split).
-
(simpl).
(apply impl_spec_exec; intros).
(inv_clear H0; simpl).
(eapply Himpl in H; propositional; eauto).
-
(destruct (Hnoop _ v) as (?, ->)).
(apply impl_spec_aexec; intros).
(destruct ret; firstorder).
Qed.
Theorem ret_hspec T `(spec : Specification T unit State) (v : T)
  (Hcrash_non_error : NonError crash_step) :
  (forall state,
   pre (spec state) ->
   post (spec state) state v /\
   (forall state', crash_step state (Val state' tt) -> alternate (spec state) state' tt)) ->
  proc_hspec (Ret v) spec.
Proof.
(unfold proc_hspec, spec_exec, spec_aexec; simpl).
(unfold "--->", pure; split; propositional).
-
(right; intros).
(specialize (H _ H0); propositional).
-
(right; intros).
(specialize (H _ H1); propositional).
(destruct y; firstorder).
(destruct t).
firstorder.
Qed.
Definition idempotent A T R `(spec : A -> Specification T R State) :=
  forall a state,
  pre (spec a state) ->
  forall v state',
  alternate (spec a state) state' v ->
  exists a',
    pre (spec a' state') /\
    (forall rv state'', post (spec a' state') state'' rv -> post (spec a state) state'' rv).
Theorem rspec_intros T R `(spec : Specification T R State) `(p : proc T) `(rec : proc R) :
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
(split; intros; [ apply impl_spec_exec | apply impl_spec_aexec ]; intros).
-
(destruct ret; firstorder).
-
(eapply H in H1; propositional; eauto).
(intuition idtac; firstorder).
Qed.
Theorem hspec_intros T `(spec : Specification T unit State) `(p : proc T) :
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
(split; intros; [ apply impl_spec_exec | apply impl_spec_aexec ]; intros).
-
(destruct ret; firstorder).
-
(eapply H in H1; propositional; eauto).
(intuition idtac; firstorder).
Qed.
Theorem op_spec_sound T (op : Op T) (Hop_nonerror : NonError (sem.(step) op))
  (Hcrash_nonerror : NonError crash_step) : proc_hspec (Call op) (op_spec sem op).
Proof.
(unfold proc_hspec; split).
-
(apply impl_spec_exec; intros).
(unfold op_spec in H; simpl in *).
(destruct ret; simpl; eauto).
(apply Hop_nonerror in H0; auto).
-
(simpl).
Split.
*
(apply impl_spec_aexec; intros).
(destruct ret; firstorder).
(destruct t; auto).
*
(apply impl_spec_aexec; intros).
(destruct ret; firstorder).
(destruct t; auto).
Qed.
Theorem spec_exec_impl `(p_hspec : Specification T unit State)
  `(p_rspec : Specification T R State) :
  forall s,
  (p_rspec s).(pre) ->
  (p_hspec s).(pre) /\
  (forall s' v, (p_hspec s).(post) s' v -> (p_rspec s).(post) s' v).
Theorem spec_exec_impl `(p_hspec : Specification T unit State)
  `(p_rspec : Specification T R State) :
  (forall s,
   (p_rspec s).(pre) ->
   (p_hspec s).(pre) /\
   (forall s' v, (p_hspec s).(post) s' v -> (p_rspec s).(post) s' v)) ->
  spec_exec p_rspec ---> spec_exec p_hspec.
Theorem spec_exec_impl `(p_hspec : Specification T unit State)
  `(p_rspec : Specification T R State) :
  (forall s,
   (p_rspec s).(pre) ->
   (p_hspec s).(pre) /\
   (forall s' v, (p_hspec s).(post) s' v -> (p_rspec s).(post) s' v)) ->
  spec_exec p_hspec ---> spec_exec p_rspec.
Proof.
(intros).
(apply impl_spec_exec; firstorder).
(unfold spec_exec in H1).
(destruct ret; simpl in *; firstorder).
Add Search Blacklist "Raw" "Proofs".
(apply impl_spec_exec).
(destruct ret; firstorder).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqi7mBFI"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqw8jmHL"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqouVULq"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem proc_hspec_to_rspec A' T R
  (p_hspec : Specification T unit State)
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
   alternate (p_hspec state) state' v ->
   exists a, pre (rec_hspec a state')) ->
  (forall a s sc,
   (p_rspec s).(pre) ->
   forall sfin rv,
   (rec_hspec a sc).(post) sfin rv ->
   (p_rspec s).(alternate) sfin rv) -> proc_rspec p rec p_rspec.
Proof.
(intros (Hpe, Hpc) Hc).
(unfold idempotent).
(intros Hidemp).
(intros Himpl1 Hc_crash_r Hr_alt).
split.
-
(rew Hpe; auto).
(* Auto-generated comment: Succeeded. *)

