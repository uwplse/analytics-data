Time From Perennial Require Import Spec.Proc.
Time Require Import Setoid.
Time Require Import Morphisms.
Time Require Import Proc.
Time Set Implicit Arguments.
Time
Class Injectable (Op1 Op : Type -> Type) :=
    inject : forall T, Op1 T -> Op T.
Time Arguments inject {Op1} {Op} {_} {T}.
Time
Fixpoint lift Op1 Op {i : Injectable Op1 Op} T (p : proc Op1 T) : 
proc Op T :=
  match p with
  | Call op => Call (inject op)
  | Ret v => Ret v
  | Bind p1 p2 => Bind (lift p1) (fun v => lift (p2 v))
  | Loop body init => Loop (fun v => lift (body v)) init
  | Spawn p => Spawn (lift p)
  | Unregister => Unregister
  | Wait => Wait
  end.
Time From Classes Require Import Classes.
Time From Transitions Require Import Relations Rewriting.
Time Require Import Tactical.ProofAutomation.
Time Require Import List.
Time Import RelationNotations.
Time Section Dynamics.
Time Context `(sem : Dynamics Op OpState).
Time Notation proc := (proc Op).
Time Notation proc_seq := (proc_seq Op).
Time Notation rec_seq := (rec_seq Op).
Time Notation step := sem.(step).
Time Notation crash_step := (lifted_crash_step sem).
Time Notation finish_step := (lifted_finish_step sem).
Time Notation State := (@State OpState).
Time Notation exec_halt := (exec_halt sem).
Time Notation exec_partial := (exec_partial sem).
Time Notation exec := (exec sem).
Time Notation exec_pool := (exec_pool sem).
Time Module OpSums.
Time
Inductive OpSum (Op1 Op2 : Type -> Type) : Type -> Type :=
  | Inl : forall T, Op1 T -> OpSum Op1 Op2 T
  | Inr : forall T, Op2 T -> OpSum Op1 Op2 T.
Time Notation exec_seq_partial := (exec_seq_partial sem).
Time Notation exec_seq := (exec_seq sem).
Time Notation rexec_seq := (rexec_seq sem).
Time Notation exec_recover1 := (exec_recover1 sem).
Time Notation exec_recover := (exec_recover sem).
Time Notation exec_recover_partial := (exec_recover_partial sem).
Time Notation rexec := (rexec sem).
Time Notation rexec_partial := (rexec_partial sem).
Time Notation rexec_seq_partial := (rexec_seq_partial sem).
Time Notation proc_exec_seq := (proc_exec_seq sem).
Time Notation exec_or_rexec := (exec_or_rexec sem).
Time Arguments Inl {Op1} {Op2} {T}.
Time Arguments Inr {Op1} {Op2} {T}.
Time Infix "\226\138\149" := OpSum (at level 60).
Time
Instance Inl_inject  Op1 Op2: (Injectable Op1 (Op1 \226\138\149 Op2)) := (@Inl _ _).
Time
Instance Inr_inject  Op1 Op2: (Injectable Op2 (Op1 \226\138\149 Op2)) := (@Inr _ _).
Time Hint Resolve rimpl_refl requiv_refl.
Time
Ltac
 destruct_hd :=
  match goal with
  | |- and_then match ?v with
                | _ => _
                end _ ---> _ => destruct v
  end.
Time
Theorem exec_halt_finish T (p : proc T) : (exec p;; pure tt) ---> exec_halt p.
Time Proof.
Time
(unfold exec, exec_halt; induction p; simpl in *; norm; try rel_congruence;
  repeat destruct_hd; norm; apply from_none).
Time End OpSums.
Time Qed.
Time Theorem exec_halt_noop T (p : proc T) : pure tt ---> exec_halt p.
Time Proof.
Time (unfold exec_halt).
Time setoid_rewrite  <- bind_star_expand_r.
Time Left.
Time Qed.
Time
Theorem exec_seq_partial_noop (p : rec_seq) : pure tt ---> exec_seq_partial p.
Time Proof.
Time (induction p; simpl; eauto).
Time Right.
Time (apply exec_halt_noop).
Time Qed.
Time
Lemma exec_partial_ret T (v : T) :
  exec_partial (Ret v) <---> pure (existT _ _ (Ret v) :: nil)%list.
Time Proof.
Time (apply rimpl_to_requiv).
Time -
Time (unfold exec_partial).
Time (apply bind_star_ind_r_pure).
Time Split.
Time (simpl in *).
Time (unfold exec_pool_hd).
Time (simpl in *).
Time norm.
Time rew none_plus_r.
Time (apply from_none).
Time -
Time setoid_rewrite  <- bind_star_expand_r.
Time Left.
Time Qed.
Time
Lemma exec_partial_finish T (p : proc T) s1 s2 (v : T) 
  tp :
  exec_partial p s1 (Val s2 (cons (existT _ _ (Ret v)) tp)) ->
  exec p s1 (Val s2 (existT _ _ v)).
Time Proof.
Time (intros).
Time (do 2 eexists).
Time (split; eauto).
Time (simpl).
Time (econstructor; eauto).
Time Qed.
Time Theorem exec_halt_ret T (v : T) : exec_halt (Ret v) <---> pure tt.
Time Proof.
Time (unfold exec_halt).
Time rew exec_partial_ret.
Time Qed.
Time
Theorem exec_halt_idem T (p : proc T) :
  pure tt + exec_halt p <---> exec_halt p.
Time Proof.
Time (apply rimpl_or; auto using exec_halt_noop).
Time Qed.
Time
Theorem exec_seq_partial_idem (p : rec_seq) :
  pure tt + exec_seq_partial p <---> exec_seq_partial p.
Time Proof.
Time (apply rimpl_or; auto using exec_seq_partial_noop).
Time Qed.
Time
Definition exec_equiv T (p p' : proc T) :=
  exec p <---> exec p' /\ exec_halt p <---> exec_halt p'.
Time
Definition exec_seq_equiv (p p' : rec_seq) :=
  exec_seq p <---> exec_seq p' /\
  exec_seq_partial p <---> exec_seq_partial p'.
Time #[global]
Instance exec_equiv_equiv  T: (Equivalence (exec_equiv (T:=T))).
Time Proof.
Time (unfold exec_equiv).
Time
(RelInstance_t; intuition idtac;
  repeat
   match goal with
   | H:_ <---> _ |- _ => apply requiv_to_rimpls in H
   | |- _ <---> _ => apply rimpl_to_requiv
   | _ => progress propositional
   end; auto; try (solve [ etransitivity; eauto ])).
Time Qed.
Time Infix "<==>" := exec_equiv (at level 70).
Time
Lemma exec_partial_crash_pure T (p : proc T) :
  _ <- exec_partial p;
  crash_step
  <--->
   _ <- exec_partial p;; pure tt;
  crash_step.
Time Proof.
Time (rewrite bind_assoc).
Time norm.
Time Qed.
Time
Theorem rexec_equiv T (p p' : proc T) (rec : rec_seq) :
  p <==> p' -> rexec p rec <---> rexec p' rec.
Time Proof.
Time (unfold "<==>"; propositional).
Time (unfold exec_halt in H0).
Time setoid_rewrite  <- bind_assoc.
Time rel_congruence.
Time (rewrite exec_partial_crash_pure).
Time (rewrite H0).
Time norm.
Time Qed.
Time
Theorem rexec_partial_equiv T (p p' : proc T) (rec : rec_seq) :
  p <==> p' -> rexec_partial p rec <---> rexec_partial p' rec.
Time Proof.
Time (unfold "<==>"; propositional).
Time (unfold exec_halt in H0).
Time setoid_rewrite  <- bind_assoc.
Time rel_congruence.
Time (rewrite exec_partial_crash_pure).
Time (rewrite H0).
Time norm.
Time Qed.
Time #[global]
Instance exec_respectful  T:
 (Proper (@exec_equiv T ==> @requiv State State _) exec).
Time Proof.
Time (intros ? ? (?, ?); intuition).
Time Qed.
Time #[global]
Instance exec_halt_respectful  T:
 (Proper (@exec_equiv T ==> @requiv State State unit) exec_halt).
Time Proof.
Time (intros ? ? (?, ?); intuition).
Time Qed.
Time #[global]
Instance rexec_respectful  T:
 (Proper (@exec_equiv T ==> @eq rec_seq ==> @requiv State State _) rexec).
Time Proof.
Time (intros ? ? ? ? ? ->).
Time (eapply rexec_equiv; eauto).
Time Qed.
Time #[global]
Instance rexec_partial_respectful  T:
 (Proper (@exec_equiv T ==> @eq rec_seq ==> @requiv State State _)
    rexec_partial).
Time Proof.
Time (intros ? ? ? ? ? ->).
Time (eapply rexec_partial_equiv; eauto).
Time Qed.
Time
Theorem monad_left_id T T' (p : T' -> proc T) v : Bind (Ret v) p <==> p v.
Time Proof.
Time (split; simpl; norm).
Time -
Time (unfold exec, exec_partial).
Time (apply rimpl_to_requiv).
Time *
Time rew<- bind_star_expand.
Time (Split; [ apply from_none |  ]).
Time (simpl).
Time setoid_rewrite none_absorb_l at 1.
Time setoid_rewrite none_plus_r at 1.
Time (unfold exec_pool_hd; norm; simpl).
Time setoid_rewrite  <- bind_star_expand at 1.
Time (rel_congruence; simpl).
Time *
Time setoid_rewrite  <- bind_star_expand at 2.
Time Right.
Time (simpl).
Time setoid_rewrite none_absorb_l_equiv at 1.
Time rew none_plus_r.
Time (simpl).
Time (unfold exec_pool_hd; norm).
Time -
Time (unfold exec_halt, exec_partial).
Time (apply rimpl_to_requiv).
Time *
Time (setoid_rewrite  <- bind_star_expand at 1; norm).
Time (Split; [ rew<- bind_star_expand; Left |  ]).
Time (simpl).
Time setoid_rewrite none_absorb_l at 1.
Time setoid_rewrite none_plus_r at 1.
Time (simpl).
Time (unfold exec_pool_hd; norm; simpl).
Time *
Time (setoid_rewrite  <- bind_star_expand at 2; norm).
Time Right.
Time (simpl).
Time setoid_rewrite none_absorb_l_equiv at 1.
Time rew none_plus_r.
Time (simpl).
Time (unfold exec_pool_hd; norm; simpl).
Time Qed.
Time Lemma exec_seq_partial_nil : exec_seq_partial Seq_Nil <---> pure tt.
Time Proof.
Time eauto.
Time Qed.
Time Lemma exec_seq_nil : exec_seq Seq_Nil <---> pure tt.
Time Proof.
Time eauto.
Time Qed.
Time Lemma exec_recover_nil : exec_recover Seq_Nil <---> seq_star crash_step.
Time Proof.
Time (unfold exec_recover).
Time setoid_rewrite exec_seq_partial_nil.
Time norm.
Time (apply bind_right_id_unit).
Time Qed.
Time
Definition exec_partial_n {T} (p : proc T) n :=
  bind_rep_n n exec_pool (existT _ T p :: nil).
Time
Definition exec_n {T} (e : proc T) n (\207\131 : State)
  (res : Return State {T : Type & T}) : Prop :=
  match res with
  | Err => bind_rep_n n exec_pool (existT _ _ e :: nil) \207\131 Err
  | Val \207\131' v =>
      exists tp,
        bind_rep_n n exec_pool (existT _ _ e :: nil) \207\131
          (Val \207\131' (existT _ _ (Ret (projT2 v)) :: tp))
  end.
Time
Lemma exec_equiv_exec_n {T} (e : proc T) \207\131 res :
  exec e \207\131 res <-> (exists n, exec_n e n \207\131 res).
Time Proof.
Time (destruct res).
Time -
Time split.
Time *
Time (intros (tp, (?, (Hhd, Htl)))).
Time (destruct tp as [| (v', []) tp']; try inversion Htl).
Time subst.
Time (apply bind_star_inv_rep_n in Hhd as (n, ?)).
Time exists n,tp'.
Time eauto.
Time *
Time (intros (n, (tp, Hexec))).
Time (apply bind_star_rep_n_to_bind_star in Hexec).
Time (eexists (_ :: tp),_; split; eauto).
Time (simpl).
Time (destruct t; econstructor).
Time -
Time split.
Time *
Time (intros H%bind_with_no_err).
Time {
Time (apply bind_star_inv_rep_n in H as (n, ?)).
Time exists n.
Time eauto.
Time }
Time {
Time (intros ? [| (?, [])]; inversion 1).
Time }
Time *
Time (intros (n, Hexec)).
Time left.
Time (apply bind_star_rep_n_to_bind_star in Hexec).
Time eauto.
Time Qed.
Time
Lemma exec_partial_equiv_exec_partial_n {T} (e : proc T) 
  \207\131 res : exec_partial e \207\131 res <-> (exists n, exec_partial_n e n \207\131 res).
Time Proof.
Time split.
Time -
Time (intros (n, Hrep)%bind_star_inv_rep_n).
Time (exists n; eauto).
Time -
Time (intros (n, ?)).
Time (eapply bind_star_rep_n_to_bind_star; eauto).
Time Qed.
Time Opaque Proc.exec.
Time
Definition rec_singleton {T} (rec : proc T) : rec_seq := Seq_Cons rec Seq_Nil.
Time
Lemma exec_seq_snoc T `(p : proc T) `(rec : rec_seq) :
  exec_seq (rec_seq_snoc rec p) <---> (exec_seq rec;; exec p;; pure tt).
Time Proof.
Time (induction rec).
Time -
Time (simpl).
Time norm.
Time -
Time (simpl).
Time rew IHrec.
Time Qed.
Time
Lemma exec_seq_append `(rec1 : rec_seq) (rec2 : rec_seq) :
  exec_seq (rec_seq_append rec1 rec2) <---> (exec_seq rec1;; exec_seq rec2).
Time Proof.
Time (induction rec1).
Time -
Time (simpl).
Time norm.
Time -
Time (simpl).
Time rew IHrec1.
Time Qed.
Time
Lemma exec_seq_partial_snoc T `(p : proc T) `(rec : rec_seq) :
  exec_seq_partial (rec_seq_snoc rec p)
  <--->
   exec_seq_partial rec + (exec_seq rec;; exec_halt p).
Time Proof.
Time (induction rec).
Time -
Time (simpl).
Time (rewrite bind_left_id, exec_halt_idem).
Time (apply rimpl_to_requiv).
Time *
Time (rewrite exec_halt_finish, rel_or_idem; auto).
Time *
Time Right.
Time -
Time (simpl).
Time setoid_rewrite IHrec.
Time (rewrite bind_dist_l).
Time norm.
Time (rewrite <- rel_or_assoc).
Time (rewrite <- rel_or_assoc).
Time (apply or_respects_equiv; eauto).
Time (apply rel_or_symmetric).
Time Qed.
Time
Lemma exec_seq_partial_singleton {T} (rec : proc T) :
  exec_seq_partial (rec_singleton rec) <---> exec_halt rec.
Time Proof.
Time (simpl).
Time (apply rimpl_to_requiv).
Time -
Time Split.
Time (apply exec_halt_finish).
Time -
Time Right.
Time Qed.
Time
Lemma exec_seq_partial_append `(rec1 : rec_seq) `(rec2 : rec_seq) :
  exec_seq_partial (rec_seq_append rec1 rec2)
  <--->
   exec_seq_partial rec1 + (exec_seq rec1;; exec_seq_partial rec2).
Time Proof.
Time (induction rec1).
Time -
Time (simpl).
Time (rewrite bind_left_id, exec_seq_partial_idem; auto).
Time -
Time (simpl).
Time setoid_rewrite IHrec1.
Time (rewrite bind_dist_l).
Time norm.
Time (rewrite <- rel_or_assoc).
Time (rewrite <- rel_or_assoc).
Time (apply or_respects_equiv; eauto).
Time (apply rel_or_symmetric).
Time Qed.
Time
Theorem exec_recover_snoc T `(p : proc T) `(rec : rec_seq) :
  exec_recover (rec_seq_snoc rec p)
  <--->
   (exec_recover rec;; seq_star (rexec p rec);; exec p;; pure tt).
Time Proof.
Time (unfold exec_recover).
Time (unfold exec_recover, rexec, rexec_seq; simpl; norm).
Time (rewrite exec_seq_partial_snoc).
Time (rewrite ?bind_dist_r).
Time (unfold exec_recover).
Time setoid_rewrite exec_seq_snoc.
Time (gen exec_seq rec exec_seq_partial rec crash_step; clear rec).
Time (intros rec1 rec1_crash crash).
Time rew denesting.
Time rel_congruence.
Time (rewrite <- ?bind_assoc).
Time (rel_congruence; norm).
Time (rewrite <- bind_assoc).
Time (rewrite seq_unit_sliding_equiv).
Time norm.
Time Qed.
Time
Lemma exec_recover_append_helper
  (rec1 rec1_crash rec2 rec2_crash crash : relation State State unit) :
  _ <- seq_star (_ <- rec1_crash; crash + _ <- _ <- rec1;
                                                 rec2_crash; crash);
  _ <- rec1;
  rec2
  <--->
   _ <- seq_star (_ <- rec1_crash; crash);
  _ <- rec1;
  _ <- seq_star
         (_ <- rec2_crash; _ <- crash;
          _ <- seq_star (_ <- rec1_crash; crash); rec1);
  rec2.
Time Proof.
Time (intros).
Time rew denesting.
Time rel_congruence.
Time (rewrite <- ?bind_assoc).
Time (rel_congruence; norm).
Time (rewrite seq_unit_sliding_equiv).
Time norm.
Time Qed.
Time
Theorem exec_recover_append `(rec1 : rec_seq) `(rec2 : rec_seq) :
  exec_recover (rec_seq_append rec1 rec2)
  <--->
   (exec_recover rec1;; seq_star (rexec_seq rec2 rec1);; exec_seq rec2).
Time Proof.
Time (unfold exec_recover, rexec, rexec_seq; simpl; norm).
Time (rewrite exec_seq_partial_append).
Time (rewrite ?bind_dist_r).
Time (unfold exec_recover).
Time setoid_rewrite exec_seq_append.
Time (apply exec_recover_append_helper).
Time Qed.
Time Opaque lifted_crash_step.
Time
Theorem exec_recover_partial_append `(rec1 : rec_seq) 
  `(rec2 : rec_seq) :
  exec_recover_partial (rec_seq_append rec1 rec2)
  --->
   exec_recover_partial rec1 +
   (exec_recover rec1;;
    seq_star (rexec_seq rec2 rec1);; rexec_seq_partial rec2 rec1) +
   (exec_recover rec1;;
    seq_star (rexec_seq rec2 rec1);; exec_seq_partial rec2).
Time Proof.
Time
(unfold exec_recover, exec_recover_partial, rexec, rexec_seq,
  rexec_seq_partial; simpl; norm).
Time (rewrite exec_seq_partial_append).
Time (rewrite ?bind_dist_r).
Time setoid_rewrite exec_seq_partial_append.
Time (rewrite ?bind_dist_l).
Time
(assert
  (Hcase2 :
   (exec_recover rec1;;
    seq_star (rexec_seq rec2 rec1);; rexec_seq_partial rec2 rec1)
   <--->
    _ <- seq_star (_ <- exec_seq_partial rec1; crash_step);
   _ <- seq_star
          (_ <- exec_seq rec1; _ <- exec_seq_partial rec2; 
           _ <- crash_step;
           seq_star (_ <- exec_seq_partial rec1; crash_step));
   _ <- exec_seq rec1;
   _ <- exec_seq_partial rec2;
   _ <- crash_step;
   exec_recover_partial rec1)).
Time {
Time (unfold exec_recover).
Time setoid_rewrite bind_assoc.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- bind_assoc at 3.
Time setoid_rewrite  <- bind_assoc at 3.
Time setoid_rewrite  <- (seq_unit_sliding_equiv (exec_seq rec1)).
Time norm.
Time }
Time
(assert
  (Hcase3 :
   (exec_recover rec1;;
    seq_star (rexec_seq rec2 rec1);; exec_seq_partial rec2)
   <--->
    _ <- seq_star (_ <- exec_seq_partial rec1; crash_step);
   _ <- seq_star
          (_ <- exec_seq rec1; _ <- exec_seq_partial rec2; 
           _ <- crash_step;
           seq_star (_ <- exec_seq_partial rec1; crash_step));
   _ <- exec_seq rec1;
   exec_seq_partial rec2)).
Time {
Time (unfold rexec_seq, exec_recover).
Time setoid_rewrite bind_assoc at 1.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- (seq_unit_sliding_equiv (exec_seq rec1)).
Time norm.
Time }
Time Split.
Time -
Time rew denesting.
Time setoid_rewrite star_expand_r at 2.
Time Split.
Time *
Time (do 2 Left).
Time *
Time Left.
Time Right.
Time (unfold exec_recover, rexec_seq, rexec_seq_partial in Hcase2).
Time left_assoc rew Hcase2.
Time -
Time rew denesting.
Time Right.
Time (unfold exec_recover, rexec_seq, rexec_seq_partial in Hcase3).
Time left_assoc rew Hcase3.
Time Qed.
Time
Theorem exec_recover_partial_noop (p : rec_seq) :
  pure tt ---> exec_recover_partial p.
Time Proof.
Time (unfold exec_recover_partial).
Time rew<- seq_star_none.
Time (apply exec_seq_partial_noop).
Time Qed.
Time
Lemma exec_partial_err_exec_err T (p : proc T) s :
  exec_partial p s Err <-> exec p s Err.
Time Proof.
Time split.
Time -
Time (econstructor; eauto).
Time -
Time (destruct 1 as [?| (a, (b, (Hpart, Hbad)))]; auto).
Time (destruct a as [| (?, [])]; inversion Hbad).
Time Qed.
Time
Lemma exec_seq_partial_err_exec_seq_err (rec : rec_seq) 
  s : exec_seq_partial rec s Err -> exec_seq rec s Err.
Time Proof.
Time revert s.
Time (induction rec; auto; intros s).
Time (unfold exec_seq_partial).
Time (intros [?| Hhd]).
Time -
Time (eapply and_then_err_cancel; eauto).
Time -
Time (apply bind_pure_no_err in Hhd).
Time left.
Time (apply exec_partial_err_exec_err; auto).
Time Qed.
Time
Lemma rexec_partial_err_rexec_err T `(p : proc T) 
  (rec : rec_seq) s : rexec_partial p rec s Err -> rexec p rec s Err.
Time Proof.
Time (unfold rexec_partial, rexec, exec_recover, exec_recover_partial).
Time (intros H).
Time (eapply requiv_err_elim in H; swap 1 2).
Time {
Time (repeat setoid_rewrite  <- bind_assoc).
Time reflexivity.
Time }
Time (eapply requiv_err_elim; swap 1 2).
Time {
Time (repeat setoid_rewrite  <- bind_assoc).
Time reflexivity.
Time }
Time (eapply and_then_err_cancel; eauto).
Time (simpl).
Time (intros).
Time (apply exec_seq_partial_err_exec_seq_err; auto).
Time Qed.
Time
Lemma exec_err_rexec_err T (p : proc T) rec s :
  exec p s Err -> rexec p rec s Err.
Time Proof.
Time (intros Herr).
Time (apply exec_partial_err_exec_err in Herr).
Time (unfold rexec).
Time (left; eauto).
Time Qed.
Time
Lemma rexec_singleton_ret_intro T (p : proc T) \207\1311 
  \207\1312 \207\1312' tp :
  exec_partial p \207\1311 (Val \207\1312 tp) ->
  crash_step \207\1312 (Val \207\1312' tt) ->
  rexec p (rec_singleton (Ret tt)) \207\1311 (Val \207\1312' tt).
Time Proof.
Time (intros).
Time (do 2 eexists; split; eauto).
Time (do 2 eexists; split; eauto).
Time (do 2 eexists; split; simpl; eauto).
Time {
Time (eapply seq_star_refl).
Time }
Time (do 2 eexists; split; simpl; [  | econstructor ]).
Time (do 2 eexists; split; eauto).
Time econstructor.
Time (simpl).
Time econstructor.
Time Unshelve.
Time exact tt.
Time Qed.
Time
Inductive seq_star_exec_steps {R} (rec : proc R) :
nat -> relation State State unit :=
  | sses_nil : forall \207\131 o, seq_star_exec_steps rec O \207\131 (Val \207\131 o)
  | sses_cons_val :
      forall \207\1311 \207\1311' \207\1312 ret \207\1313 k n,
      crash_step \207\1311 (Val \207\1311' tt) ->
      bind_rep_n n exec_pool (existT _ R rec :: nil) \207\1311' (Val \207\1312 ret) ->
      seq_star_exec_steps rec k \207\1312 \207\1313 ->
      seq_star_exec_steps rec (S n + S k) \207\1311 \207\1313
  | sses_cons_err :
      forall \207\1311 \207\1311' n,
      crash_step \207\1311 (Val \207\1311' tt) ->
      bind_rep_n n exec_pool (existT _ R rec :: nil) \207\1311' Err ->
      seq_star_exec_steps rec (S n) \207\1311 Err.
Time
Context (crash_non_err : forall s1 ret, crash_step s1 ret -> ret <> Err).
Time
Lemma seq_star_exec_steps_intro {R} (rec : proc R) 
  \207\131halt ret :
  seq_star (_ <- crash_step; exec_halt rec) \207\131halt ret ->
  exists k, seq_star_exec_steps rec k \207\131halt ret.
Time Proof.
Time (intros Hstar).
Time (induction Hstar as [| ? ? ? [] Hstep| ? Hstep]; subst).
Time -
Time exists O.
Time econstructor.
Time -
Time (destruct Hstep as ([], (\207\131', (Hcrash, Hexec)))).
Time (edestruct IHHstar as (k, Hrest); auto).
Time (destruct Hexec as (?, (?, (Hpartial, Hpure)))).
Time (inversion Hpure; subst).
Time (apply bind_star_inv_rep_n in Hpartial as (n, Hbind)).
Time (exists (S n + S k)%nat; econstructor; eauto).
Time -
Time (destruct Hstep as [Hcrash| ([], (\207\131', (Hcrash, Hexec)))]).
Time {
Time exfalso.
Time (eapply crash_non_err in Hcrash).
Time eauto.
Time }
Time (apply bind_pure_no_err in Hexec).
Time (apply exec_partial_equiv_exec_partial_n in Hexec as (n, ?)).
Time eexists.
Time (eapply sses_cons_err; eauto).
Time Qed.
Time
Lemma seq_star_exec_steps_elim {R} (rec : proc R) 
  \207\131halt ret k :
  seq_star_exec_steps rec k \207\131halt ret ->
  seq_star (_ <- crash_step; exec_halt rec) \207\131halt ret.
Time Proof.
Time (intros Hstar).
Time (induction Hstar as [| ? ? ? ? ? k n| ? ? ?]; subst).
Time -
Time econstructor.
Time -
Time (econstructor; eauto).
Time (do 2 eexists; split; eauto).
Time (do 2 eexists; split; [  | econstructor ]).
Time (apply exec_partial_equiv_exec_partial_n; eexists; eauto).
Time -
Time (eapply seq_star_one_more_err).
Time right.
Time (do 2 eexists; split; eauto).
Time left.
Time (apply exec_partial_equiv_exec_partial_n; eexists; eauto).
Time Qed.
Time
Inductive rexec_n {T} {R} (e : proc T) (rec : proc R) 
(n : nat) : relation State State unit :=
    rexec_n_intro :
      forall \207\1311 ret n1 n2 n3,
      (n1 + n2 + n3 = n)%nat ->
      (_ <- exec_partial_n e n1; _ <- seq_star_exec_steps rec n2;
       _ <- crash_step; _ <- exec_n rec n3; pure tt) \207\1311 ret ->
      rexec_n e rec n \207\1311 ret.
Time
Lemma rexec_equiv_rexec_n {T} {R} (e : proc T) (rec : proc R) 
  \207\1311 ret :
  (_ <- exec_partial e; _ <- seq_star (_ <- crash_step; exec_halt rec);
   _ <- crash_step; _ <- exec rec; pure tt) \207\1311 ret <->
  (exists n, rexec_n e rec n \207\1311 ret).
Time Proof.
Time split.
Time -
Time (destruct ret as [\207\1312 tt| ]).
Time *
Time
(intros (tp, (\207\1311a, (Hpartial, ([], (?, (Hstar, ([], (?, (?, Hexec)))))))))).
Time (apply exec_partial_equiv_exec_partial_n in Hpartial as (n1, ?)).
Time (apply seq_star_exec_steps_intro in Hstar as (n2, ?); eauto).
Time (destruct Hexec as (?, (?, (Hexec, Hpure))); inversion Hpure; subst).
Time (apply exec_equiv_exec_n in Hexec as (n3, ?)).
Time (exists (n1 + n2 + n3)%nat; econstructor; eauto).
Time (repeat (do 2 eexists; split; eauto)).
Time *
Time (intros [Hpartial| (tp, (\207\1311a, (Hpartial, Hrest)))]).
Time {
Time (apply exec_partial_equiv_exec_partial_n in Hpartial as (n1, ?)).
Time exists n1.
Time exists n1 O O.
Time **
Time (do 2 rewrite <- plus_n_O).
Time auto.
Time **
Time (left; eauto).
Time }
Time (apply exec_partial_equiv_exec_partial_n in Hpartial as (n1, ?)).
Time (destruct Hrest as [Hstar| ([], (?, (Hstar, Hexec)))]).
Time {
Time (apply seq_star_exec_steps_intro in Hstar as (n2, ?); eauto).
Time exists (n1 + n2)%nat.
Time exists n1 n2 O.
Time **
Time (rewrite <- plus_n_O).
Time auto.
Time **
Time right.
Time (do 2 eexists; split; eauto).
Time (left; eauto).
Time }
Time (apply seq_star_exec_steps_intro in Hstar as (n2, ?); eauto).
Time (destruct Hexec as [| ([], (?, (?, Hexec)))]).
Time {
Time exfalso.
Time (eapply crash_non_err; eauto).
Time }
Time (apply bind_pure_no_err, exec_equiv_exec_n in Hexec as (n3, ?)).
Time exists (n1 + n2 + n3)%nat.
Time (exists n1 n2 n3; auto).
Time right.
Time (do 2 eexists; split; eauto).
Time right.
Time (do 2 eexists; split; eauto).
Time right.
Time (do 2 eexists; split; eauto).
Time (left; eauto).
Time -
Time (intros (n, H)).
Time (inversion H as [? ? n1 n2 n3 Heq Hstep]; subst).
Time (destruct ret as [\207\1312 tt| ]).
Time *
Time
(destruct Hstep
  as (tp, (\207\1311a, (Hpartial, ([], (?, (Hstar, ([], (?, (?, Hexec)))))))))).
Time (destruct Hexec as (?, (?, (?, Hpure)))).
Time (inversion Hpure; subst).
Time (do 2 eexists; split; eauto).
Time {
Time (eapply exec_partial_equiv_exec_partial_n; eexists; eauto).
Time }
Time (do 2 eexists; split; eauto).
Time {
Time (eapply seq_star_exec_steps_elim; eauto).
Time }
Time (do 2 eexists; split; eauto).
Time (do 2 eexists; split; eauto).
Time {
Time (eapply exec_equiv_exec_n; eexists; eauto).
Time }
Time *
Time (destruct Hstep as [Hpartial| (tp, (\207\1311a, (Hpartial, Hrest)))]).
Time {
Time left.
Time (eapply exec_partial_equiv_exec_partial_n; eexists; eauto).
Time }
Time (destruct Hrest as [Hstar| ([], (?, (Hstar, Hexec)))]).
Time {
Time right.
Time (do 2 eexists; split).
Time {
Time (eapply exec_partial_equiv_exec_partial_n; eexists; eauto).
Time }
Time {
Time left.
Time (eapply seq_star_exec_steps_elim; eauto).
Time }
Time }
Time right.
Time (do 2 eexists; split; eauto).
Time {
Time (eapply exec_partial_equiv_exec_partial_n; eexists; eauto).
Time }
Time right.
Time (do 2 eexists; split; eauto).
Time {
Time (eapply seq_star_exec_steps_elim; eauto).
Time }
Time (destruct Hexec as [| ([], (?, (?, Hexec)))]).
Time {
Time exfalso.
Time (eapply crash_non_err; eauto).
Time }
Time right.
Time (do 2 eexists; split; eauto).
Time (apply bind_pure_no_err in Hexec).
Time left.
Time (eapply exec_equiv_exec_n; eauto).
Time Qed.
Time
Lemma rexec_equiv_rexec_n'_val {T} {R} (e : proc T) 
  (rec : proc R) \207\1311 \207\1312 :
  ~ rexec e (rec_singleton rec) \207\1311 Err ->
  rexec e (rec_singleton rec) \207\1311 (Val \207\1312 tt) <->
  (exists n, rexec_n e rec n \207\1311 (Val \207\1312 tt)).
Time Proof.
Time (intros Hnoerr).
Time split.
Time -
Time (intros Hrexec; apply rexec_equiv_rexec_n; eauto).
Time (eapply requiv_no_err_elim in Hrexec; swap 1 3).
Time {
Time eassumption.
Time }
Time {
Time (unfold rexec, exec_recover).
Time setoid_rewrite exec_seq_partial_singleton.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- seq_unit_sliding_equiv.
Time setoid_rewrite bind_assoc.
Time reflexivity.
Time }
Time eauto.
Time -
Time (intros (n, Hrexec_n)).
Time (eapply requiv_no_err_elim'; swap 1 3).
Time {
Time eassumption.
Time }
Time {
Time (unfold rexec, exec_recover).
Time setoid_rewrite exec_seq_partial_singleton.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- seq_unit_sliding_equiv.
Time setoid_rewrite bind_assoc.
Time reflexivity.
Time }
Time (eapply rexec_equiv_rexec_n; eauto).
Time Qed.
Time
Lemma rexec_equiv_rexec_n'_err {T} {R} (e : proc T) 
  (rec : proc R) \207\1311 :
  rexec e (rec_singleton rec) \207\1311 Err <-> (exists n, rexec_n e rec n \207\1311 Err).
Time Proof.
Time split.
Time -
Time (intros Hrexec; apply rexec_equiv_rexec_n; eauto).
Time (eapply requiv_err_elim in Hrexec).
Time {
Time eassumption.
Time }
Time {
Time (unfold rexec, exec_recover).
Time setoid_rewrite exec_seq_partial_singleton.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- seq_unit_sliding_equiv.
Time setoid_rewrite bind_assoc.
Time reflexivity.
Time }
Time -
Time (intros (n, Hrexec_n)).
Time (eapply requiv_err_elim).
Time {
Time (eapply rexec_equiv_rexec_n; eauto).
Time }
Time {
Time symmetry.
Time (unfold rexec, exec_recover).
Time setoid_rewrite exec_seq_partial_singleton.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite  <- seq_unit_sliding_equiv.
Time setoid_rewrite bind_assoc.
Time reflexivity.
Time }
Time Qed.
Time
Definition exec_or_rexec_n {T} {R} (p : proc T) (rec : proc R) 
  n :=
  v <- exec_n p n; _ <- finish_step; pure (Normal v) + 
  v <- rexec_n p rec n; _ <- fst_lift (puts (fun _ => 1));
  pure (Recovered (existT (fun T => T) _ v)).
Time
Lemma exec_or_rexec_equiv_exec_or_rexec_n {T} {R} 
  (e : proc T) (rec : proc R) \207\1311 \207\1312 out :
  ~ exec_or_rexec e (rec_singleton rec) \207\1311 Err ->
  exec_or_rexec e (rec_singleton rec) \207\1311 (Val \207\1312 out) <->
  (exists n, exec_or_rexec_n e rec n \207\1311 (Val \207\1312 out)).
Time Proof.
Time (intros Hno_err).
Time split.
Time -
Time (intros [Hexec| Hrexec]).
Time *
Time (destruct Hexec as ([], (?, (Hexec, Hpure)))).
Time (inversion Hpure; subst).
Time (eapply exec_equiv_exec_n in Hexec as (n, ?)).
Time exists n.
Time left.
Time (do 2 eexists; split; eauto).
Time *
Time (destruct Hrexec as ([], (?, (Hexec, Hpure)))).
Time (inversion Hpure; subst).
Time (eapply rexec_equiv_rexec_n'_val in Hexec as (n, ?)).
Time {
Time exists n.
Time right.
Time (do 2 eexists; split; eauto).
Time }
Time {
Time (intros Herr).
Time (eapply Hno_err).
Time right.
Time (econstructor; eauto).
Time }
Time -
Time (intros (n, [Hexec| Hrexec])).
Time *
Time (destruct Hexec as ([], (?, (Hexec, Hpure)))).
Time (inversion Hpure; subst).
Time left.
Time (do 2 eexists; split; eauto).
Time (eapply exec_equiv_exec_n).
Time (eexists; eauto).
Time *
Time (destruct Hrexec as ([], (?, (Hexec, Hpure)))).
Time (inversion Hpure; subst).
Time right.
Time (do 2 eexists; split; eauto).
Time (eapply rexec_equiv_rexec_n'_val).
Time {
Time (intros Herr).
Time (eapply Hno_err).
Time right.
Time (econstructor; eauto).
Time }
Time {
Time (eexists; eauto).
Time }
Time Qed.
Time
Fixpoint proc_exec_seq_n {T R} (p : proc_seq T) (rec : proc R) 
n :=
  match p with
  | Proc_Seq_Nil v => fun s1 ret => n = 5 /\ (pure v) s1 ret
  | Proc_Seq_Bind p f =>
      fun s1 ret =>
      exists n1 n2,
        (n = 5 + n1 + S n2)%nat /\
        (v <- exec_or_rexec_n p rec n1; proc_exec_seq_n (f v) rec n2) s1 ret
  end.
Time
Lemma proc_exec_seq_equiv_proc_exec_seq_n {T} {R} 
  (p : proc_seq T) (rec : proc R) \207\1311 \207\1312 out :
  ~ proc_exec_seq p (rec_singleton rec) \207\1311 Err ->
  proc_exec_seq p (rec_singleton rec) \207\1311 (Val \207\1312 out) <->
  (exists n, proc_exec_seq_n p rec n \207\1311 (Val \207\1312 out)).
Time Proof.
Time revert \207\1311.
Time (induction p as [| ? ? ? IH]; intros \207\1311 Hno_err).
Time *
Time (split; simpl).
Time **
Time intuition eauto.
Time **
Time (intros (?, []); eauto).
Time *
Time split.
Time **
Time (intros (?, (?, (Hhd, Htl)))).
Time (eapply IH in Htl as (n2, ?)).
Time {
Time (eapply exec_or_rexec_equiv_exec_or_rexec_n in Hhd as (n1, ?)).
Time {
Time exists (5 + n1 + S n2)%nat.
Time (do 2 eexists; split; eauto).
Time (do 2 eexists; split; eauto).
Time }
Time {
Time (intros Herr).
Time (eapply Hno_err).
Time (left; eauto).
Time }
Time }
Time {
Time (intros Herr).
Time (eapply Hno_err).
Time right.
Time (do 2 eexists; split; eauto).
Time }
Time **
Time (intros (n, (?, (?, (?, (?, (?, (Hhd, Htl)))))))).
Time subst.
Time (do 2 eexists; split).
Time {
Time (eapply exec_or_rexec_equiv_exec_or_rexec_n; eauto).
Time (intros Herr).
Time (eapply Hno_err).
Time (left; eauto).
Time }
Time {
Time (eapply IH; eauto).
Time (intros Herr).
Time (eapply Hno_err).
Time (right; eauto).
Time (do 2 eexists; split; eauto).
Time (eapply exec_or_rexec_equiv_exec_or_rexec_n; eauto).
Time (intros Herr').
Time (eapply Hno_err).
Time (left; eauto).
Time }
Time Qed.
Time End Dynamics.
Time Arguments exec_halt_noop [Op] [OpState] [sem] [T].
Time Arguments exec_halt_finish [Op] [OpState] [sem] [T].
Time Arguments exec_halt_ret [Op] [OpState] [sem] [T].
