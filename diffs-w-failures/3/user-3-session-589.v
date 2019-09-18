Time Require Import Setoid.
Time Require Import Morphisms.
Time Require Import Proc.
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
