Require Import Setoid.
From Tactical Require Import Propositional.
Require Import Spec.Proc.
Require Import Morphisms.
Require Import Proc.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Import RelationNotations.
Section Abstraction.
Context (AState CState : Type).
Context (absr : relation AState CState unit).
Definition refines T (p : relation CState CState T)
  (spec : relation AState AState T) := absr;; p ---> v <- spec; absr;; pure v.
Theorem refine_unfolded_iff T (p : relation CState CState T)
  (spec : relation AState AState T) :
  (forall s s__a,
   absr s__a s tt ->
   forall s' v,
   p s s' v -> exists s__a', spec s__a s__a' v /\ absr s__a' s' tt) <->
  refines p spec.
From Classes Require Import Classes.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Tactical.ProofAutomation.
Proof.
(unfold refines, rimpl, and_then, pure; split).
-
propositional.
(destruct o1).
Import RelationNotations.
Section Dynamics.
Context `(sem : Dynamics Op State).
Notation proc := (proc Op).
Notation step := sem.(step).
Notation crash_step := sem.(crash_step).
Notation exec_crash := (exec_crash sem).
Notation exec := (exec sem).
Notation exec_recover := (exec_recover sem).
Notation rexec := (rexec sem).
Hint Resolve rimpl_refl requiv_refl: core.
Theorem exec_crash_finish T (p : proc T) :
  exec p;; crash_step ---> exec_crash p.
Proof.
(eapply H in H0; eauto; propositional).
(induction p; simpl in *; norm).
eauto  10.
-
(intros).
(edestruct H; eauto).
propositional.
(destruct o1).
eauto  10.
Qed.
Theorem refine_unfolded T (p : relation CState CState T)
  (spec : relation AState AState T) :
  (forall s s__a,
   absr s__a s tt ->
   forall s' v,
   p s s' v -> exists s__a', spec s__a s__a' v /\ absr s__a' s' tt) ->
  refines p spec.
Proof.
(eapply refine_unfolded_iff).
Qed.
Section Dynamics.
Context C_Op (c_sem : Dynamics C_Op CState).
Notation c_proc := (proc C_Op).
Notation c_exec := (exec c_sem).
Notation c_rexec := (rexec c_sem).
Definition crash_refines T R (p : c_proc T) (rec : c_proc R)
  (exec_spec : relation AState AState T)
  (rexec_spec : relation AState AState R) :=
  refines (c_exec p) exec_spec /\ refines (c_rexec p rec) rexec_spec.
End Dynamics.
End Abstraction.
Theorem refines_transitive_abs State1 State2 State3 
  abs1 abs2 T (spec1 : relation State1 State1 T)
  (spec2 : relation State2 State2 T) (spec3 : relation State3 State3 T) :
  refines abs1 spec1 spec2 ->
  refines abs2 spec2 spec3 -> refines (abs2;; abs1) spec1 spec3.
Proof.
(unfold refines; norm; intros).
-
(rewrite <- rel_or_intror).
reflexivity.
-
setoid_rewrite H.
(rewrite <- rel_or_intror).
eauto.
Qed.
Theorem exec_crash_noop T (p : proc T) : crash_step ---> exec_crash p.
Proof.
(induction p; simpl in *; norm).
-
Left.
(setoid_rewrite H; norm).
-
Left.
(rewrite <- bind_assoc  at 1).
auto.
Qed.
Theorem exec_crash_ret T (v : T) : exec_crash (Ret v) <---> crash_step.
Proof.
reflexivity.
Qed.
(rewrite H0; norm).
Theorem exec_crash_idem T (p : proc T) :
  crash_step + exec_crash p <---> exec_crash p.
Proof.
(apply rimpl_or; auto using exec_crash_noop).
Qed.
Definition exec_equiv T (p p' : proc T) :=
  exec p <---> exec p' /\ exec_crash p <---> exec_crash p'.
#[global]Instance exec_equiv_equiv  T: (Equivalence (exec_equiv (T:=T))).
Proof.
(unfold exec_equiv).
(RelInstance_t; intuition idtac;
  repeat
   match goal with
   | H:_ <---> _ |- _ => apply requiv_to_rimpls in H
   | |- _ <---> _ => apply rimpl_to_requiv
   | _ => progress propositional
   end; auto; try (solve [ etransitivity; eauto ])).
Qed.
Infix "<==>" := exec_equiv (at level 70).
Theorem rexec_equiv T (p p' : proc T) R (rec : proc R) :
  p <==> p' -> rexec p rec <---> rexec p' rec.
Proof.
(unfold "<==>"; propositional).
(unfold rexec).
rew H0.
Qed.
#[global]
Instance exec_respectful  T:
 (Proper (@exec_equiv T ==> @requiv State State T) exec).
Proof.
(intros ? ? (?, ?); intuition).
Qed.
#[global]
Instance exec_crash_respectful  T:
 (Proper (@exec_equiv T ==> @requiv State State unit) exec_crash).
Proof.
(intros ? ? (?, ?); intuition).
Qed.
#[global]
Instance rexec_respectful  T R:
 (Proper (@exec_equiv T ==> eq ==> @requiv State State R) rexec).
Proof.
(intros ? ? ? ? ? ->).
(eapply rexec_equiv; eauto).
Qed.
Theorem monad_left_id T T' (p : T' -> proc T) v : Bind (Ret v) p <==> p v.
Proof.
(split; simpl; norm).
Qed.
Theorem refines_respects_bind State1 State2 abs T1 
  T2 (r1 : relation State1 State1 T1) (r2 : T1 -> relation State1 State1 T2)
  (r1' : relation State2 State2 T1) (r2' : T1 -> relation State2 State2 T2) :
  refines abs r1 r1' ->
  (forall v, refines abs (r2 v) (r2' v)) ->
  refines abs (and_then r1 r2) (and_then r1' r2').
rew exec_crash_idem.
Proof.
(unfold refines; intros).
(rewrite <- bind_assoc).
Qed.
Theorem monad_assoc `(p1 : proc T1) `(p2 : T1 -> proc T2)
  `(p3 : T2 -> proc T3) :
  Bind (Bind p1 p2) p3 <==> Bind p1 (fun v => Bind (p2 v) p3).
(setoid_rewrite H; norm).
Proof.
(split; simpl; norm).
(repeat setoid_rewrite bind_dist_l).
(setoid_rewrite H0; norm).
Qed.
Theorem refines_respects_bind_unit State1 State2 abs 
  T2 (r1 : relation State1 State1 unit)
  (r2 : unit -> relation State1 State1 T2)
  (r1' : relation State2 State2 unit)
  (r2' : unit -> relation State2 State2 T2) :
  refines abs r1 r1' ->
  refines abs (r2 tt) (r2' tt) ->
  refines abs (and_then r1 r2) (and_then r1' r2').
Proof.
(intros).
(apply refines_respects_bind; auto).
(destruct v; auto).
Qed.
Theorem refines_respects_seq State1 State2 abs T
  (r1 r2 : relation State1 State1 T) (r1' r2' : relation State2 State2 T) :
  refines abs r1 r1' ->
  refines abs r2 r2' -> refines abs (r1;; r2) (r1';; r2').
Proof.
auto using refines_respects_bind.
Qed.
Theorem refines_respects_star State1 State2 abs T
  (r1 : relation State1 State1 T) (r2 : relation State2 State2 T) :
  refines abs r1 r2 -> refines abs (seq_star r1) (seq_star r2).
Proof.
(unfold refines).
(intros Hr).
(rew simulation_seq_value; auto).
Qed.
Theorem refines_respects_or State1 State2 abs T
  (r1 r1' : relation State1 State1 T) (r2 r2' : relation State2 State2 T) :
  refines abs r1 r2 ->
  refines abs r1' r2' -> refines abs (r1 + r1') (r2 + r2').
Proof.
(unfold refines).
(intros Hr Hr').
(repeat rew bind_dist_r).
norm.
(repeat rew bind_dist_l).
Qed.
Theorem exec_recover_bind `(rec1 : proc R) `(rec2 : R -> proc R') :
  exec_recover (Bind rec1 rec2)
  <--->
   v <- exec_recover rec1;
  v' <- bind_star (fun v => rexec (rec2 v) rec1) v;
  exec (rec2 v').
Proof.
(repeat unfold exec_recover, rexec; simpl; norm).
(rewrite ?bind_dist_r; norm).
(gen exec rec1 exec_crash rec1 crash_step; clear rec1;
  intros rec1 rec1_crash crash).
rew denesting.
rew Hr.
rew Hr'.
Qed.
rel_congruence.
(rewrite <- ?bind_assoc).
(rel_congruence; norm).
rew bind_sliding.
Qed.
Theorem rexec_to_exec_recover `(rec : proc R) :
  rexec rec rec ---> exec_recover rec.
Proof.
(unfold rexec, exec_recover).
setoid_rewrite  <- bind_assoc at 1.
rew seq_star1.
Qed.
Theorem exec_recover_to_rexec `(rec : proc R) :
  crash_step;; exec_recover rec ---> rexec rec rec.
Proof.
(unfold rexec, exec_recover).
(setoid_rewrite  <- exec_crash_noop at 2; norm).
Qed.
Lemma exec_crash_ret_proc `(rec : proc R) :
  exec_crash (Ret tt) ---> exec_crash rec.
Proof.
(induction rec; simpl; firstorder).
Qed.
Lemma exec_crash_ret_recover_fold `(rec : proc R) :
  _ <- exec_crash (Ret tt); exec_recover rec ---> exec_recover rec.
Proof.
setoid_rewrite (exec_crash_ret_proc rec).
(unfold exec_recover).
setoid_rewrite  <- bind_assoc.
(rewrite seq_star_fold; eauto).
Qed.
End Dynamics.
Arguments exec_crash_noop [Op] [State] [sem] [T].
Arguments exec_crash_finish [Op] [State] [sem] [T].
Arguments exec_crash_ret [Op] [State] [sem] [T].
