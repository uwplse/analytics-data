Require Import Setoid.
Require Import Morphisms.
Require Import Proc.
From Classes Require Import Classes.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Tactical.ProofAutomation.
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
(induction p; simpl in *; norm).
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
-
Left.
auto.
Qed.
Theorem exec_crash_ret T (v : T) : exec_crash (Ret v) <---> crash_step.
Proof.
reflexivity.
Qed.
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
rew exec_crash_idem.
Qed.
Theorem monad_assoc `(p1 : proc T1) `(p2 : T1 -> proc T2)
  `(p3 : T2 -> proc T3) :
  Bind (Bind p1 p2) p3 <==> Bind p1 (fun v => Bind (p2 v) p3).
Proof.
(split; simpl; norm).
(repeat setoid_rewrite bind_dist_l).
norm.
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
