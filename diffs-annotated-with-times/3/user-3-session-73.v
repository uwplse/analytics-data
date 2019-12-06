Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIyHzwp"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Spec.Proc.
Require Import Spec.Hoare.
From Transitions Require Import Relations Rewriting NonError.
Require Import Abstraction.
Require Import Layer.
Section Abstraction.
Context (AState CState : Type).
Context (absr : relation AState CState unit).
Context (absr_ok : NonError absr).
Definition refine_spec T R (spec : Specification T R AState) :
  AState -> Specification T R CState :=
  fun s cs =>
  {|
  pre := absr s (Val cs tt) /\ (spec s).(pre);
  post := fun cs' r =>
          exists s', absr s' (Val cs' tt) /\ (spec s).(post) s' r;
  alternate := fun cs' r =>
               exists s', absr s' (Val cs' tt) /\ (spec s).(alternate) s' r |}.
Context A_Op C_Op `(a_sem : Dynamics A_Op AState)
 `(c_sem : Dynamics C_Op CState).
Import RelationNotations.
Lemma proc_rspec_refine_exec T R (p : proc C_Op T) 
  (rec : proc C_Op R) spec :
  (forall t, proc_rspec c_sem p rec (refine_spec spec t)) ->
  (forall sA sC, absr sA (Val sC tt) -> (spec sA).(pre)) ->
  _ <- absr; exec c_sem p ---> v <- spec_exec spec; _ <- absr; pure v.
Proof.
(intros Hprspec Habstr_pre).
Admitted.
Lemma proc_rspec_refine_rec T R (p : proc C_Op T) 
  (rec : proc C_Op R) spec :
  (forall t, proc_rspec c_sem p rec (refine_spec spec t)) ->
  (forall sA sC, absr sA (Val sC tt) -> (spec sA).(pre)) ->
  _ <- absr; rexec c_sem p rec ---> v <- spec_aexec spec; _ <- absr; pure v.
Proof.
(intros Hprspec Habstr_pre).
Admitted.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqheJlbx"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqRwhwTy"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Lemma proc_rspec_crash_refines T (p : proc C_Op T) 
  (rec : proc C_Op unit) spec op :
  (forall t, proc_rspec c_sem p rec (refine_spec spec t)) ->
  (forall sO sT, absr sO (Val sT tt) -> (spec sO).(pre)) ->
  spec_exec spec ---> exec a_sem (Call op) ->
  spec_aexec spec
  --->
   a_sem.(crash_step) + (a_sem.(step) op;; a_sem.(crash_step)) ->
  crash_refines absr c_sem p rec (a_sem.(step) op)
    (a_sem.(crash_step) + (a_sem.(step) op;; a_sem.(crash_step))).
Proof.
(intros ? ? He Ha).
(unfold crash_refines, refines).
split.
-
setoid_rewrite  <- He.
(eapply proc_rspec_refine_exec; eauto).
-
setoid_rewrite  <- Ha.
(eapply proc_rspec_refine_rec; eauto).
Qed.
Lemma proc_rspec_crash_refines_op T (p : proc C_Op T) 
  (rec : proc C_Op unit) spec (op : A_Op T) :
  (forall sA sC,
   absr sA sC tt -> proc_rspec c_sem p rec (refine_spec spec sA)) ->
  (forall sA sC, absr sA sC tt -> (spec sA).(pre)) ->
  (forall sA sC sA' v,
   absr sA' sC tt ->
   (spec sA).(post) sA' v -> (op_spec a_sem op sA).(post) sA' v) ->
  (forall sA sC sA' v,
   absr sA sC tt ->
   (spec sA).(alternate) sA' v -> (op_spec a_sem op sA).(alternate) sA' v) ->
  crash_refines absr c_sem p rec (a_sem.(step) op)
    (a_sem.(crash_step) + (a_sem.(step) op;; a_sem.(crash_step))).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-07 13:54:09.540000.*)

