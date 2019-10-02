Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIyHzwp"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Spec.Proc.
Require Import Spec.Hoare.
From Transitions Require Import Relations Rewriting.
Require Import Abstraction.
Require Import Layer.
Section Abstraction.
Context (AState CState : Type).
Context (absr : relation AState CState unit).
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
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKwOLDP"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Admitted.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq44j751"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrIRuKB"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Lemma proc_rspec_refine_rec T R (p : proc C_Op T) 
  (rec : proc C_Op R) spec :
  (forall t, proc_rspec c_sem p rec (refine_spec spec t)) ->
  (forall sA sC, absr sA (Val sC tt) -> (spec sA).(pre)) ->
  _ <- absr; rexec c_sem p rec ---> v <- spec_aexec spec; _ <- absr; pure v.
Proof.
(intros Hprspec Habstr_pre).
(intros sA sC b ([], (sTstart, (Hrd, Hexec)))).
(* Auto-generated comment: Succeeded. *)

