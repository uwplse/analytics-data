Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCYzfGC"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
From Coq Require Import Morphisms.
From Tactical Require Import ProofAutomation.
Unset Silent.
From Transitions Require Import Relations.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhYHqpm"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSlNpkl"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
Import RelationNotations.
Generalizable Variables all.
Class NonError {A} {B} {T} (r : relation A B T) :=
    non_erroring : forall x, ~ r x (Err B T).
Instance nonError_bind  `{NonError A B T1 r1}
 `{forall x, @NonError B C T2 (r2 x)}: (NonError (and_then r1 r2)).
Proof.
(unfold NonError, not, and_then in *).
(intuition idtac; propositional; eauto).
Qed.
Instance nonError_or  `{NonError A B T r1} `{!NonError r2}:
 (NonError (r1 + r2)%rel).
Proof.
(unfold NonError, not, rel_or in *; intros).
(intuition idtac; propositional; eauto).
Qed.
Instance nonError_equiv : (Proper (@requiv A B T ==> iff) NonError).
Proof.
firstorder.
Qed.
Instance nonError_star  `{NonError A A T r1}: (NonError (seq_star r1)).
Proof.
(unfold NonError, not in *; intros).
(remember (Err A T)).
(induction H0; try congruence; eauto).
Qed.
Instance nonError_bind_star  `{forall x, @NonError A A T (r1 x)}:
 (forall x, NonError (bind_star r1 x)).
Proof.
(unfold NonError, not in *; intros).
(remember (Err A T)).
(induction H0; try congruence; eauto).
Unset Silent.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqG9OqQC"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqC9qYgb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Timeout 1 Check @List.In.
Timeout 1 Check @PeanoNat.Nat.le_decidable.
Timeout 1 Check @non_erroring.
Timeout 1 Check @nonError_or.
Timeout 1 Check @nonError_or.
Timeout 1 Check @nonError_or.
Timeout 1 Check @nonError_or.
Timeout 1 Check @nonError_or.
Timeout 1 Check @nonError_or.
Timeout 1 Check @forall_def.
Timeout 1 Check @readNone.
Timeout 1 Check @readNone.
Timeout 1 Check @NonError.
Timeout 1 Check @NonError.
Timeout 1 Check @NonError.
Timeout 1 Check @NonError.
Check puts.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Instance nonError_puts  `(f : A -> A): (NonError (puts f)).
Unset Silent.
Proof.
(hnf).
