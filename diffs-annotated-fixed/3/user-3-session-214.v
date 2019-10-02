Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCYzfGC"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import Morphisms.
From Tactical Require Import ProofAutomation.
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
Check puts.
Instance nonError_puts  `(f : A -> A): (NonError (puts f)).
Proof.
(unfold NonError, not, puts; intros).
congruence.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqntCw84"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqPFyTBc"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKp0FVe"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Check reads.
Instance nonError_reads  `(f : A -> T): (NonError (reads f)).
Proof.
(unfold NonError, not, reads; intros).
congruence.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbPqPYD"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqq7Bakj"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtVIxsc"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Instance nonError_none : (@NonError A A T none).
(unfold NonError, not, none; intros).
auto.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqwXsKKb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqErDP1i"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOn8jq8"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
(* Auto-generated comment: Succeeded. *)

