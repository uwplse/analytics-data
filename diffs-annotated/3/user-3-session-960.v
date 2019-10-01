Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWfrXOb"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ProofIrrelevance.
From Coq Require Export String.
#[program]
Fixpoint nat_to_le base (x : nat) {measure x lt} :
list {x : nat | x < S (S base)} :=
  match x with
  | 0 => nil
  | _ =>
      let digit := x mod S (S base) in
      exist _ digit _ :: nat_to_le base (x / S (S base))
  end.
Next Obligation of nat_to_le_func.
Proof.
(apply PeanoNat.Nat.mod_upper_bound; auto).
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrgUG1T"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZulPN0"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Next Obligation of nat_to_le_func.
Proof.
subst digit.
(apply PeanoNat.Nat.div_lt; auto; try lia).
Qed.
Next Obligation of nat_to_le_func.
Proof.
lia.
Qed.
Next Obligation of nat_to_le_func.
Proof.
