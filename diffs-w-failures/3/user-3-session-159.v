Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0oM8Ug"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
Require Import Examples.StatDb.Impl.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @True.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Ret.
Timeout 1 Check @SReqe_Reqe.
Timeout 1 Check @readNone.
Set Printing Width 78.
From Transitions Require Import NonError.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq4Wt8Ur"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgwakKd"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.
Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l res =>
  match res with
  | Val s _ => fst s = fold_right plus 0 l /\ snd s = length l
  | Err _ _ => False
  end.
Unset Silent.
Instance absr_non_error : (NonError absr).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq6gXHSd"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqdPtyvh"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Proof.
(hnf).
