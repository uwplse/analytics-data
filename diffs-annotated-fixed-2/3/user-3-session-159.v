Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0oM8Ug"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Examples.StatDb.Impl.
Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXI6axi"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0BLEGv"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l res =>
  match res with
  | Val s _ => fst s = fold_right plus 0 l /\ snd s = length l
  | Err _ _ => False
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqiQZm2s"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq4uHC6k"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Instance absr_non_error : (NonError absr).
(* Auto-generated comment: Succeeded. *)

