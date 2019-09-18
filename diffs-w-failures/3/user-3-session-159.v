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
Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.
Unset Silent.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXI6axi"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0BLEGv"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @rimpl_to_requiv.
Timeout 1 Check @rimpl_to_requiv.
Timeout 1 Check @Nat.bitwise.
Timeout 1 Check @Val.
Timeout 1 Check @Err.
Timeout 1 Check @Err.
Timeout 1 Check @False.
Timeout 1 Check @False.
Timeout 1 Check @False.
Timeout 1 Check @denesting.
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
Timeout 1 Check @In.
Timeout 1 Check @absr.
Timeout 1 Check @absr.
Timeout 1 Check @absr.
Timeout 1 Check @absr.
Timeout 1 Check @absr.
Timeout 1 Check @readNone.
Timeout 1 Check @readNone.
Timeout 1 Check @NonError.NonError.
Timeout 1 Check @NonError.NonError.
Timeout 1 Check @NonError.NonError.
Timeout 1 Check @NonError.NonError.
Timeout 1 Check @NonError.NonError.
Timeout 1 Check @absr.
Timeout 1 Check @absr.
Timeout 1 Check @absr.
Instance absr_non_error : (NonError absr).
