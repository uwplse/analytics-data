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
Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l s _ => fst s = fold_right plus 0 l /\ snd s = length l.
