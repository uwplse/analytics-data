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
Definition absr : relation DB.l.(State) Var.l.(State) unit :=
  fun l s _ => fst s = fold_right plus 0 l /\ snd s = length l.
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-07 13:59:26.670000.*)

