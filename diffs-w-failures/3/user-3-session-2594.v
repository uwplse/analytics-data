Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2PZidX"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
From Coq Require Import FunInd Recdef.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @PeanoNat.Nat.mod_small.
Set Printing Width 78.
From Coq Require Import PeanoNat.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqPFg0QW"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbXPA9y"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
From Armada Require Import Goose.Machine.
Opaque Nat.modulo Nat.div.
#[local]Obligation Tactic := (intros; simpl; subst).
Unset Silent.
