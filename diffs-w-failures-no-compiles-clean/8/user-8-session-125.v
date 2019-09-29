Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqnNPFXM"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqyNKPug"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Bullet Behavior Strict Subproofs.
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.
Lemma init_qubit1 : (\226\159\166 init true \226\159\167) (I 1) == \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
(matrix_denote; lma).
