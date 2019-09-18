Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIyHzwp"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
Require Import Spec.Proc.
Require Import Spec.Hoare.
From Transitions Require Import Relations Rewriting.
Require Import Abstraction.
Require Import Layer.
Section Abstraction.
Context (AState CState : Type).
Context (absr : relation AState CState unit).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Unset Silent.
