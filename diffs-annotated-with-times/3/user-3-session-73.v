Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIyHzwp"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Spec.Proc.
Require Import Spec.Hoare.
From Transitions Require Import Relations Rewriting.
Require Import Abstraction.
Require Import Layer.
Section Abstraction.
Context (AState CState : Type).
Context (absr : relation AState CState unit).
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-07 13:54:02.390000.*)

