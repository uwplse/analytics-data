Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Lists.List.
Require Import
  Coq.Sorting.Permutation.
Require Import
  Coq.Sorting.Sorted.
Require Import Orders.
Require Import FunInd.
Require Import Recdef.
Require Import Extraction.
Require Import
  ExtrOcamlBasic.
Require Import
  Coq.Program.Equality.
Require Import Math.
#[local]
Coercion is_true : bool >->
 Sortclass.
Module Sort.
Parameter (t : Type).
Parameter
  (leb : t -> t -> bool).
Notation "a <=? b" :=
  (leb a b).
Notation "! a " := 
  (negb a) (at level 10).
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-26 23:37:51.040000.*)

