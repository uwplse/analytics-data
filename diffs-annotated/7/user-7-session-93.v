Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Create HintDb DBBetaJulia.
Inductive cname : Type :=
  | NInt : _
  | NFlt : _
  | NStr : _.
Definition varid : Type := nat.
Inductive ty : Type :=
  | TCName : cname -> ty
  | TPair : ty -> ty -> ty
  | TUnion : ty -> ty -> ty
  | TRef : ty -> ty
  | TVar : varid -> ty
  | TExist : varid -> ty -> ty.
Definition tint := TCName NInt.
Definition vX := 1.
Definition vY := 2.
Definition vZ := 3.
Definition tX := TVar vX.
Definition tY := TVar vY.
Definition teXX := TExist vX vX.
(* Failed. *)
