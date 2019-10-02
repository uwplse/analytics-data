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
Inductive ty : Type :=
  | TCName : cname -> ty
  | TPair : ty -> ty -> ty
  | TUnion : ty -> ty -> ty
  | TRef : ty -> ty.
Definition tint := TCName NInt.
Definition tflt := TCName NFlt.
Definition tstr := TCName NStr.
Definition tIntInt := TPair tint tint.
Inductive value_type : ty -> Prop :=
  | VT_CName : forall cn, value_type (TCName cn)
  | VT_Pair : forall v1 v2, value_type v1 -> value_type v2 -> value_type (TPair v1 v2)
  | VT_Ref : forall t, value_type (TRef t).
Hint Constructors value_type: DBBetaJulia.
Declare Scope btjm_scope.
Reserved Notation "'|'t'|'" (at level 20).
(* Auto-generated comment: Failed. *)

