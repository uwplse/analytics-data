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
Declare Scope btjt_scope.
Reserved Notation "'|' t '|'" (at level 20).
Fixpoint inv_depth (t : ty) :=
  match t with
  | TCName _ => 0
  | TPair t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TUnion t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TRef t' => 1 + | t' |
  end
where "'|' t '|'" := (inv_depth t) : btjt_scope.
Delimit Scope btjt_scope with btjt.
Inductive atom_type : ty -> Prop :=
  | AT_CName : forall c : cname, atom_type (TCName c)
  | AT_Pair : forall ta1 ta2 : ty, atom_type ta1 -> atom_type ta2 -> atom_type (TPair ta1 ta2)
  | AT_Ref : forall t : ty, in_nf t -> atom_type (TRef t)
with in_nf : ty -> Prop :=
  | NF_Atom : forall ta : ty, atom_type ta -> in_nf ta
  | NF_Union : forall t1 t2 : ty, in_nf t1 -> in_nf t2 -> in_nf (TUnion t1 t2).
Scheme atom_type_mut := Induction for atom_type Sort Prop
  with in_nf_mut := Induction for in_nf Sort Prop.
(* Auto-generated comment: Failed. *)
