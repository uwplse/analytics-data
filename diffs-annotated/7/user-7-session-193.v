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
Require Import Recdef.
Create HintDb DBBetaJulia.
Declare Scope btjt_scope.
Delimit Scope btjt_scope with btjt.
Open Scope btjt.
Inductive cname : Type :=
  | NInt : _
  | NFlt : _
  | NStr : _.
Inductive ty : Type :=
  | TCName : cname -> ty
  | TPair : ty -> ty -> ty
  | TUnion : ty -> ty -> ty
  | TExist : id -> ty -> ty
  | TBVar : id -> ty
  | TFVar : id -> ty
  | TEV : id -> ty.
Definition tint := TCName NInt.
Definition tflt := TCName NFlt.
Definition tstr := TCName NStr.
Definition tIntInt := TPair tint tint.
Definition vX := Id 1.
Definition vY := Id 2.
Definition vZ := Id 3.
Definition tX := TBVar vX.
Definition tY := TBVar vY.
Definition teXX := TExist vX tX.
Fixpoint FFV (t : ty) : id_set :=
  match t with
  | TCName _ => IdSet.empty
  | TPair t1 t2 => IdSet.union (FFV t1) (FFV t2)
  | TUnion t1 t2 => IdSet.union (FFV t1) (FFV t2)
  | TExist y t' => FFV t'
  | TBVar _ => IdSet.empty
  | TFVar y => IdSet.singleton y
  | TEV _ => IdSet.empty
  end.
Fixpoint FBV (t : ty) : id_set :=
  match t with
  | TCName _ => IdSet.empty
  | TPair t1 t2 => IdSet.union (FFV t1) (FFV t2)
  | TUnion t1 t2 => IdSet.union (FFV t1) (FFV t2)
  | TExist y t' => IdSet.remove y (FFV t')
  | TBVar y => IdSet.singleton y
  | TFVar _ => IdSet.empty
  | TEV _ => IdSet.empty
  end.
Definition free (X : id) (fvs : id_set) := IdSet.In X fvs.
Definition not_free (X : id) (fvs : id_set) := ~ IdSet.In X fvs.
Definition ffree_in_ty (X : id) (t : ty) := free X (FFV t).
Definition not_ffree_in_ty (X : id) (t : ty) := not_free X (FFV t).
Definition f_free_in_ty (X : id) (t : ty) := free X (FFV t).
Definition not_f_free_in_ty (X : id) (t : ty) := not_free X (FFV t).
Definition b_free_in_ty (X : id) (t : ty) := free X (FBV t).
Definition not_b_free_in_ty (X : id) (t : ty) := not_free X (FBV t).
Hint Unfold free not_free f_free_in_ty not_f_free_in_ty b_free_in_ty not_b_free_in_ty: DBBetaJulia.
Print IdSet.
Definition wf_ty (t : ty) := IdSet.Equal (FBV t) IdSet.empty.
(* Failed. *)
