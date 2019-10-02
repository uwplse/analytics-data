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
  | TVar : id -> ty
  | TEV : id -> ty.
Definition tint := TCName NInt.
Definition tflt := TCName NFlt.
Definition tstr := TCName NStr.
Definition tIntInt := TPair tint tint.
Definition vX := Id 1.
Definition vY := Id 2.
Definition vZ := Id 3.
Definition tX := TVar vX.
Definition tY := TVar vY.
Definition teXX := TExist vX tX.
Fixpoint FV (t : ty) : id_set :=
  match t with
  | TCName _ => IdSet.empty
  | TPair t1 t2 => IdSet.union (FV t1) (FV t2)
  | TUnion t1 t2 => IdSet.union (FV t1) (FV t2)
  | TExist y t' => IdSet.remove y (FV t')
  | TVar y => IdSet.singleton y
  | TEV _ => IdSet.empty
  end.
Definition fresh (X : id) (fvs : id_set) := ~ IdSet.In X fvs.
Axiom (gen_fresh__fresh : forall fvs : id_set, fresh (gen_fresh fvs) fvs).
Definition get_fresh_in_ty (t : ty) := gen_fresh (FV t).
Reserved Notation "'[' x ':=' s ']' t" (at level 30).
Fixpoint subst (x : id) (s t : ty) :=
  match t with
  | TCName _ => t
  | TPair t1 t2 => TPair ([x := s] t1) ([x := s] t2)
  | TUnion t1 t2 => TUnion ([x := s] t1) ([x := s] t2)
  | TExist y t' =>
      let s' := if IdSet.mem y (FV s) then [y := TVar (gen_fresh (FV s))] s else s in TExist y (if beq_id x y then t' else [x := s'] t')
  | TVar y => if beq_id x y then s else t
  | TEV y => t
  end
where "'[' x ':=' s ']' t" := (subst x s t) : btjt_scope.
(* Failed. *)
