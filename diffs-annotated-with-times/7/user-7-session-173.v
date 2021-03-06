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
Definition fresh_in_ty (X : id) (t : ty) := fresh X (FV t).
Definition free_in_ty (X : id) (t : ty) := IdSet.In X (FV t).
Hint Unfold fresh fresh_in_ty free_in_ty: DBBetaJulia.
Axiom (gen_fresh : id_set -> id).
Axiom (gen_fresh__fresh : forall fvs : id_set, fresh (gen_fresh fvs) fvs).
Definition get_fresh_in_ty (t : ty) := gen_fresh (FV t).
Reserved Notation "'[' x '@' y ']' t" (at level 30).
Fixpoint rename (x y : id) (t : ty) :=
  match t with
  | TCName _ => t
  | TPair t1 t2 => TPair ([x @ y] t1) ([x @ y] t2)
  | TUnion t1 t2 => TUnion ([x @ y] t1) ([x @ y] t2)
  | TExist z t' => TExist z (if beq_id x z then t' else [x @ y] t')
  | TVar z => if beq_id x z then TVar y else t
  | TEV z => t
  end
where "'[' x '@' y ']' t" := (rename x y t) : btjt_scope.
Fixpoint size (t : ty) :=
  match t with
  | TCName _ => 1
  | TPair t1 t2 => 1 + size t1 + size t2
  | TUnion t1 t2 => 1 + size t1 + size t2
  | TExist z t' => 1 + size t'
  | TVar z => 1
  | TEV z => 1
  end.
Lemma rename__size : forall (x y : id) (t : ty), size ([x @ y] t) = size t.
Proof.
(intros x y).
(induction t; simpl; try (solve [ reflexivity | rewrite IHt1; rewrite IHt2; reflexivity ])).
-
(apply f_equal).
(destruct (beq_idP x i)).
+
subst.
reflexivity.
+
assumption.
-
(destruct (beq_idP x i); reflexivity).
Qed.
Check lt.
Definition lt_size (t1 t2 : ty) := lt (size t1) (size t2).
Function
 subst (x : id) (s t : ty) {wf lt_size t} : ty :=
   match t with
   | TCName _ => t
   | TPair t1 t2 => TPair (subst x s t1) (subst x s t2)
   | TUnion t1 t2 => TUnion (subst x s t1) (subst x s t2)
   | TExist y t' =>
       if IdSet.mem y (FV s)
       then let z := gen_fresh (IdSet.union (FV s) (FV t')) in let tz := [y @ z] t' in TExist z (if beq_id x z then tz else subst x s t')
       else TExist y (if beq_id x y then t' else subst x s t')
   | TVar y => if beq_id x y then s else t
   | TEV y => t
   end.
Print All.
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-29 15:09:13.570000.*)

