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
Require Import Coq.Program.Wf.
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
#[program]
Fixpoint subst (x : id) (s t : ty) {measure size t :=
  match t with
  | TCName _ => t
  | TPair t1 t2 => TPair (subst x s t1) (subst x s t2)
  | TUnion t1 t2 => TUnion (subst x s t1) (subst x s t2)
  | TExist y t' =>
      if IdSet.mem y (FV s)
      then let z := gen_fresh (IdSet.union (FV s) (FV t')) in let tz := [y @ z] t' in TExist z (if beq_id x z then tz else subst x s tz)
      else TExist y (if beq_id x y then t' else subst x s t')
  | TVar y => if beq_id x y then s else t
  | TEV y => t
  end.
Next Obligation.
(simpl).
Omega.omega.
Qed.
Next Obligation.
(simpl).
Omega.omega.
Qed.
Next Obligation.
(simpl).
Omega.omega.
Qed.
Next Obligation.
(simpl).
Omega.omega.
Qed.
Next Obligation.
(simpl).
(rewrite rename__size).
Omega.omega.
Qed.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 30) : btjt_scope.
Inductive value_type : ty -> Prop :=
  | VT_CName : forall cn, value_type (TCName cn)
  | VT_Pair : forall v1 v2, value_type v1 -> value_type v2 -> value_type (TPair v1 v2)
  | VT_EV : forall X : id, value_type (TEV X).
Hint Constructors value_type: DBBetaJulia.
Declare Scope btjm_scope.
Delimit Scope btjm_scope with btjm.
Open Scope btjm.
Reserved Notation "'|-[' w ']' v '<$' t" (at level 40).
Fixpoint match_ty (w : nat) :=
  fix mtyv (v : ty) :=
    fix mtyt (t : ty) :=
      match w, v, t with
      | _, TCName c, TCName c' => c = c'
      | _, TPair v1 v2, TPair t1 t2 => mtyv v1 t1 /\ mtyv v2 t2
      | _, _, TUnion t1 t2 => mtyt t1 \/ mtyt t2
      | S w, v, TExist X t' => exists tx, |-[ w] v <$ [X := tx] t'
      | _, TEV X, TVar X' => X = X'
      | _, TEV X, TEV X' => X = X'
      | _, _, _ => False
      end
where "'|-[' w ']' v '<$' t" := (match_ty w v t) : btjm_scope.
Definition sem_sub_w (w1 w2 : nat) (t1 t2 : ty) := forall v : ty, |-[ w1] v <$ t1 -> |-[ w2] v <$ t2.
Notation "'||-[' w1 ',' w2 ']' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub_w w1 w2 t1 t2) (at level 45) : btjm_scope.
Definition sem_sub (t1 t2 : ty) := forall w1 : nat, exists w2 : nat, ||-[ w1, w2][t1]<= [t2].
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.
Definition sem_eq (t1 t2 : ty) := ||- [t1]<= [t2] /\ ||- [t2]<= [t1].
Notation "'||-' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq t1 t2) (at level 50) : btjm_scope.
Hint Unfold sem_sub_w sem_sub sem_eq: DBBetaJulia.
Lemma sem_sub__refl : forall t : ty, ||- [t]<= [t].
Proof.
(intros t w1).
exists w1.
(intros v).
tauto.
Qed.
Lemma sem_eq__refl : forall t : ty, ||- [t]= [t].
Proof.
(intros t; split; apply sem_sub__refl).
Qed.
Lemma sem_sub__trans : forall t1 t2 t3 : ty, ||- [t1]<= [t2] -> ||- [t2]<= [t3] -> ||- [t1]<= [t3].
Proof.
(intros t1 t2 t3 Hsem1 Hsem2).
(unfold sem_sub in *).
(intros w1).
specialize (Hsem1 w1).
(destruct Hsem1 as [w2 Hsem1]).
specialize (Hsem2 w2).
(destruct Hsem2 as [w3 Hsem2]).
exists w3.
(intros v).
auto.
Qed.
Lemma sem_eq__trans : forall t1 t2 t3 : ty, ||- [t1]= [t2] -> ||- [t2]= [t3] -> ||- [t1]= [t3].
Proof.
(intros t1 t2 t3 Hsem1 Hsem2).
(unfold sem_eq in *).
(destruct Hsem1 as [Hsem11 Hsem12]).
(destruct Hsem2 as [Hsem21 Hsem22]).
(split; eapply sem_sub__trans; eauto).
Qed.
Declare Scope btjd_scope.
Delimit Scope btjd_scope with btjd.
Open Scope btjd.
Reserved Notation "'|-' t1 '<<' t2" (at level 50).
Inductive sub_d : ty -> ty -> Prop :=
  | SD_Refl : forall t, |- t << t
  | SD_Trans : forall t1 t2 t3, |- t1 << t2 -> |- t2 << t3 -> |- t1 << t3
  | SD_Pair : forall t1 t2 t1' t2', |- t1 << t1' -> |- t2 << t2' -> |- TPair t1 t2 << TPair t1' t2'
  | SD_UnionL : forall t1 t2 t, |- t1 << t -> |- t2 << t -> |- TUnion t1 t2 << t
  | SD_UnionR1 : forall t1 t2, |- t1 << TUnion t1 t2
  | SD_UnionR2 : forall t1 t2, |- t2 << TUnion t1 t2
  | SD_Distr1 : forall t11 t12 t2, |- TPair (TUnion t11 t12) t2 << TUnion (TPair t11 t2) (TPair t12 t2)
  | SD_Distr2 : forall t1 t21 t22, |- TPair t1 (TUnion t21 t22) << TUnion (TPair t1 t21) (TPair t1 t22)
  | SD_ExistL : forall (X : id) (t t' : ty) (X' : id), fresh_in_ty X' t' -> |- [X := TVar X'] t << t' -> |- TExist X t << t'
  | SD_ExistR : forall (X : id) (t t' : ty), (exists tx : ty, |- t << [X := tx] t') -> |- t << TExist X t'
 where "|- t1 '<<' t2" := (sub_d t1 t2) : btjd_scope.
Hint Constructors sub_d: DBBetaJulia.
Lemma union_right_1 : forall t t1 t2 : ty, |- t << t1 -> |- t << TUnion t1 t2.
Proof.
(intros t t1 t2 H).
(eapply SD_Trans).
eassumption.
constructor.
Qed.
Lemma union_right_2 : forall t t1 t2 : ty, |- t << t2 -> |- t << TUnion t1 t2.
Proof.
(intros t t1 t2 H).
(eapply SD_Trans).
eassumption.
constructor.
Qed.
Hint Resolve union_right_1 union_right_2: DBBetaJulia.
Ltac solve_trans := eapply SD_Trans; eassumption.
(* Auto-generated comment: Succeeded. *)

