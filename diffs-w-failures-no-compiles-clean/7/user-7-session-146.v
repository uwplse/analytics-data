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
  | TRef : ty -> ty
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
Definition tyXRefX := TExist vX (TRef tX).
Reserved Notation "'[' x ':=' s ']' t" (at level 30).
Fixpoint subst (x : id) (s t : ty) :=
  match t with
  | TCName _ => t
  | TPair t1 t2 => TPair ([x := s] t1) ([x := s] t2)
  | TUnion t1 t2 => TUnion ([x := s] t1) ([x := s] t2)
  | TRef t' => TRef ([x := s] t')
  | TExist y t' => TExist y (if beq_id x y then t' else [x := s] t')
  | TVar y => if beq_id x y then s else t
  | TEV y => t
  end
where "'[' x ':=' s ']' t" := (subst x s t) : btjt_scope.
Fixpoint FV (t : ty) : id_set :=
  match t with
  | TCName _ => IdSet.empty
  | TPair t1 t2 => IdSet.union (FV t1) (FV t2)
  | TUnion t1 t2 => IdSet.union (FV t1) (FV t2)
  | TRef t' => FV t'
  | TExist y t' => IdSet.remove y (FV t')
  | TVar y => IdSet.singleton y
  | TEV _ => IdSet.empty
  end.
Definition fresh (X : id) (fvs : id_set) := ~ IdSet.In X fvs.
Definition fresh_in_ty (X : id) (t : ty) := fresh X (FV t).
Hint Unfold fresh fresh_in_ty: DBBetaJulia.
Inductive value_type : ty -> Prop :=
  | VT_CName : forall cn, value_type (TCName cn)
  | VT_Pair : forall v1 v2, value_type v1 -> value_type v2 -> value_type (TPair v1 v2)
  | VT_Ref : forall t, value_type (TRef t)
  | VT_EV : forall X : id, value_type (TEV X).
Hint Constructors value_type: DBBetaJulia.
Declare Scope btjm_scope.
Delimit Scope btjm_scope with btjm.
Open Scope btjm.
Reserved Notation "'|-[' k ',' w ']' v '<$' t" (at level 40).
Fixpoint match_ty (k : nat) :=
  fix mtyw (w : nat) :=
    fix mtyv (v : ty) :=
      fix mtyt (t : ty) :=
        match k, w, v, t with
        | _, _, TCName c, TCName c' => c = c'
        | _, _, TPair v1 v2, TPair t1 t2 => mtyv v1 t1 /\ mtyv v2 t2
        | _, _, _, TUnion t1 t2 => mtyt t1 \/ mtyt t2
        | 0, _, TRef t', TRef t => True
        | S k, _, TRef t', TRef t =>
            (forall w1, exists w2, forall v, |-[ k, w1] v <$ t' -> |-[ k, w2] v <$ t) /\
            (forall w1, exists w2, forall v, |-[ k, w1] v <$ t -> |-[ k, w2] v <$ t')
        | _, S w, v, TExist X t' => exists tx, mtyw w v ([X := tx] t')
        | _, _, TEV X, TVar X' => X = X'
        | _, _, TEV X, TEV X' => X = X'
        | _, _, _, _ => False
        end
where "'|-[' k ',' w ']' v '<$' t" := (match_ty k w v t) : btjm_scope.
Definition sem_sub_k_w (k w1 w2 : nat) (t1 t2 : ty) := forall v : ty, |-[ k, w1] v <$ t1 -> |-[ k, w2] v <$ t2.
Notation "'||-[' k ',' w1 ',' w2 ']' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub_k_w k w1 w2 t1 t2) (at level 45) : btjm_scope.
Definition sem_sub_k (k : nat) (t1 t2 : ty) := forall w1 : nat, exists w2 : nat, ||-[ k, w1, w2][t1]<= [t2].
Notation "'||-[' k ']' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub_k k t1 t2) (at level 47) : btjm_scope.
Definition sem_eq_k (k : nat) (t1 t2 : ty) := ||-[ k][t1]<= [t2] /\ ||-[ k][t2]<= [t1].
Notation "'||-[' k ']' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq_k k t1 t2) (at level 47) : btjm_scope.
Definition sem_sub (t1 t2 : ty) := forall k : nat, ||-[ k][t1]<= [t2].
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.
Definition sem_eq (t1 t2 : ty) := forall k : nat, ||-[ k][t1]= [t2].
Notation "'||-' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq t1 t2) (at level 50) : btjm_scope.
Hint Unfold sem_sub_k_w sem_sub_k sem_eq_k sem_sub sem_eq: DBBetaJulia.
Lemma sem_sub_k__refl : forall (k : nat) (t : ty), ||-[ k][t]<= [t].
Proof.
(intros k t w1).
exists w1.
(intros v).
tauto.
Qed.
Lemma sem_eq_k__refl : forall (k : nat) (t : ty), ||-[ k][t]= [t].
Proof.
(intros k t; split; intros w1; exists w1; intros v; tauto).
Qed.
Lemma sem_sub_k__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t3] -> ||-[ k][t1]<= [t3].
Proof.
(intros k t1 t2 t3 Hsem1 Hsem2).
(unfold sem_sub_k in *).
(intros w1).
specialize (Hsem1 w1).
(destruct Hsem1 as [w2 Hsem1]).
specialize (Hsem2 w2).
(destruct Hsem2 as [w3 Hsem2]).
exists w3.
(intros v).
auto.
Qed.
Lemma sem_eq_k__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]= [t2] -> ||-[ k][t2]= [t3] -> ||-[ k][t1]= [t3].
Proof.
(intros k t1 t2 t3 Hsem1 Hsem2).
(unfold sem_eq_k in *).
(destruct Hsem1 as [Hsem11 Hsem12]).
(destruct Hsem2 as [Hsem21 Hsem22]).
(split; eapply sem_sub_k__trans; eauto).
Qed.
Lemma sem_sub__refl : forall t : ty, ||- [t]<= [t].
Proof.
(intros t k).
(apply sem_sub_k__refl).
Qed.
Lemma sem_eq__refl : forall t : ty, ||- [t]= [t].
Proof.
(intros t k).
(apply sem_eq_k__refl).
Qed.
Lemma sem_sub__trans : forall t1 t2 t3 : ty, ||- [t1]<= [t2] -> ||- [t2]<= [t3] -> ||- [t1]<= [t3].
Proof.
(intros t1 t2 t3 Hsem1 Hsem2).
(intros k).
(apply sem_sub_k__trans with t2; auto).
Qed.
Lemma sem_eq__trans : forall t1 t2 t3 : ty, ||- [t1]= [t2] -> ||- [t2]= [t3] -> ||- [t1]= [t3].
Proof.
(intros t1 t2 t3 Hsem1 Hsem2).
(intros k).
(apply sem_eq_k__trans with t2; auto).
Qed.
Inductive atom_type : ty -> Prop :=
  | AT_CName : forall c : cname, atom_type (TCName c)
  | AT_Pair : forall ta1 ta2 : ty, atom_type ta1 -> atom_type ta2 -> atom_type (TPair ta1 ta2)
  | AT_Ref : forall t : ty, in_nf t -> atom_type (TRef t)
with in_nf : ty -> Prop :=
  | NF_Atom : forall ta : ty, atom_type ta -> in_nf ta
  | NF_Union : forall t1 t2 : ty, in_nf t1 -> in_nf t2 -> in_nf (TUnion t1 t2)
  | NF_Exist : forall (X : id) (t : ty), in_nf t -> in_nf (TExist X t).
Scheme atom_type_mut := Induction for atom_type Sort Prop
  with in_nf_mut := Induction for in_nf Sort Prop.
Declare Scope btjnf_scope.
Delimit Scope btjnf_scope with btjnf.
Open Scope btjnf.
Notation "'InNF(' t ')'" := (in_nf t) (at level 30) : btjnf_scope.
Hint Constructors atom_type in_nf: DBBetaJulia.
Lemma atom_type__value_type : forall t : ty, atom_type t -> value_type t.
Proof.
(apply (atom_type_mut (fun (t : ty) (Hat : atom_type t) => value_type t) (fun (t : ty) (_ : in_nf t) => True));
  try (solve [ auto with DBBetaJulia ])).
Qed.
Fixpoint unite_pairs (t1 : ty) :=
  fix unprs (t2 : ty) :=
    match t1, t2 with
    | TUnion t11 t12, _ => TUnion (unite_pairs t11 t2) (unite_pairs t12 t2)
    | _, TUnion t21 t22 => TUnion (unprs t21) (unprs t22)
    | _, _ => TPair t1 t2
    end.
