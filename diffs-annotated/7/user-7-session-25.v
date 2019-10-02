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
Declare Scope btjnf_scope.
Delimit Scope btjnf_scope with btjnf.
Open Scope btjnf.
Notation "'InNF(' t ')'" := (in_nf t) (at level 30) : btjnf_scope.
Hint Constructors atom_type in_nf: DBBetaJulia.
Fixpoint unite_pairs (t1 : ty) :=
  fix unprs (t2 : ty) :=
    match t1, t2 with
    | TUnion t11 t12, _ => TUnion (unite_pairs t11 t2) (unite_pairs t12 t2)
    | _, TUnion t21 t22 => TUnion (unprs t21) (unprs t22)
    | _, _ => TPair t1 t2
    end.
Fixpoint mk_nf (t : ty) :=
  match t with
  | TCName n => t
  | TPair t1 t2 => let t1' := mk_nf t1 in let t2' := mk_nf t2 in unite_pairs t1' t2'
  | TUnion t1 t2 => TUnion (mk_nf t1) (mk_nf t2)
  | TRef t' => TRef (mk_nf t')
  end.
Notation "'MkNF(' t ')'" := (mk_nf t) (at level 30) : btjnf_scope.
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
  | SD_Ref : forall t t', |- t << t' -> |- t' << t -> |- TRef t << TRef t'
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
Declare Scope btjr_scope.
Delimit Scope btjr_scope with btjr.
Open Scope btjr.
Reserved Notation "'|-' t1 '<<' t2" (at level 50).
Inductive sub_r : ty -> ty -> Prop :=
  | SR_CNameRefl : forall c : cname, |- TCName c << TCName c
  | SR_Pair : forall t1 t2 t1' t2', |- t1 << t1' -> |- t2 << t2' -> |- TPair t1 t2 << TPair t1' t2'
  | SR_UnionL : forall t1 t2 t', |- t1 << t' -> |- t2 << t' -> |- TUnion t1 t2 << t'
  | SR_UnionR1 : forall t1 t1' t2', |- t1 << t1' -> |- t1 << TUnion t1' t2'
  | SR_UnionR2 : forall t2 t1' t2', |- t2 << t2' -> |- t2 << TUnion t1' t2'
  | SR_Ref : forall t t', |- t << t' -> |- t' << t -> |- TRef t << TRef t'
  | SR_NormalForm : forall t t', |- MkNF( t) << t' -> |- t << t'
 where "|- t1 '<<' t2" := (sub_r t1 t2) : btjr_scope.
Hint Constructors sub_r: DBBetaJulia.
