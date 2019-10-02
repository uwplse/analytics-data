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
Delimit Scope btjt_scope with btjt.
Open Scope btjt.
Reserved Notation "'|' t '|'" (at level 20).
Fixpoint inv_depth (t : ty) :=
  match t with
  | TCName _ => 0
  | TPair t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TUnion t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TRef t' => 1 + | t' |
  end
where "'|' t '|'" := (inv_depth t) : btjt_scope.
Inductive value_type : ty -> Prop :=
  | VT_CName : forall cn, value_type (TCName cn)
  | VT_Pair : forall v1 v2, value_type v1 -> value_type v2 -> value_type (TPair v1 v2)
  | VT_Ref : forall t, value_type (TRef t).
Hint Constructors value_type: DBBetaJulia.
Declare Scope btjm_scope.
Delimit Scope btjm_scope with btjm.
Open Scope btjm.
Reserved Notation "'|-[' k ']' v '<$' t" (at level 40).
Fixpoint match_ty (k : nat) :=
  fix mty (v : ty) :=
    fix mty' (t : ty) :=
      match k, v, t with
      | _, TCName c, TCName c' => c = c'
      | _, TPair v1 v2, TPair t1 t2 => mty v1 t1 /\ mty v2 t2
      | _, _, TUnion t1 t2 => mty' t1 \/ mty' t2
      | S k, TRef t', TRef t => (inv_depth t <= k /\ inv_depth t' = inv_depth t) /\ (forall v, |-[ k] v <$ t' <-> |-[ k] v <$ t)
      | _, _, _ => False
      end
where "|-[ k ']' v '<$' t" := (match_ty k v t) : btjm_scope.
Definition sem_sub_k (k : nat) (t1 t2 : ty) := forall v : ty, |-[ k] v <$ t1 -> |-[ k] v <$ t2.
Notation "'||-[' k ']' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub_k k t1 t2) (at level 45) : btjm_scope.
Definition sem_eq_k (k : nat) (t1 t2 : ty) := forall v : ty, |-[ k] v <$ t1 <-> |-[ k] v <$ t2.
Notation "'||-[' k ']' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq_k k t1 t2) (at level 45) : btjm_scope.
Definition sem_sub (t1 t2 : ty) := forall k : nat, ||-[ k][t1]<= [t2].
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.
Definition sem_eq (t1 t2 : ty) := forall k : nat, ||-[ k][t1]= [t2].
Notation "'||-' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq t1 t2) (at level 50) : btjm_scope.
Hint Unfold sem_sub_k sem_eq_k sem_sub sem_eq: DBBetaJulia.
Inductive atom_type : ty -> Prop :=
  | AT_CName : forall c : cname, atom_type (TCName c)
  | AT_Pair : forall ta1 ta2 : ty, atom_type ta1 -> atom_type ta2 -> atom_type (TPair ta1 ta2)
  | AT_Ref : forall t : ty, in_nf t -> atom_type (TRef t)
with in_nf : ty -> Prop :=
  | NF_Atom : forall ta : ty, atom_type ta -> in_nf ta
  | NF_Union : forall t1 t2 : ty, in_nf t1 -> in_nf t2 -> in_nf (TUnion t1 t2).
Scheme atom_type_mut := Induction for atom_type Sort Prop
  with in_nf_mut := Induction for in_nf Sort Prop.
Declare Scope btjnf_scope.
Delimit Scope btjnf_scope with btjnf.
Open Scope btjnf.
Notation "'InNF(' t ')'" := (in_nf t) (at level 30) : btjnf_scope.
Hint Constructors atom_type in_nf: DBBetaJulia.
Example innf_1 : InNF( tint).
Proof.
(repeat constructor).
Qed.
Example innf_2 : InNF( TPair tint tstr).
Proof.
(repeat constructor).
Qed.
Example innf_3 : InNF( TUnion (TPair tint tstr) tint).
Proof.
(apply NF_Union; repeat constructor).
Qed.
Example innf_4 : InNF( TPair tint (TUnion tint tstr)) -> False.
Proof.
(intros Hcontra; inversion Hcontra).
(inversion H).
(inversion H4).
Qed.
Example innf_5 : InNF( TRef (TUnion tint tstr)).
Proof.
(apply NF_Atom).
(apply AT_Ref).
(solve [ repeat constructor ]).
Qed.
Example innf_6 : InNF( TRef (TPair tint (TUnion tint tstr))) -> False.
Proof.
(intros Hcontra).
(inversion Hcontra; subst).
(inversion H; subst).
(apply innf_4; assumption).
Qed.
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
(* Auto-generated comment: Failed. *)

