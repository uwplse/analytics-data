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
Theorem match_ty__value_type_l : forall (k : nat) (t v : ty), |-[ k] v <$ t -> value_type v.
Proof.
(intros k; induction t; induction v; intros Hm; try (solve [ constructor | destruct k; contradiction ])).
(destruct k).
(* Auto-generated comment: Failed. *)

