Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Set Printing Width 148.
Set Silent.
Declare Scope btjt_scope.
Set Printing Width 148.
Set Silent.
Delimit Scope btjt_scope with btjt.
Unset Silent.
Open Scope btjt.
Set Silent.
Reserved Notation "'|' t '|'" (at level 20).
Unset Silent.
Fixpoint inv_depth (t : ty) :=
  match t with
  | TCName _ => 0
  | TPair t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TUnion t1 t2 => Nat.max (| t1 |) (| t2 |)
  | TRef t' => 1 + | t' |
  end
where "'|' t '|'" := (inv_depth t) : btjt_scope.
Set Silent.
Inductive value_type : ty -> Prop :=
  | VT_CName : forall cn, value_type (TCName cn)
  | VT_Pair : forall v1 v2, value_type v1 -> value_type v2 -> value_type (TPair v1 v2)
  | VT_Ref : forall t, value_type (TRef t).
Hint Constructors value_type: DBBetaJulia.
Declare Scope btjm_scope.
Delimit Scope btjm_scope with btjm.
Unset Silent.
Open Scope btjm.
Set Printing Width 148.
Function odd (n : nat) := match n with
                          | 0 => false
                          | S n => true
                          end even (n : nat) := false.
Set Printing Width 148.
Set Silent.
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
Unset Silent.
Notation "'||-[' k ']' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq_k k t1 t2) (at level 47) : btjm_scope.
Set Silent.
Unset Silent.
