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
Inductive value_type : ty -> Prop :=
  | VT_CName : forall cn, value_type (TCName cn)
  | VT_Pair : forall v1 v2, value_type v1 -> value_type v2 -> value_type (TPair v1 v2)
  | VT_Ref : forall t, value_type (TRef t)
  | VT_EV : forall X : id, value_type (TEV X).
Hint Constructors value_type: DBBetaJulia.
Declare Scope btjm_scope.
Delimit Scope btjm_scope with btjm.
Open Scope btjm.
Reserved Notation "'|-[' w ',' k ']' v '<$' t" (at level 40).
Fixpoint match_ty (w : nat) :=
  fix mtyk (k : nat) :=
    fix mty (v : ty) :=
      fix mty' (t : ty) :=
        match w, k, v, t with
        | _, _, TCName c, TCName c' => c = c'
        | _, _, TPair v1 v2, TPair t1 t2 => mty v1 t1 /\ mty v2 t2
        | _, _, _, TUnion t1 t2 => mty' t1 \/ mty' t2
        | _, 0, TRef t', TRef t => True
        | _, S k, TRef t', TRef t => forall v, |-[ w, k] v <$ t' <-> |-[ w, k] v <$ t
        | 0, _, v, TExist _ t' => mty' t'
        | S w, _, v, TExist X t' => exists tx, |-[ w, k] v <$ [X := tx] t'
        | _, _, TEV X, TVar X' => X = X'
        | _, _, _, _ => False
        end
where "'|-[' w ',' k ']' v '<$' t" := (match_ty w k v t) : btjm_scope.
(* Failed. *)
