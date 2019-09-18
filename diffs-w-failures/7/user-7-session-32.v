Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Declare Scope btjmi_scope.
Delimit Scope btjmi_scope with btjmi.
Open Scope btjmi.
Reserved Notation "'|-[' k ']' t1 '<$' t2" (at level 40).
Fixpoint match_ty_i (k : nat) :=
  fix mty (v : ty) :=
    fix mty' (t : ty) :=
      match k, v, t with
      | _, TCName c, TCName c' => c = c'
      | _, TPair v1 v2, TPair t1 t2 => mty v1 t1 /\ mty v2 t2
      | _, _, TUnion t1 t2 => mty' t1 \/ mty' t2
      | 0, TRef t', TRef t => True
      | S k, TRef t', TRef t => forall v, |-[ k] v <$ t <-> |-[ k] v <$ t'
      | _, _, _ => False
      end
where "|-[ k ']' t1 '<$' t2" := (match_ty_i k t1 t2) : btjmi_scope.
Definition sem_sub_k_i (k : nat) (t1 t2 : ty) := forall v : ty, |-[ k] v <$ t1 -> |-[ k] v <$ t2.
Notation "'||-[' k ']' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub_k_i k t1 t2) (at level 45) : btjmi_scope.
Definition sem_eq_k_i (k : nat) (t1 t2 : ty) := forall v : ty, |-[ k] v <$ t1 <-> |-[ k] v <$ t2.
Notation "'||-[' k ']' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq_k_i k t1 t2) (at level 45) : btjmi_scope.
Definition sem_sub_i (t1 t2 : ty) := forall k : nat, ||-[ k][t1]<= [t2].
Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub_i t1 t2) (at level 50) : btjmi_scope.
Definition sem_eq_i (t1 t2 : ty) := forall k : nat, ||-[ k][t1]= [t2].
Notation "'||-' '[' t1 ']' '=' '[' t2 ']'" := (sem_eq_i t1 t2) (at level 50) : btjmi_scope.
Unset Silent.
Hint Unfold sem_sub_k_i sem_eq_k_i sem_sub_i sem_eq_i: DBBetaJulia.
