Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Reserved Notation "'|-[' k ']' t1 '<$' t2" (at level 50).
Fixpoint match_ty_i (k : nat) :=
  fix mty (v : ty) :=
    fix mty' (t : ty) :=
      match k, v, t with
      | _, TCName c, TCName c' => c = c'
      | _, TPair v1 v2, TPair t1 t2 => mty v1 t1 /\ mty v2 t2
      | _, _, TUnion t1 t2 => mty' t1 \/ mty' t2
      | 0, TRef t', TRef t => True
      | S k, TRef t', TRef t => forall v, value_type v -> |-[ k] v <$ t <-> |-[ k] v <$ t'
      | _, _, _ => False
      end
where "|-[ k ']' t1 '<$' t2" := (match_ty_i k t1 t2) : btjmi_scope.
(* Auto-generated comment: Failed. *)
