Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0260a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Unset Silent.
Open Scope btjm.
Set Silent.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Theorem match_ty__value_type_l : forall (v t : ty) (k : nat), |-[ k] v <$ t -> value_type v.
Unset Silent.
Proof.
Set Silent.
(intros v t).
generalize dependent v.
Unset Silent.
(induction t; intros k v Hm).
Set Silent.
-
Unset Silent.
