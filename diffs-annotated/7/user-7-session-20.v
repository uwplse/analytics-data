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
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Open Scope btjnf_scope.
Lemma in_nf_pair__inv : forall t1 t2 : ty, InNF( TPair t1 t2) -> InNF( t1) /\ InNF( t2).
Proof.
(intros t1 t2 Hnf).
(inversion Hnf; subst).
(inversion H; subst).
(split; constructor; assumption).
Qed.
Lemma in_nf_union__inv : forall t1 t2 : ty, InNF( TUnion t1 t2) -> InNF( t1) /\ InNF( t2).
Proof.
(intros t1 t2 Hnf).
(inversion Hnf; subst).
(* Failed. *)
