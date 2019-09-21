Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Lemma not_fresh_in_union__inv : forall (X : id) (fvs1 fvs2 : id_set), not_fresh X (IdSet.union fvs1 fvs2) -> not_fresh X fvs1 /\ not_fresh X fvs2.
Unset Silent.
Proof.
Set Silent.
(intros X fvs1 fvs2 H).
Unset Silent.
(unfold not_fresh in *).
Search -IdSet.union.
(simpl in H).
