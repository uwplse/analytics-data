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
Set Printing Width 148.
Set Silent.
Lemma not_fresh_in_union__inv : forall (X : id) (fvs1 fvs2 : id_set), not_fresh X (IdSet.union fvs1 fvs2) -> not_fresh X fvs1 /\ not_fresh X fvs2.
Proof.
(intros X fvs1 fvs2 H).
Unset Silent.
(unfold not_fresh in *).
Show.
Set Silent.
Abort.
Lemma subs_not_in_FV : forall (X : id) (t : ty), not_fresh_in_ty X t -> forall s : ty, [X := s] t = t.
Proof.
(intros X t).
(induction t; intros Hnfresh s; try (solve [ reflexivity ])).
-
(simpl).
Unset Silent.
(unfold not_fresh_in_ty in *).
