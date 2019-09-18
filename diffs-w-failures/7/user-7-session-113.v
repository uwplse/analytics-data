Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Set Printing Width 148.
Open Scope btjt.
Set Silent.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Unset Silent.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Lemma subs_not_in_FV : forall (X : id) (t : ty), ~ fresh_in_ty X t -> forall s : ty, [X := s] t = t.
Proof.
(intros X t).
Set Printing Width 148.
Set Printing Width 148.
(induction t; intros Hnfresh s; try (solve [ reflexivity ])).
-
(simpl).
Set Printing Width 148.
(unfold fresh_in_ty in *).
(simpl in Hnfresh).
