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
Lemma subs_neq__permute : forall X Y : id, X <> Y -> forall t s1 s2 : ty, [X := s1] ([Y := s2] t) = [Y := s2] ([X := s1] t).
Proof.
(intros X Y Hneq t).
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
(induction t; intros s1 s2; try (solve [ simpl; reflexivity | specialize (IHt1 s1 s2); specialize (IHt2 s1 s2); auto ])).
