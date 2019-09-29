Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Lemma subs_not_in_FV : forall (X : id) (t : ty), not_fresh_in_ty X t -> forall s : ty, [X := s] t = t.
Proof.
(intros X t).
(induction t; intros Hnfresh s; try (solve [ reflexivity ])).
-
(simpl).
(unfold not_fresh_in_ty in *).
