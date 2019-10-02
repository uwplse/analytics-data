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
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Lemma fresh_union__inv : forall (X : id) (fvs1 fvs2 : id_set), fresh X (IdSet.union fvs1 fvs2) -> fresh X fvs1 /\ fresh X fvs2.
Proof.
(intros X fvs1 fvs2 H).
(unfold fresh in *).
(split; intros Hcontra; [ apply (IdSetFacts.union_2 fvs2) in Hcontra | apply (IdSetFacts.union_3 fvs1) in Hcontra ]).
Qed.
(induction t; intros Hfresh s; try (solve [ reflexivity ]); unfold fresh_in_ty in *; simpl in Hfresh).
(induction t; intros Hfresh s; try (solve [ reflexivity ]); unfold fresh_in_ty in *; simpl in Hfresh; simpl).
-
(apply fresh_union__inv in Hfresh).
(destruct Hfresh as [Hfresh1 Hfresh2]).
(simpl).
(rewrite IHt1; try assumption).
(rewrite IHt2; try assumption).
reflexivity.
(* Failed. *)
