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
Open Scope btjt.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Lemma fresh_union__inv : forall (X : id) (fvs1 fvs2 : id_set), fresh X (IdSet.union fvs1 fvs2) -> fresh X fvs1 /\ fresh X fvs2.
Proof.
(intros X fvs1 fvs2 H).
(unfold fresh in *).
Set Printing Width 148.
Set Printing Width 148.
(split; intros Hcontra; [ apply (IdSetFacts.union_2 fvs2) in Hcontra | apply (IdSetFacts.union_3 fvs1) in Hcontra ]; contradiction).
Qed.
Set Silent.
Set Printing Width 148.
Set Printing Width 148.
(induction t; intros Hfresh s; try (solve [ reflexivity ]); unfold fresh_in_ty in *; simpl in Hfresh; simpl).
Show.
Set Silent.
-
(apply fresh_union__inv in Hfresh).
Set Printing Width 148.
Set Silent.
(rewrite IHt1; try assumption).
(rewrite IHt2; try assumption).
Unset Silent.
reflexivity.
Set Silent.
-
(apply fresh_union__inv in Hfresh).
(destruct Hfresh as [Hfresh1 Hfresh2]).
(rewrite IHt1; try assumption).
(rewrite IHt2; try assumption).
Unset Silent.
reflexivity.
-
(rewrite IHt; try assumption).
reflexivity.
-
Set Printing Width 148.
(destruct (beq_idP X i); try reflexivity).
Set Silent.
(rewrite IHt).
reflexivity.
(unfold fresh in *).
(intros Hcontra).
(apply Hfresh).
(apply IdSetFacts.remove_2; try assumption).
(intros Heq).
subst.
contradiction.
-
Set Printing Width 148.
(destruct (beq_idP X i); try reflexivity).
Show.
Show.
Show.
Set Printing Width 148.
subst.
Show.
exfalso.
(apply Hfresh).
Show.
Search -IdSet.singleton.
(apply IdSetFacts.singleton_2).
Show.
reflexivity.
Qed.
