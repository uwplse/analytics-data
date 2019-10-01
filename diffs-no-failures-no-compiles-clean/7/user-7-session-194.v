Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0282a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt.
Lemma f_free_in_ty__decidable : forall (X : id) (t : ty), Decidable.decidable (f_free_in_ty X t).
Proof.
(intros X t).
(apply IdSetProps.Dec.MSetDecideAuxiliary.dec_In).
Qed.
Lemma b_free_in_ty__decidable : forall (X : id) (t : ty), Decidable.decidable (b_free_in_ty X t).
Proof.
(intros X t).
(apply IdSetProps.Dec.MSetDecideAuxiliary.dec_In).
Qed.
Lemma f_free_in_ty__dec : forall (X : id) (t : ty), f_free_in_ty X t \/ not_f_free_in_ty X t.
Proof.
(intros X t).
(apply IdSetProps.Dec.MSetDecideAuxiliary.dec_In).
Qed.
Lemma b_free_in_ty__dec : forall (X : id) (t : ty), b_free_in_ty X t \/ not_b_free_in_ty X t.
Proof.
(intros X t).
(apply IdSetProps.Dec.MSetDecideAuxiliary.dec_In).
Qed.
Lemma not_free_union__inv : forall (X : id) (fvs1 fvs2 : id_set), not_free X (IdSet.union fvs1 fvs2) -> not_free X fvs1 /\ not_free X fvs2.
Proof.
(intros X fvs1 fvs2 H).
(unfold not_free in *).
(split; intros Hcontra; [ apply (IdSetFacts.union_2 fvs2) in Hcontra | apply (IdSetFacts.union_3 fvs1) in Hcontra ]; contradiction).
Qed.
Lemma not_free_in_ty_pair__inv : forall (X : id) (t1 t2 : ty), not_free_in_ty X (TPair t1 t2) -> not_free_in_ty X t1 /\ not_free_in_ty X t2.
