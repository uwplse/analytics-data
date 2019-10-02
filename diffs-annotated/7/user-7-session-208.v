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
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
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
Ltac
 solve_not_free_union fvname := intros X t1 t2 Hfresh; unfold fvname in *; simpl in Hfresh; simpl; apply not_free_union__inv in Hfresh; assumption.
Lemma wf_ty__not_b_free_in_ty : forall (t : ty) (X : id), wf_ty t -> not_b_free_in_ty X t.
Proof.
(unfold wf_ty, not_b_free_in_ty, not_free).
(intros t X Ht Hcontra).
(apply IdSetProps.empty_is_empty_1 in Ht).
(pose proof IdSetFacts.In_m as Hfact).
(destruct (IdSetFacts.empty_iff X) as [H _]).
(assert (Heq : X = X) by reflexivity).
(apply H).
specialize (Hfact X X Heq (FBV t) IdSet.empty Ht).
tauto.
Qed.
Lemma not_f_free_in_ty_pair__inv : forall (X : id) (t1 t2 : ty), not_f_free_in_ty X (TPair t1 t2) -> not_f_free_in_ty X t1 /\ not_f_free_in_ty X t2.
Proof.
(solve_not_free_union not_f_free_in_ty).
Qed.
Lemma not_b_free_in_ty_pair__inv : forall (X : id) (t1 t2 : ty), not_b_free_in_ty X (TPair t1 t2) -> not_b_free_in_ty X t1 /\ not_b_free_in_ty X t2.
Proof.
(solve_not_free_union not_b_free_in_ty).
Qed.
Lemma not_f_free_in_ty_union__inv :
  forall (X : id) (t1 t2 : ty), not_f_free_in_ty X (TUnion t1 t2) -> not_f_free_in_ty X t1 /\ not_f_free_in_ty X t2.
Proof.
(solve_not_free_union not_f_free_in_ty).
Qed.
Lemma not_b_free_in_ty_union__inv :
  forall (X : id) (t1 t2 : ty), not_b_free_in_ty X (TUnion t1 t2) -> not_b_free_in_ty X t1 /\ not_b_free_in_ty X t2.
Proof.
(solve_not_free_union not_b_free_in_ty).
Qed.
Lemma not_f_free_in_ty_exist__inv : forall (X Y : id) (t : ty), not_f_free_in_ty X (TExist Y t) -> not_f_free_in_ty t.
Lemma not_f_free_in_ty_exist__inv : forall (X Y : id) (t : ty), not_f_free_in_ty X (TExist Y t) -> not_f_free_in_ty X t.
(intros X Y t).
(* Failed. *)
