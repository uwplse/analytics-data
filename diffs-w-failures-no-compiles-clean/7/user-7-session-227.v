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
Lemma free_union__inv : forall (X : id) (fvs1 fvs2 : id_set), free X (IdSet.union fvs1 fvs2) -> free X fvs1 \/ free X fvs2.
Proof.
(intros X fvs1 fvs2).
(unfold free).
(apply IdSetFacts.union_1).
Qed.
Ltac solve_free_union_inv fvname := intros X t1 t2; unfold fvname; simpl; apply free_union__inv.
Ltac
 solve_free_union fvname :=
  unfold fvname, free; simpl; intros X t1 t2 H; destruct H as [H| H]; [ apply IdSetFacts.union_2 | apply IdSetFacts.union_3 ]; assumption.
Lemma union_empty__inv : forall s1 s2, IdSet.Empty (IdSet.union s1 s2) -> IdSet.Empty s1 /\ IdSet.Empty s2.
Proof.
(intros s1 s2 H).
(pose proof (IdSetProps.empty_union_1 s1 H) as H1).
(pose proof (IdSetProps.empty_union_1 s2 H) as H2).
Admitted.
Lemma union_empty : forall s1 s2, IdSet.Empty s1 /\ IdSet.Empty s2 -> IdSet.Empty (IdSet.union s1 s2).
Proof.
Admitted.
Lemma not_f_free_in_ty_pair__inv : forall (X : id) (t1 t2 : ty), not_f_free_in_ty X (TPair t1 t2) -> not_f_free_in_ty X t1 /\ not_f_free_in_ty X t2.
Proof.
(solve_not_free_union not_f_free_in_ty).
Qed.
Lemma not_f_free_in_ty_union__inv :
  forall (X : id) (t1 t2 : ty), not_f_free_in_ty X (TUnion t1 t2) -> not_f_free_in_ty X t1 /\ not_f_free_in_ty X t2.
Proof.
(solve_not_free_union not_f_free_in_ty).
Qed.
Lemma not_f_free_in_ty_exist__inv : forall (X Y : id) (t : ty), not_f_free_in_ty X (TExist Y t) -> not_f_free_in_ty X t.
Proof.
(unfold not_f_free_in_ty, not_free).
(intros X Y t HX Hcontra).
(simpl in HX).
contradiction.
Qed.
Lemma not_f_free_in_ty_fvar__inv : forall X Y : id, not_f_free_in_ty X (TFVar Y) -> X <> Y.
Proof.
(unfold not_f_free_in_ty, not_free).
(simpl).
Search -IdSet.singleton.
(intros X Y Hin).
(destruct (beq_idP X Y) as [HXY| HXY]).
-
subst.
exfalso.
(apply Hin).
(apply IdSet.Facts.singleton_1).
