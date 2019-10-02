Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
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
(split; intros Hcontra; [ apply (IdSetFacts.union_2 fvs2) in Hcontra | apply (IdSetFacts.union_3 fvs1) in Hcontra ]; contradiction).
Qed.
Lemma fresh_in_ty_pair__inv : forall (X : id) (t1 t2 : ty), fresh_in_ty X (TPair t1 t2) -> fresh_in_ty X t1 /\ fresh_in_ty X t2.
Proof.
(intros X t1 t2 Hfresh).
(unfold fresh_in_ty in *; simpl in Hfresh; simpl).
(apply fresh_union__inv in Hfresh).
assumption.
Qed.
Lemma fresh_in_ty_union__inv : forall (X : id) (t1 t2 : ty), fresh_in_ty X (TUnion t1 t2) -> fresh_in_ty X t1 /\ fresh_in_ty X t2.
Proof.
(intros X t1 t2 Hfresh).
(unfold fresh_in_ty in *; simpl in Hfresh; simpl).
(apply fresh_union__inv in Hfresh).
assumption.
Qed.
Lemma fresh_in_ty_exist_neq__inv : forall (X X' : id) (t : ty), X <> X' -> fresh_in_ty X (TExist X' t) -> fresh_in_ty X t.
Proof.
(intros X X' t Hneq Hfresh).
(unfold fresh_in_ty in *; simpl in Hfresh; simpl).
(unfold fresh in *).
(intros Hcontra).
(assert (Hneq' : X' <> X) by auto).
(apply (IdSetFacts.remove_2 Hneq') in Hcontra).
contradiction.
Qed.
Lemma free_in_ty_union__inv : forall (X : id) (t1 t2 : ty), free_in_ty X (TUnion t1 t2) -> free_in_ty X t1 \/ free_in_ty X t2.
(intros X t1 t2 HX).
(unfold fresh_in_ty, fresh in *).
(unfold fresh_in_ty in *).
(unfold freee_in_ty in *).
(* Failed. *)
