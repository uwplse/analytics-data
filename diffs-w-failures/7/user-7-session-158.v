Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Lemma subst_pair : forall (X : id) (s t1 t2 : ty), [X := s] TPair t1 t2 = TPair ([X := s] t1) ([X := s] t2).
Proof.
(intros; reflexivity).
Qed.
Lemma subst_union : forall (X : id) (s t1 t2 : ty), [X := s] TUnion t1 t2 = TUnion ([X := s] t1) ([X := s] t2).
Proof.
(intros; reflexivity).
Qed.
Unset Silent.
Lemma subst_var_eq : forall (X : id) (s : ty), [X := s] TVar X = s.
Set Silent.
Proof.
(intros; reflexivity).
Set Printing Width 148.
Set Silent.
(intros).
Unset Silent.
(simpl).
(rewrite beq_id_refl).
