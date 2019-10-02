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
Proof.
(intros; reflexivity).
Qed.
Lemma subst_union : forall (X : id) (s t1 t2 : ty), [X := s] TUnion t1 t2 = TUnion ([X := s] t1) ([X := s] t2).
Proof.
(intros; reflexivity).
Qed.
Lemma subst_fresh_in_ty : forall (X : id) (t : ty), fresh_in_ty X t -> forall s : ty, [X := s] t = t.
Proof.
(intros X t).
(induction t; intros Hfresh s; try (solve [ reflexivity ]); unfold fresh_in_ty in *; simpl in Hfresh; simpl;
  try (solve
   [ apply fresh_union__inv in Hfresh; destruct Hfresh as [Hfresh1 Hfresh2]; rewrite IHt1; try assumption; rewrite IHt2; try assumption;
      reflexivity ])).
-
(destruct (beq_idP X i); try reflexivity).
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
(unfold fresh in Hfresh).
(destruct (beq_idP X i); try reflexivity).
subst.
exfalso.
(apply Hfresh).
(apply IdSetFacts.singleton_2).
reflexivity.
Qed.
Lemma subs_neq__permute :
  forall X Y : id, X <> Y -> forall t s1 s2 : ty, fresh_in_ty X s2 -> fresh_in_ty Y s1 -> [X := s1] ([Y := s2] t) = [Y := s2] ([X := s1] t).
Proof.
(intros X Y Hneq t).
(induction t; intros s1 s2 HXs2 HYs1;
  try (solve [ simpl; reflexivity | simpl; rewrite IHt1; try assumption; rewrite IHt2; try assumption; reflexivity ])).
-
(simpl).
(destruct (beq_idP X i)).
+
subst.
(destruct (beq_idP Y i); reflexivity).
+
(destruct (beq_idP Y i)).
*
subst.
reflexivity.
*
(rewrite IHt; try assumption).
reflexivity.
-
(simpl; destruct (beq_idP X i); destruct (beq_idP Y i); subst).
+
contradiction.
+
(simpl).
(rewrite <- beq_id_refl).
symmetry.
(apply subs_fresh_in_ty).
