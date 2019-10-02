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
Lemma not_f_free_in_ty_exist__inv : forall (X Y : id) (t : ty), not_f_free_in_ty X (TExist Y t) -> not_f_free_in_ty X t.
Proof.
(unfold not_f_free_in_ty, not_free).
(intros X Y t HX Hcontra).
(simpl in HX).
contradiction.
Qed.
Lemma f_free_in_ty_exist__inv : forall (X Y : id) (t : ty), f_free_in_ty X (TExist Y t) -> f_free_in_ty X t.
Proof.
(unfold f_free_in_ty, free).
(intros X Y t HX).
(simpl in HX).
assumption.
Qed.
Lemma f_free_in_ty_pair__inv : forall (X : id) (t1 t2 : ty), f_free_in_ty X (TPair t1 t2) -> f_free_in_ty X t1 \/ f_free_in_ty X t2.
Proof.
(solve_free_union_inv f_free_in_ty).
Qed.
Lemma f_free_in_ty_union__inv : forall (X : id) (t1 t2 : ty), f_free_in_ty X (TUnion t1 t2) -> f_free_in_ty X t1 \/ f_free_in_ty X t2.
Proof.
(solve_free_union_inv f_free_in_ty).
Qed.
Lemma f_free_in_ty_pair : forall (X : id) (t1 t2 : ty), f_free_in_ty X t1 \/ f_free_in_ty X t2 -> f_free_in_ty X (TPair t1 t2).
Proof.
(solve_free_union f_free_in_ty).
Qed.
Lemma f_free_in_ty_union : forall (X : id) (t1 t2 : ty), f_free_in_ty X t1 \/ f_free_in_ty X t2 -> f_free_in_ty X (TUnion t1 t2).
Proof.
(solve_free_union f_free_in_ty).
Qed.
Lemma f_free_in_ty_exist : forall (X Y : id) (t : ty), f_free_in_ty X t -> f_free_in_ty X (TExist Y t).
Proof.
(unfold f_free_in_ty, free).
(intros X Y t HX).
(simpl).
assumption.
Qed.
Lemma b_subst_cname : forall (X : id) (s : ty) (c : cname), [BX := s] TCName c = TCName c.
Proof.
(intros).
reflexivity.
Qed.
Lemma b_subst_pair : forall (X : id) (s t1 t2 : ty), [BX := s] TPair t1 t2 = TPair ([BX := s] t1) ([BX := s] t2).
Proof.
(intros).
reflexivity.
Qed.
Lemma b_subst_union : forall (X : id) (s t1 t2 : ty), [BX := s] TUnion t1 t2 = TUnion ([BX := s] t1) ([BX := s] t2).
Proof.
(intros).
(simpl).
reflexivity.
Qed.
Lemma b_subst_ev : forall (X : id) (s : ty) (Y : id), [BX := s] TEV Y = TEV Y.
Proof.
(intros).
reflexivity.
Qed.
Lemma b_subst_bvar_eq : forall (X : id) (s : ty), [BX := s] TBVar X = s.
Proof.
(intros).
(simpl).
(rewrite <- beq_id_refl).
reflexivity.
Qed.
Lemma b_subst_bvar_neq : forall (X : id) (s : ty) (Y : id), X <> Y -> [BX := s] TBVar Y = TBVar Y.
Proof.
(intros X s Y Hneq).
(simpl).
(destruct (beq_id_false_iff X Y) as [_ Hid]).
specialize (Hid Hneq).
(simpl).
(rewrite Hid).
reflexivity.
Qed.
Lemma b_subst_exist_eq : forall (X : id) (s : ty) (t : ty), [BX := s] TExist X t = TExist X t.
Proof.
(intros).
(simpl).
(rewrite <- beq_id_refl).
reflexivity.
Qed.
Lemma b_subst_exist_neq : forall (X : id) (s : ty) (Y : id) (t : ty), X <> Y -> [BX := s] TExist Y t = TExist Y ([BX := s] t).
Proof.
(intros X s Y t Hneq).
(simpl).
(destruct (beq_id_false_iff X Y) as [_ Hid]).
specialize (Hid Hneq).
(rewrite Hid).
reflexivity.
Qed.
Lemma b_subst_not_b_free_in_ty : forall (X : id) (t : ty), not_b_free_in_ty X t -> forall s : ty, [BX := s] t = t.
Proof.
(intros X t).
(induction t; intros HX s;
  try (solve
   [ reflexivity
   | try destruct (not_b_free_in_ty_pair__inv _ _ _ HX) as [HX1 HX2]; try destruct (not_b_free_in_ty_union__inv _ _ _ HX) as [HX1 HX2]; simpl;
      rewrite IHt1; try assumption; rewrite IHt2; try assumption; reflexivity ])).
-
(destruct (beq_idP X i); try (subst; rewrite b_subst_exist_eq; reflexivity)).
(rewrite b_subst_exist_neq; try assumption).
(rewrite IHt).
reflexivity.
(unfold not_b_free_in_ty, not_free in *).
(simpl in HX).
(intros Hcontra).
(apply HX).
(apply IdSetFacts.remove_iff).
auto.
-
(destruct (beq_idP X i)).
+
subst.
(unfold not_b_free_in_ty in HX).
(simpl in HX).
(unfold not_free in HX).
exfalso.
(apply HX).
(apply IdSetFacts.singleton_2).
reflexivity.
+
subst.
(rewrite b_subst_bvar_neq; try assumption).
reflexivity.
Qed.
Lemma b_subst_neq__permute :
  forall X Y : id, X <> Y -> forall s1 s2 t : ty, wf_ty s1 -> wf_ty s2 -> [BX := s1] ([BY := s2] t) = [BY := s2] ([BX := s1] t).
Proof.
(intros X Y Hneq s1 s2 t Hs1 Hs2).
generalize dependent t.
(induction t; try (solve [ simpl; reflexivity | simpl; rewrite IHt1; try assumption; rewrite IHt2; try assumption; reflexivity ])).
-
(simpl).
(destruct (beq_idP Y i)).
+
subst.
(destruct (beq_idP X i)).
*
subst.
(repeat rewrite b_subst_exist_eq).
reflexivity.
*
(rewrite b_subst_exist_neq; try assumption).
(rewrite b_subst_exist_eq).
reflexivity.
+
(destruct (beq_idP X i)).
*
subst.
(rewrite b_subst_exist_eq).
(rewrite b_subst_exist_neq; try assumption).
reflexivity.
*
(repeat rewrite b_subst_exist_neq; try assumption).
(rewrite IHt).
reflexivity.
-
(simpl; destruct (beq_idP X i); destruct (beq_idP Y i); subst).
+
contradiction.
+
(simpl).
(rewrite <- beq_id_refl).
(rewrite b_subst_not_b_free_in_ty).
reflexivity.
(apply wf_ty__not_b_free_in_ty; assumption).
+
(simpl).
(rewrite <- beq_id_refl).
(rewrite b_subst_not_b_free_in_ty).
reflexivity.
(apply wf_ty__not_b_free_in_ty; assumption).
+
(rewrite b_subst_bvar_neq; try assumption).
(rewrite b_subst_bvar_neq; try assumption).
reflexivity.
Qed.
Lemma f_free_in_ty__f_free_in_b_subst : forall (Y : id) (s : ty) (X : id) (t : ty), f_free_in_ty X t -> f_free_in_ty X ([BY := s] t).
Proof.
(intros Y s X t HX).
(induction t; try (solve [ simpl; assumption ])).
-
(rewrite b_subst_pair).
(apply f_free_in_ty_pair).
(apply f_free_in_ty_pair__inv in HX).
tauto.
-
(rewrite b_subst_union).
(apply f_free_in_ty_union).
(apply f_free_in_ty_union__inv in HX).
tauto.
-
(destruct (beq_idP Y i)).
+
subst.
(rewrite b_subst_exist_eq).
assumption.
+
(rewrite b_subst_exist_neq; try assumption).
(apply f_free_in_ty_exist).
tauto.
-
(unfold f_free_in_ty, free in HX).
(simpl in HX).
(rewrite IdSetFacts.empty_iff in HX).
contradiction.
Qed.
Lemma f_subst_cname : forall (X : id) (s : ty) (c : cname), [FX := s] TCName c = TCName c.
Proof.
(intros).
reflexivity.
Qed.
Lemma f_subst_pair : forall (X : id) (s t1 t2 : ty), [FX := s] TPair t1 t2 = TPair ([FX := s] t1) ([FX := s] t2).
Proof.
(intros).
reflexivity.
Qed.
Lemma f_subst_union : forall (X : id) (s t1 t2 : ty), [FX := s] TUnion t1 t2 = TUnion ([FX := s] t1) ([FX := s] t2).
Proof.
(intros).
(simpl).
reflexivity.
Qed.
Lemma f_subst_ev : forall (X : id) (s : ty) (Y : id), [FX := s] TEV Y = TEV Y.
Proof.
(intros).
reflexivity.
Qed.
Lemma f_subst_exist : forall (X : id) (s : ty) (Y : id) (t : ty), [FX := s] TExist Y t = TExist Y ([FX := s] t).
Proof.
(intros).
reflexivity.
Qed.
Lemma f_subst_fvar_neq : forall (X : id) (s : ty) (Y : id), X <> Y -> [FX := s] TFVar Y = TFVar Y.
Proof.
(intros X s Y Hneq).
(simpl).
(destruct (beq_id_false_iff X Y) as [_ Hid]).
specialize (Hid Hneq).
(simpl).
(rewrite Hid).
reflexivity.
Qed.
Lemma f_subst_not_b_free_in_ty : forall (X : id) (t : ty), not_f_free_in_ty X t -> forall s : ty, [FX := s] t = t.
Proof.
(intros X t).
(induction t; intros HX s;
  try (solve
   [ reflexivity
   | try destruct (not_f_free_in_ty_pair__inv _ _ _ HX) as [HX1 HX2]; try destruct (not_f_free_in_ty_union__inv _ _ _ HX) as [HX1 HX2]; simpl;
      rewrite IHt1; try assumption; rewrite IHt2; try assumption; reflexivity ])).
-
(rewrite f_subst_exist).
(apply not_f_free_in_ty_exist__inv in HX).
(rewrite IHt).
reflexivity.
assumption.
-
(destruct (beq_idP X i)).
+
subst.
(unfold not_f_free_in_ty, not_free in HX).
(simpl in HX).
exfalso.
(apply HX).
(apply IdSetFacts.singleton_2).
reflexivity.
+
subst.
(rewrite f_subst_fvar_neq; try assumption).
reflexivity.
Qed.
Lemma union_empty__inv : forall s1 s2, IdSet.Empty (IdSet.union s1 s2) -> IdSet.Empty s1 /\ IdSet.Empty s2.
Proof.
(intros s1 s2 H).
Check IdSetProps.empty_union_1.
Check IdSetProps.empty_union_1.
(pose proof (IdSetProps.empty_union_1 s1 H) as H1).
(pose proof (IdSetProps.empty_union_1 s2 H) as H2).
(unfold wf_ty; simpl).
(apply union_empty__inv).
(* Failed. *)
