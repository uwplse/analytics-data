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
Lemma wf_ty_pair__inv : forall t1 t2 : ty, wf_ty (TPair t1 t2) -> wf_ty t1 /\ wf_ty t2.
Proof.
(intros t1 t2 Hwf).
(unfold wf_ty in *; simpl in *).
Search -IdSet.Empty.
admit.
Admitted.
Lemma wf_ty_union__inv : forall t1 t2 : ty, wf_ty (TUnion t1 t2) -> wf_ty t1 /\ wf_ty t2.
Proof.
(intros t1 t2 Hwf).
(unfold wf_ty in *; simpl in *).
admit.
Admitted.
(* Failed. *)
