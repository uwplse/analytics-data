Time From iris.base_logic Require Export bi.
Time From iris.bi Require Export bi.
Time From stdpp Require Import namespaces.
Time Set Default Proof Using "Type".
Time Import bi.
Time
Inductive modality_action (PROP1 : bi) : bi \226\134\146 Type :=
  | MIEnvIsEmpty : forall {PROP2 : bi}, modality_action PROP1 PROP2
  | MIEnvForall : forall C : PROP1 \226\134\146 Prop, modality_action PROP1 PROP1
  | MIEnvTransform :
      forall {PROP2 : bi} (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop),
      modality_action PROP1 PROP2
  | MIEnvClear : forall {PROP2}, modality_action PROP1 PROP2
  | MIEnvId : modality_action PROP1 PROP1.
Time Arguments MIEnvIsEmpty {_} {_}.
Time Arguments MIEnvForall {_} _.
Time Arguments MIEnvTransform {_} {_} _.
Time Arguments MIEnvClear {_} {_}.
Time Arguments MIEnvId {_}.
Time Notation MIEnvFilter C:= (MIEnvTransform (TCDiag C)).
Time
Definition modality_intuitionistic_action_spec {PROP1} 
  {PROP2} (s : modality_action PROP1 PROP2) : (PROP1 \226\134\146 PROP2) \226\134\146 Prop :=
  match s with
  | MIEnvIsEmpty => \206\187 M, True
  | MIEnvForall C =>
      \206\187 M, (\226\136\128 P, C P \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P)) \226\136\167 (\226\136\128 P Q, M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q))
  | MIEnvTransform C =>
      \206\187 M, (\226\136\128 P Q, C P Q \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 Q)) \226\136\167 (\226\136\128 P Q, M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q))
  | MIEnvClear => \206\187 M, True
  | MIEnvId => \206\187 M, \226\136\128 P, \226\150\161 P \226\138\162 M (\226\150\161 P)
  end.
Time
Definition modality_spatial_action_spec {PROP1} {PROP2}
  (s : modality_action PROP1 PROP2) : (PROP1 \226\134\146 PROP2) \226\134\146 Prop :=
  match s with
  | MIEnvIsEmpty => \206\187 M, True
  | MIEnvForall C => \206\187 M, \226\136\128 P, C P \226\134\146 P \226\138\162 M P
  | MIEnvTransform C => \206\187 M, \226\136\128 P Q, C P Q \226\134\146 P \226\138\162 M Q
  | MIEnvClear => \206\187 M, \226\136\128 P, Absorbing (M P)
  | MIEnvId => \206\187 M, \226\136\128 P, P \226\138\162 M P
  end.
Time
Record modality_mixin {PROP1 PROP2 : bi} (M : PROP1 \226\134\146 PROP2)
(iaction saction : modality_action PROP1 PROP2) :={
 modality_mixin_intuitionistic :
  modality_intuitionistic_action_spec iaction M;
 modality_mixin_spatial : modality_spatial_action_spec saction M;
 modality_mixin_emp : emp \226\138\162 M emp;
 modality_mixin_mono : forall P Q, (P \226\138\162 Q) \226\134\146 M P \226\138\162 M Q;
 modality_mixin_sep : forall P Q, M P \226\136\151 M Q \226\138\162 M (P \226\136\151 Q)}.
Time
Record modality (PROP1 PROP2 : bi) :=
 Modality {modality_car :> PROP1 \226\134\146 PROP2;
           modality_intuitionistic_action : modality_action PROP1 PROP2;
           modality_spatial_action : modality_action PROP1 PROP2;
           modality_mixin_of :
            modality_mixin modality_car modality_intuitionistic_action
              modality_spatial_action}.
Time Arguments Modality {_} {_} _ {_} {_} _.
Time Arguments modality_intuitionistic_action {_} {_} _.
Time Arguments modality_spatial_action {_} {_} _.
Time Section modality.
Time Context {PROP1} {PROP2} (M : modality PROP1 PROP2).
Time
Lemma modality_intuitionistic_transform C P Q :
  modality_intuitionistic_action M = MIEnvTransform C \226\134\146 C P Q \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time From iris.bi Require Export bi.
Time Qed.
Time
Lemma modality_and_transform C P Q :
  modality_intuitionistic_action M = MIEnvTransform C \226\134\146 M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Set Default Proof Using "Type".
Time Import bi base_logic.bi.uPred.
Time Module uPred.
Time Section derived.
Time Context {M : ucmraT}.
Time Implicit Type \207\134 : Prop.
Time Implicit Types P Q : uPred M.
Time Implicit Type A : Type.
Time Notation "P \226\138\162 Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Time Notation "P \226\138\163\226\138\162 Q" := (equiv (A:=uPredI M) P%I Q%I).
Time #[global]
Instance uPred_valid_proper : (Proper ((\226\138\163\226\138\162) ==> iff) (@uPred_valid M)).
Time Proof.
Time solve_proper.
Time Qed.
Time
Lemma modality_spatial_transform C P Q :
  modality_spatial_action M = MIEnvTransform C \226\134\146 C P Q \226\134\146 P \226\138\162 M Q.
Time Proof.
Time Qed.
Time #[global]
Instance uPred_valid_mono : (Proper ((\226\138\162) ==> impl) (@uPred_valid M)).
Time Proof.
Time solve_proper.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time #[global]
Instance uPred_valid_flip_mono :
 (Proper (flip (\226\138\162) ==> flip impl) (@uPred_valid M)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance ownM_proper : (Proper ((\226\137\161) ==> (\226\138\163\226\138\162)) (@uPred_ownM M)) :=
 (ne_proper _).
Time #[global]
Instance cmra_valid_proper  {A : cmraT}:
 (Proper ((\226\137\161) ==> (\226\138\163\226\138\162)) (@uPred_cmra_valid M A)) := 
 (ne_proper _).
Time
Lemma persistently_cmra_valid_1 {A : cmraT} (a : A) :
  \226\156\147 a \226\138\162 <pers> (\226\156\147 a : uPred M).
Time Proof.
Time by rewrite {+1}plainly_cmra_valid_1 plainly_elim_persistently.
Time Qed.
Time
Lemma modality_spatial_clear P :
  modality_spatial_action M = MIEnvClear \226\134\146 Absorbing (M P).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time Lemma modality_emp : emp \226\138\162 M emp.
Time Proof.
Time (eapply modality_mixin_emp, modality_mixin_of).
Time Qed.
Time Lemma modality_mono P Q : (P \226\138\162 Q) \226\134\146 M P \226\138\162 M Q.
Time Proof.
Time (eapply modality_mixin_mono, modality_mixin_of).
Time Qed.
Time Lemma modality_sep P Q : M P \226\136\151 M Q \226\138\162 M (P \226\136\151 Q).
Time Proof.
Time (eapply modality_mixin_sep, modality_mixin_of).
Time Qed.
Time #[global]Instance modality_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) M).
Time Proof.
Time (intros P Q).
Time (apply modality_mono).
Time Qed.
Time #[global]
Instance modality_flip_mono' : (Proper (flip (\226\138\162) ==> flip (\226\138\162)) M).
Time Proof.
Time (intros P Q).
Time (apply modality_mono).
Time Qed.
Time #[global]Instance modality_proper : (Proper ((\226\137\161) ==> (\226\137\161)) M).
Time Proof.
Time (intros P Q).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !equiv_spec =>- 
  [? ?]; eauto using modality_mono).
Time Qed.
Time
Lemma intuitionistically_ownM (a : M) :
  CoreId a \226\134\146 \226\150\161 uPred_ownM a \226\138\163\226\138\162 uPred_ownM a.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /bi_intuitionistically
  affine_affinely =>?; apply (anti_symm _);
  [ by rewrite persistently_elim |  ]).
Time Qed.
Time End modality.
Time Section modality1.
Time Context {PROP} (M : modality PROP PROP).
Time
Lemma modality_intuitionistic_forall C P :
  modality_intuitionistic_action M = MIEnvForall C \226\134\146 C P \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time by rewrite {+1}persistently_ownM_core core_id_core.
Time Qed.
Time
Lemma modality_and_forall C P Q :
  modality_intuitionistic_action M = MIEnvForall C \226\134\146 M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time
Lemma modality_intuitionistic_id P :
  modality_intuitionistic_action M = MIEnvId \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time
Lemma modality_spatial_forall C P :
  modality_spatial_action M = MIEnvForall C \226\134\146 C P \226\134\146 P \226\138\162 M P.
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time Lemma ownM_invalid (a : M) : \194\172 \226\156\147{0} a \226\134\146 uPred_ownM a \226\138\162 False.
Time Proof.
Time by intros; rewrite ownM_valid cmra_valid_elim.
Time Qed.
Time
Lemma modality_spatial_id P : modality_spatial_action M = MIEnvId \226\134\146 P \226\138\162 M P.
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time #[global]
Instance ownM_mono : (Proper (flip (\226\137\188) ==> (\226\138\162)) (@uPred_ownM M)).
Time Proof.
Time (intros a b [b' ->]).
Time Qed.
Time
Lemma modality_intuitionistic_forall_big_and C Ps :
  modality_intuitionistic_action M = MIEnvForall C
  \226\134\146 Forall C Ps \226\134\146 \226\150\161 [\226\136\167] Ps \226\138\162 M (\226\150\161 [\226\136\167] Ps).
Time Proof.
Time (induction 2 as [| P Ps ? _ IH]; simpl).
Time -
Time by rewrite intuitionistically_True_emp -modality_emp.
Time by rewrite ownM_op sep_elim_l.
Time -
Time rewrite intuitionistically_and -modality_and_forall // -IH.
Time Qed.
Time Lemma ownM_unit' : uPred_ownM \206\181 \226\138\163\226\138\162 True.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm _) ; first  by
 apply pure_intro).
Time (apply ownM_unit).
Time Qed.
Time Lemma plainly_cmra_valid {A : cmraT} (a : A) : \226\150\160 \226\156\147 a \226\138\163\226\138\162 \226\156\147 a.
Time Proof.
Time (apply (anti_symm _), plainly_cmra_valid_1).
Time (apply plainly_elim, _).
Time Qed.
Time Lemma intuitionistically_cmra_valid {A : cmraT} (a : A) : \226\150\161 \226\156\147 a \226\138\163\226\138\162 \226\156\147 a.
Time Proof.
Time rewrite /bi_intuitionistically affine_affinely.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; apply (anti_symm _) ; first  by
 rewrite persistently_elim).
Time apply : {}persistently_cmra_valid_1 {}.
Time by rewrite {+1}(modality_intuitionistic_forall _ P).
Time Qed.
Time Lemma bupd_ownM_update x y : x ~~> y \226\134\146 uPred_ownM x \226\138\162 |==> uPred_ownM y.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; rewrite (bupd_ownM_updateP _ (y =))
 ; last  by apply cmra_update_updateP).
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply bupd_mono, exist_elim =>y';
  <ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>{+}->.
Time Qed.
Time
Lemma modality_spatial_forall_big_sep C Ps :
  modality_spatial_action M = MIEnvForall C
  \226\134\146 Forall C Ps \226\134\146 [\226\136\151] Ps \226\138\162 M ([\226\136\151] Ps).
Time Qed.
Time #[global]
Instance valid_timeless  {A : cmraT} `{!CmraDiscrete A} 
 (a : A): (Timeless (\226\156\147 a : uPred M)%I).
Time Proof.
Time rewrite /Timeless !discrete_valid.
Time Proof.
Time (induction 2 as [| P Ps ? _ IH]; simpl).
Time -
Time by rewrite -modality_emp.
Time -
Time by rewrite -modality_sep -IH {+1}(modality_spatial_forall _ P).
Time (apply (timeless _)).
Time Qed.
Time #[global]
Instance ownM_timeless  (a : M): (Discrete a \226\134\146 Timeless (uPred_ownM a)).
Time Proof.
Time (intros ?).
Time rewrite /Timeless later_ownM.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>b).
Time
rewrite (timeless (a \226\137\161 b)) (except_0_intro (uPred_ownM b)) -except_0_and.
Time Qed.
Time End modality1.
Time
Lemma modality_id_mixin {PROP : bi} :
  modality_mixin (@id PROP) MIEnvId MIEnvId.
Time Proof.
Time (split; simpl; eauto).
Time Qed.
Time
Definition modality_id {PROP : bi} := Modality (@id PROP) modality_id_mixin.
Time (apply except_0_mono).
Time rewrite internal_eq_sym.
Time
(apply (internal_eq_rewrite' b a uPred_ownM _); auto
  using and_elim_l, and_elim_r).
Time Qed.
Time #[global]
Instance cmra_valid_plain  {A : cmraT} (a : A): (Plain (\226\156\147 a : uPred M)%I).
Time Proof.
Time rewrite /Persistent.
Time (apply plainly_cmra_valid_1).
Time Qed.
Time #[global]
Instance cmra_valid_persistent  {A : cmraT} (a : A):
 (Persistent (\226\156\147 a : uPred M)%I).
Time Proof.
Time rewrite /Persistent.
Time (apply persistently_cmra_valid_1).
Time Qed.
Time #[global]
Instance ownM_persistent  a: (CoreId a \226\134\146 Persistent (@uPred_ownM M a)).
Time Proof.
Time (intros).
Time rewrite /Persistent -{+2}(core_id_core a).
Time (apply persistently_ownM_core).
Time Qed.
Time #[global]
Instance uPred_ownM_sep_homomorphism :
 (MonoidHomomorphism op uPred_sep (\226\137\161) (@uPred_ownM M)).
Time Proof.
Time (split; [ split; try apply _ |  ]).
Time (apply ownM_op).
Time (apply ownM_unit').
Time Qed.
Time
Lemma bupd_plain_soundness P `{!Plain P} :
  bi_emp_valid (|==> P) \226\134\146 bi_emp_valid P.
Time Proof.
Time (eapply bi_emp_valid_mono).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; last  exact : {}bupd_plainly {}).
Time (apply bupd_mono').
Time apply : {}plain {}.
Time Qed.
Time Corollary soundness \207\134 n : (\226\150\183^n \226\140\156\207\134\226\140\157 : uPred M)%I \226\134\146 \207\134.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> induction n as [| n IH] =>/=).
Time -
Time (apply pure_soundness).
Time -
Time (intros H).
Time by apply IH, later_soundness.
Time Qed.
Time Corollary consistency_modal n : \194\172 (\226\150\183^n False : uPred M)%I.
Time Proof.
Time exact (soundness False n).
Time Qed.
Time Corollary consistency : \194\172 (False : uPred M)%I.
Time Proof.
Time exact (consistency_modal 0).
Time Qed.
Time End derived.
Time End uPred.
