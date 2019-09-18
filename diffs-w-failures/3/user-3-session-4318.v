Time From iris.proofmode Require Export classes.
Time From iris.bi Require Import bi.
Time From iris.proofmode Require Export classes.
Time From iris.algebra Require Export cmra.
Time Set Default Proof Using "Type".
Time Import bi.
Time Section bi_modalities.
Time Context {PROP : bi}.
Time
Lemma modality_persistently_mixin :
  modality_mixin (@bi_persistently PROP) MIEnvId MIEnvClear.
Time Proof.
Time
(split; simpl; eauto
  using equiv_entails_sym, persistently_intro, persistently_mono,
    persistently_sep_2 with typeclass_instances).
Time Qed.
Time
Definition modality_persistently := Modality _ modality_persistently_mixin.
Time
Lemma modality_affinely_mixin :
  modality_mixin (@bi_affinely PROP) MIEnvId (MIEnvForall Affine).
Time Proof.
Time
(split; simpl; eauto
  using equiv_entails_sym, affinely_intro, affinely_mono, affinely_sep_2
  with typeclass_instances).
Time Qed.
Time Definition modality_affinely := Modality _ modality_affinely_mixin.
Time
Lemma modality_intuitionistically_mixin :
  modality_mixin (@bi_intuitionistically PROP) MIEnvId MIEnvIsEmpty.
Time Proof.
Time
(split; simpl; eauto
  using equiv_entails_sym, intuitionistically_emp, affinely_mono,
    persistently_mono, intuitionistically_idemp, intuitionistically_sep_2
  with typeclass_instances).
Time Class IsOp {A : cmraT} (a b1 b2 : A) :=
         is_op : a \226\137\161 b1 \226\139\133 b2.
Time Qed.
Time
Definition modality_intuitionistically :=
  Modality _ modality_intuitionistically_mixin.
Time
Lemma modality_embed_mixin `{BiEmbed PROP PROP'} :
  modality_mixin (@embed PROP PROP' _) (MIEnvTransform IntoEmbed)
    (MIEnvTransform IntoEmbed).
Time Proof.
Time
(split; simpl; split_and ?; eauto
  using equiv_entails_sym, embed_emp_2, embed_sep, embed_and).
Time Arguments is_op {_} _ _ _ {_}.
Time Hint Mode IsOp + - - -: typeclass_instances.
Time Instance is_op_op  {A : cmraT} (a b : A): (IsOp (a \226\139\133 b) a b) |100.
Time Proof.
Time by rewrite /IsOp.
Time Qed.
Time Class IsOp' {A : cmraT} (a b1 b2 : A) :=
         is_op' :> IsOp a b1 b2.
Time Hint Mode IsOp' + ! - -: typeclass_instances.
Time Hint Mode IsOp' + - ! !: typeclass_instances.
Time Class IsOp'LR {A : cmraT} (a b1 b2 : A) :=
         is_op_lr : IsOp a b1 b2.
Time -
Time (intros P Q).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoEmbed =>{+}->).
Time Existing Instance is_op_lr |0.
Time Hint Mode IsOp'LR + ! - -: typeclass_instances.
Time Instance is_op_lr_op  {A : cmraT} (a b : A): (IsOp'LR (a \226\139\133 b) a b) |0.
Time Proof.
Time by rewrite /IsOp'LR /IsOp.
Time Qed.
Time #[global]
Instance is_op_pair  {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B):
 (IsOp a b1 b2 \226\134\146 IsOp a' b1' b2' \226\134\146 IsOp' (a, a') (b1, b1') (b2, b2')).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]
Instance is_op_pair_core_id_l  {A B : cmraT} (a : A) 
 (a' b1' b2' : B):
 (CoreId a \226\134\146 IsOp a' b1' b2' \226\134\146 IsOp' (a, a') (a, b1') (a, b2')).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>//=).
Time by rewrite embed_intuitionistically_2.
Time by rewrite -core_id_dup.
Time -
Time by intros P Q ->.
Time Qed.
Time #[global]
Instance is_op_pair_core_id_r  {A B : cmraT} (a b1 b2 : A) 
 (a' : B): (CoreId a' \226\134\146 IsOp a b1 b2 \226\134\146 IsOp' (a, a') (b1, a') (b2, a')).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>//=).
Time Qed.
Time
Definition modality_embed `{BiEmbed PROP PROP'} :=
  Modality _ modality_embed_mixin.
Time End bi_modalities.
Time Section sbi_modalities.
Time Context {PROP : sbi}.
Time
Lemma modality_plainly_mixin `{BiPlainly PROP} :
  modality_mixin (@plainly PROP _) (MIEnvForall Plain) MIEnvClear.
Time Proof.
Time
(split; simpl; split_and ?; eauto
  using equiv_entails_sym, plainly_intro, plainly_mono, plainly_and,
    plainly_sep_2 with typeclass_instances).
Time by rewrite -core_id_dup.
Time Qed.
Time Qed.
Time
Definition modality_plainly `{BiPlainly PROP} :=
  Modality _ modality_plainly_mixin.
Time
Lemma modality_laterN_mixin n :
  modality_mixin (@sbi_laterN PROP n)
    (MIEnvTransform (MaybeIntoLaterN false n))
    (MIEnvTransform (MaybeIntoLaterN false n)).
Time #[global]
Instance is_op_Some  {A : cmraT} (a : A) b1 b2:
 (IsOp a b1 b2 \226\134\146 IsOp' (Some a) (Some b1) (Some b2)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance is_op_plus  (n1 n2 : nat): (IsOp (n1 + n2) n1 n2).
Time Proof.
Time done.
Time Proof.
Time
(split; simpl; split_and ?; eauto
  using equiv_entails_sym, laterN_intro, laterN_mono, laterN_and, laterN_sep
  with typeclass_instances).
Time Qed.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /MaybeIntoLaterN =>P Q {+}->).
Time by rewrite laterN_intuitionistically_2.
Time Qed.
Time Definition modality_laterN n := Modality _ (modality_laterN_mixin n).
Time End sbi_modalities.
