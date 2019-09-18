Time From iris.bi Require Import bi.
Time From iris.proofmode Require Export classes.
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
Time -
Time (intros P Q).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoEmbed =>{+}->).
Time by rewrite embed_intuitionistically_2.
Time -
Time by intros P Q ->.
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
Time Qed.
Time
Definition modality_plainly `{BiPlainly PROP} :=
  Modality _ modality_plainly_mixin.
Time
Lemma modality_laterN_mixin n :
  modality_mixin (@sbi_laterN PROP n)
    (MIEnvTransform (MaybeIntoLaterN false n))
    (MIEnvTransform (MaybeIntoLaterN false n)).
Time Proof.
Time
(split; simpl; split_and ?; eauto
  using equiv_entails_sym, laterN_intro, laterN_mono, laterN_and, laterN_sep
  with typeclass_instances).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /MaybeIntoLaterN =>P Q {+}->).
Time by rewrite laterN_intuitionistically_2.
Time Qed.
Time Definition modality_laterN n := Modality _ (modality_laterN_mixin n).
Time End sbi_modalities.
