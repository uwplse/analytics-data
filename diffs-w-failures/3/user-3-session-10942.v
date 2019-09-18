Time From iris.bi Require Import bi.
Time From stdpp Require Import nat_cancel.
Time From iris.bi Require Import bi tactics.
Time From iris.proofmode Require Export classes.
Time From iris.proofmode Require Import classes.
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
Time Set Default Proof Using "Type".
Time Import bi.
Time Section bi.
Time Context {PROP : bi}.
Time Implicit Types P Q R : PROP.
Time #[global]
Instance frame_here_absorbing  p R: (Absorbing R \226\134\146 Frame p R R True) |0.
Time Proof.
Time (intros).
Time by rewrite /Frame intuitionistically_if_elim sep_elim_l.
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
Time Qed.
Time #[global]Instance frame_here  p R: (Frame p R R emp) |1.
Time Proof.
Time (intros).
Time by rewrite /Frame intuitionistically_if_elim sep_elim_l.
Time -
Time (intros P Q).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoEmbed =>{+}->).
Time Qed.
Time #[global]
Instance frame_affinely_here_absorbing  p R:
 (Absorbing R \226\134\146 Frame p (<affine> R) R True) |0.
Time Proof.
Time (intros).
Time by rewrite embed_intuitionistically_2.
Time rewrite /Frame intuitionistically_if_elim affinely_elim.
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
Time (apply sep_elim_l, _).
Time Qed.
Time #[global]
Instance frame_affinely_here  p R: (Frame p (<affine> R) R emp) |1.
Time Proof.
Time (intros).
Time rewrite /Frame intuitionistically_if_elim affinely_elim.
Time (apply sep_elim_l, _).
Time Qed.
Time #[global]
Instance frame_here_pure_persistent  a \207\134 Q:
 (FromPure a Q \207\134 \226\134\146 Frame true \226\140\156\207\134\226\140\157 Q emp).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure /Frame /= =>{+}<-).
Time rewrite right_id.
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
Time by rewrite -affinely_affinely_if intuitionistically_affinely.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /MaybeIntoLaterN =>P Q {+}->).
Time Qed.
Time #[global]
Instance frame_here_pure  a \207\134 Q:
 (FromPure a Q \207\134
  \226\134\146 TCOr (TCEq a false) (BiAffine PROP) \226\134\146 Frame false \226\140\156\207\134\226\140\157 Q emp).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure /Frame =>{+}<-
 [{+}->|?] /=).
Time by rewrite laterN_intuitionistically_2.
Time -
Time by rewrite right_id.
Time -
Time Qed.
Time Definition modality_laterN n := Modality _ (modality_laterN_mixin n).
Time End sbi_modalities.
Time by rewrite right_id -affinely_affinely_if affine_affinely.
Time Qed.
Time #[global]
Instance make_embed_pure  `{BiEmbed PROP PROP'} \207\134:
 (KnownMakeEmbed (PROP:=PROP) \226\140\156\207\134\226\140\157 \226\140\156\207\134\226\140\157).
Time Proof.
Time (apply embed_pure).
Time Qed.
Time #[global]
Instance make_embed_emp  `{BiEmbedEmp PROP PROP'}:
 (KnownMakeEmbed (PROP:=PROP) emp emp).
Time Proof.
Time (apply embed_emp).
Time Qed.
Time #[global]
Instance make_embed_default  `{BiEmbed PROP PROP'} 
 P: (MakeEmbed P \226\142\161 P \226\142\164) |100.
Time Proof.
Time by rewrite /MakeEmbed.
Time Qed.
Time #[global]
Instance frame_embed  `{BiEmbed PROP PROP'} p P Q 
 (Q' : PROP') R: (Frame p R P Q \226\134\146 MakeEmbed Q Q' \226\134\146 Frame p \226\142\161 R \226\142\164 \226\142\161 P \226\142\164 Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeEmbed =>{+}<- {+}<-).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite embed_sep
 embed_intuitionistically_if_2 =>//).
Time Qed.
Time #[global]
Instance frame_pure_embed  `{BiEmbed PROP PROP'} p 
 P Q (Q' : PROP') \207\134:
 (Frame p \226\140\156\207\134\226\140\157 P Q \226\134\146 MakeEmbed Q Q' \226\134\146 Frame p \226\140\156\207\134\226\140\157 \226\142\161 P \226\142\164 Q').
Time Proof.
Time rewrite /Frame /MakeEmbed -embed_pure.
Time (apply (frame_embed p P Q)).
Time Qed.
Time #[global]Instance make_sep_emp_l  P: (KnownLMakeSep emp P P).
Time Proof.
Time (apply left_id, _).
Time Qed.
Time #[global]Instance make_sep_emp_r  P: (KnownRMakeSep P emp P).
Time Proof.
Time (apply right_id, _).
Time Qed.
Time #[global]
Instance make_sep_true_l  P: (Absorbing P \226\134\146 KnownLMakeSep True P P).
Time Proof.
Time (intros).
Time (apply True_sep, _).
Time Qed.
Time #[global]
Instance make_sep_true_r  P: (Absorbing P \226\134\146 KnownRMakeSep P True P).
Time Proof.
Time (intros).
Time by rewrite /KnownRMakeSep /MakeSep sep_True.
Time Qed.
Time #[global]Instance make_sep_default  P Q: (MakeSep P Q (P \226\136\151 Q)) |100.
Time Proof.
Time by rewrite /MakeSep.
Time Qed.
Time #[global]
Instance frame_sep_persistent_l  progress R P1 P2 
 Q1 Q2 Q':
 (Frame true R P1 Q1
  \226\134\146 MaybeFrame true R P2 Q2 progress
    \226\134\146 MakeSep Q1 Q2 Q' \226\134\146 Frame true R (P1 \226\136\151 P2) Q') |9.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MaybeFrame /MakeSep /=
 =>{+}<- {+}<- {+}<-).
Time rewrite {+1}(intuitionistically_sep_dup R).
Time solve_sep_entails.
Time Qed.
Time #[global]
Instance frame_sep_l  R P1 P2 Q Q':
 (Frame false R P1 Q \226\134\146 MakeSep Q P2 Q' \226\134\146 Frame false R (P1 \226\136\151 P2) Q') |9.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeSep =>{+}<- {+}<-).
Time by rewrite assoc.
Time Qed.
Time #[global]
Instance frame_sep_r  p R P1 P2 Q Q':
 (Frame p R P2 Q \226\134\146 MakeSep P1 Q Q' \226\134\146 Frame p R (P1 \226\136\151 P2) Q') |10.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeSep =>{+}<- {+}<-).
Time by rewrite assoc -(comm _ P1) assoc.
Time Qed.
Time #[global]
Instance frame_big_sepL_cons  {A} p (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 R Q l x l':
 (IsCons l x l'
  \226\134\146 Frame p R (\206\166 0 x \226\136\151 ([\226\136\151 list] k\226\134\166y \226\136\136 l', \206\166 (S k) y)) Q
    \226\134\146 Frame p R ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}->).
Time by rewrite /Frame big_sepL_cons.
Time Qed.
Time #[global]
Instance frame_big_sepL_app  {A} p (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 R Q l l1 l2:
 (IsApp l l1 l2
  \226\134\146 Frame p R
      (([\226\136\151 list] k\226\134\166y \226\136\136 l1, \206\166 k y) \226\136\151 ([\226\136\151 list] k\226\134\166y \226\136\136 l2, \206\166 (length l1 + k) y))
      Q \226\134\146 Frame p R ([\226\136\151 list] k\226\134\166y \226\136\136 l, \206\166 k y) Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsApp =>{+}->).
Time by rewrite /Frame big_sepL_app.
Time Qed.
Time #[global]
Instance frame_big_sepL2_cons  {A} {B} p (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
 R Q l1 x1 l1' l2 x2 l2':
 (IsCons l1 x1 l1'
  \226\134\146 IsCons l2 x2 l2'
    \226\134\146 Frame p R (\206\166 0 x1 x2 \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 (S k) y1 y2)) Q
      \226\134\146 Frame p R ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2) Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsCons =>{+}-> {+}->).
Time by rewrite /Frame big_sepL2_cons.
Time Qed.
Time #[global]
Instance frame_big_sepL2_app  {A} {B} p (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
 R Q l1 l1' l1'' l2 l2' l2'':
 (IsApp l1 l1' l1''
  \226\134\146 IsApp l2 l2' l2''
    \226\134\146 Frame p R
        (([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1';l2', \206\166 k y1 y2)
         \226\136\151 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1'';l2'', \206\166 (length l1' + k) y1 y2)) Q
      \226\134\146 Frame p R ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IsApp /Frame =>{+}-> {+}->
 {+}->).
Time (apply wand_elim_l', big_sepL2_app).
Time Qed.
Time #[global]
Instance frame_big_sepMS_disj_union  `{Countable A} 
 p (\206\166 : A \226\134\146 PROP) R Q X1 X2:
 (Frame p R (([\226\136\151 mset] y \226\136\136 X1, \206\166 y) \226\136\151 ([\226\136\151 mset] y \226\136\136 X2, \206\166 y)) Q
  \226\134\146 Frame p R ([\226\136\151 mset] y \226\136\136 (X1 \226\138\142 X2), \206\166 y) Q).
Time Proof.
Time by rewrite /Frame big_sepMS_disj_union.
Time Qed.
Time #[global]Instance make_and_true_l  P: (KnownLMakeAnd True P P).
Time Proof.
Time (apply left_id, _).
Time Qed.
Time #[global]Instance make_and_true_r  P: (KnownRMakeAnd P True P).
Time Proof.
Time by rewrite /KnownRMakeAnd /MakeAnd right_id.
Time Qed.
Time #[global]Instance make_and_emp_l  P: (Affine P \226\134\146 KnownLMakeAnd emp P P).
Time Proof.
Time (intros).
Time by rewrite /KnownLMakeAnd /MakeAnd emp_and.
Time Qed.
Time #[global]Instance make_and_emp_r  P: (Affine P \226\134\146 KnownRMakeAnd P emp P).
Time Proof.
Time (intros).
Time by rewrite /KnownRMakeAnd /MakeAnd and_emp.
Time Qed.
Time #[global]Instance make_and_default  P Q: (MakeAnd P Q (P \226\136\167 Q)) |100.
Time Proof.
Time by rewrite /MakeAnd.
Time Qed.
Time #[global]
Instance frame_and  p progress1 progress2 R P1 P2 
 Q1 Q2 Q':
 (MaybeFrame p R P1 Q1 progress1
  \226\134\146 MaybeFrame p R P2 Q2 progress2
    \226\134\146 TCEq (progress1 || progress2) true
      \226\134\146 MakeAnd Q1 Q2 Q' \226\134\146 Frame p R (P1 \226\136\167 P2) Q') |9.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /MaybeFrame /Frame /MakeAnd
 =>{+}<- {+}<- _ {+}<-).
Time (apply and_intro; [ rewrite and_elim_l | rewrite and_elim_r ]; done).
Time Qed.
Time #[global]Instance make_or_true_l  P: (KnownLMakeOr True P True).
Time Proof.
Time (apply left_absorb, _).
Time Qed.
Time #[global]Instance make_or_true_r  P: (KnownRMakeOr P True True).
Time Proof.
Time by rewrite /KnownRMakeOr /MakeOr right_absorb.
Time Qed.
Time #[global]Instance make_or_emp_l  P: (Affine P \226\134\146 KnownLMakeOr emp P emp).
Time Proof.
Time (intros).
Time by rewrite /KnownLMakeOr /MakeOr emp_or.
Time Qed.
Time #[global]Instance make_or_emp_r  P: (Affine P \226\134\146 KnownRMakeOr P emp emp).
Time Proof.
Time (intros).
Time by rewrite /KnownRMakeOr /MakeOr or_emp.
Time Qed.
Time #[global]Instance make_or_default  P Q: (MakeOr P Q (P \226\136\168 Q)) |100.
Time Proof.
Time by rewrite /MakeOr.
Time Qed.
Time #[global]
Instance frame_or_spatial  progress1 progress2 R P1 
 P2 Q1 Q2 Q:
 (MaybeFrame false R P1 Q1 progress1
  \226\134\146 MaybeFrame false R P2 Q2 progress2
    \226\134\146 TCOr (TCEq (progress1 && progress2) true)
        (TCOr (TCAnd (TCEq progress1 true) (TCEq Q1 True%I))
           (TCAnd (TCEq progress2 true) (TCEq Q2 True%I)))
      \226\134\146 MakeOr Q1 Q2 Q \226\134\146 Frame false R (P1 \226\136\168 P2) Q) |9.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeOr =>{+}<- {+}<- _
 {+}<-).
Time by rewrite -sep_or_l.
Time Qed.
Time #[global]
Instance frame_or_persistent  progress1 progress2 
 R P1 P2 Q1 Q2 Q:
 (MaybeFrame true R P1 Q1 progress1
  \226\134\146 MaybeFrame true R P2 Q2 progress2
    \226\134\146 TCEq (progress1 || progress2) true
      \226\134\146 MakeOr Q1 Q2 Q \226\134\146 Frame true R (P1 \226\136\168 P2) Q) |9.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeOr =>{+}<- {+}<- _
 {+}<-).
Time by rewrite -sep_or_l.
Time Qed.
Time #[global]
Instance frame_wand  p R P1 P2 Q2:
 (Frame p R P2 Q2 \226\134\146 Frame p R (P1 -\226\136\151 P2) (P1 -\226\136\151 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>?).
Time (apply wand_intro_l).
Time by rewrite assoc (comm _ P1) -assoc wand_elim_r.
Time Qed.
Time #[global]
Instance make_affinely_True : (@KnownMakeAffinely PROP True emp) |0.
Time Proof.
Time
by rewrite /KnownMakeAffinely /MakeAffinely affinely_True_emp affinely_emp.
Time Qed.
Time #[global]
Instance make_affinely_affine  P: (Affine P \226\134\146 KnownMakeAffinely P P) |1.
Time Proof.
Time (intros).
Time by rewrite /KnownMakeAffinely /MakeAffinely affine_affinely.
Time Qed.
Time #[global]
Instance make_affinely_default  P: (MakeAffinely P (<affine> P)) |100.
Time Proof.
Time by rewrite /MakeAffinely.
Time Qed.
Time #[global]
Instance frame_affinely  R P Q Q':
 (Frame true R P Q \226\134\146 MakeAffinely Q Q' \226\134\146 Frame true R (<affine> P) Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeAffinely =>{+}<-
 {+}<- /=).
Time rewrite -{+1}(affine_affinely (\226\150\161 R)%I) affinely_sep_2 //.
Time Qed.
Time #[global]
Instance make_intuitionistically_True :
 (@KnownMakeIntuitionistically PROP True emp) |0.
Time Proof.
Time
by rewrite /KnownMakeIntuitionistically /MakeIntuitionistically
 intuitionistically_True_emp.
Time Qed.
Time #[global]
Instance make_intuitionistically_intuitionistic  P:
 (Affine P \226\134\146 Persistent P \226\134\146 KnownMakeIntuitionistically P P) |1.
Time Proof.
Time (intros).
Time rewrite /KnownMakeIntuitionistically /MakeIntuitionistically.
Time rewrite intuitionistic_intuitionistically //.
Time Qed.
Time #[global]
Instance make_intuitionistically_default  P: (MakeIntuitionistically P (\226\150\161 P))
 |100.
Time Proof.
Time by rewrite /MakeIntuitionistically.
Time Qed.
Time #[global]
Instance frame_intuitionistically  R P Q Q':
 (Frame true R P Q \226\134\146 MakeIntuitionistically Q Q' \226\134\146 Frame true R (\226\150\161 P) Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeIntuitionistically
 =>{+}<- {+}<- /=).
Time rewrite -intuitionistically_sep_2 intuitionistically_idemp //.
Time Qed.
Time #[global]
Instance make_absorbingly_emp : (@KnownMakeAbsorbingly PROP emp True) |0.
Time Proof.
Time
by rewrite /KnownMakeAbsorbingly /MakeAbsorbingly -absorbingly_True_emp
 absorbingly_pure.
Time Qed.
Time #[global]
Instance make_absorbingly_default  P: (MakeAbsorbingly P (<absorb> P)) |100.
Time Proof.
Time by rewrite /MakeAbsorbingly.
Time Qed.
Time #[global]
Instance frame_absorbingly  p R P Q Q':
 (Frame p R P Q \226\134\146 MakeAbsorbingly Q Q' \226\134\146 Frame p R (<absorb> P) Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeAbsorbingly =>{+}<-
 {+}<- /=).
Time by rewrite absorbingly_sep_r.
Time Qed.
Time #[global]
Instance make_persistently_true : (@KnownMakePersistently PROP True True).
Time Proof.
Time by rewrite /KnownMakePersistently /MakePersistently persistently_pure.
Time Qed.
Time #[global]
Instance make_persistently_emp : (@KnownMakePersistently PROP emp True).
Time Proof.
Time
by rewrite /KnownMakePersistently /MakePersistently -persistently_True_emp
 persistently_pure.
Time Qed.
Time #[global]
Instance make_persistently_default  P: (MakePersistently P (<pers> P)) |100.
Time Proof.
Time by rewrite /MakePersistently.
Time Qed.
Time #[global]
Instance frame_persistently  R P Q Q':
 (Frame true R P Q \226\134\146 MakePersistently Q Q' \226\134\146 Frame true R (<pers> P) Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakePersistently =>{+}<-
 {+}<- /=).
Time rewrite -persistently_and_intuitionistically_sep_l.
Time
by rewrite -persistently_sep_2 -persistently_and_sep_l_1
 persistently_affinely_elim persistently_idemp.
Time Qed.
Time #[global]
Instance frame_exist  {A} p R (\206\166 \206\168 : A \226\134\146 PROP):
 ((\226\136\128 a, Frame p R (\206\166 a) (\206\168 a)) \226\134\146 Frame p R (\226\136\131 x, \206\166 x) (\226\136\131 x, \206\168 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>?).
Time by rewrite sep_exist_l; apply exist_mono.
Time Qed.
Time #[global]
Instance frame_forall  {A} p R (\206\166 \206\168 : A \226\134\146 PROP):
 ((\226\136\128 a, Frame p R (\206\166 a) (\206\168 a)) \226\134\146 Frame p R (\226\136\128 x, \206\166 x) (\226\136\128 x, \206\168 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>?).
Time by rewrite sep_forall_l; apply forall_mono.
Time Qed.
Time #[global]
Instance frame_impl_persistent  R P1 P2 Q2:
 (Frame true R P2 Q2 \226\134\146 Frame true R (P1 \226\134\146 P2) (P1 \226\134\146 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /= =>?).
Time (apply impl_intro_l).
Time
by rewrite -persistently_and_intuitionistically_sep_l assoc 
 (comm _ P1) -assoc impl_elim_r persistently_and_intuitionistically_sep_l.
Time Qed.
Time #[global]
Instance frame_impl  R P1 P2 Q2:
 (Persistent P1
  \226\134\146 Absorbing P1 \226\134\146 Frame false R P2 Q2 \226\134\146 Frame false R (P1 \226\134\146 P2) (P1 \226\134\146 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /= =>? ? ?).
Time (apply impl_intro_l).
Time
rewrite {+1}(persistent P1) persistently_and_intuitionistically_sep_l assoc.
Time
rewrite (comm _ (\226\150\161 P1)%I) -assoc -persistently_and_intuitionistically_sep_l.
Time rewrite persistently_elim impl_elim_r //.
Time Qed.
Time End bi.
Time Section sbi.
Time Context {PROP : sbi}.
Time Implicit Types P Q R : PROP.
Time #[global]
Instance frame_eq_embed  `{SbiEmbed PROP PROP'} p 
 P Q (Q' : PROP') {A : ofeT} (a b : A):
 (Frame p (a \226\137\161 b) P Q \226\134\146 MakeEmbed Q Q' \226\134\146 Frame p (a \226\137\161 b) \226\142\161 P \226\142\164 Q').
Time Proof.
Time rewrite /Frame /MakeEmbed -embed_internal_eq.
Time (apply (frame_embed p P Q)).
Time Qed.
Time #[global]
Instance make_laterN_true  n: (@KnownMakeLaterN PROP n True True) |0.
Time Proof.
Time by rewrite /KnownMakeLaterN /MakeLaterN laterN_True.
Time Qed.
Time #[global]
Instance make_laterN_emp  `{!BiAffine PROP} n:
 (@KnownMakeLaterN PROP n emp emp) |0.
Time Proof.
Time by rewrite /KnownMakeLaterN /MakeLaterN laterN_emp.
Time Qed.
Time #[global]Instance make_laterN_default  P: (MakeLaterN n P (\226\150\183^n P)) |100.
Time Proof.
Time by rewrite /MakeLaterN.
Time Qed.
Time #[global]
Instance frame_later  p R R' P Q Q':
 (TCNoBackTrack (MaybeIntoLaterN true 1 R' R)
  \226\134\146 Frame p R P Q \226\134\146 MakeLaterN 1 Q Q' \226\134\146 Frame p R' (\226\150\183 P) Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeLaterN
 /MaybeIntoLaterN =>- [{+}->] {+}<- {+}<-).
Time by rewrite later_intuitionistically_if_2 later_sep.
Time Qed.
Time #[global]
Instance frame_laterN  p n R R' P Q Q':
 (TCNoBackTrack (MaybeIntoLaterN true n R' R)
  \226\134\146 Frame p R P Q \226\134\146 MakeLaterN n Q Q' \226\134\146 Frame p R' (\226\150\183^n P) Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeLaterN
 /MaybeIntoLaterN =>- [{+}->] {+}<- {+}<-).
Time by rewrite laterN_intuitionistically_if_2 laterN_sep.
Time Qed.
Time #[global]
Instance frame_bupd  `{BiBUpd PROP} p R P Q:
 (Frame p R P Q \226\134\146 Frame p R (|==> P) (|==> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>{+}<-).
Time by rewrite bupd_frame_l.
Time Qed.
Time #[global]
Instance frame_fupd  `{BiFUpd PROP} p E1 E2 R P Q:
 (Frame p R P Q \226\134\146 Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>{+}<-).
Time by rewrite fupd_frame_l.
Time Qed.
Time #[global]
Instance make_except_0_True : (@KnownMakeExcept0 PROP True True).
Time Proof.
Time by rewrite /KnownMakeExcept0 /MakeExcept0 except_0_True.
Time Qed.
Time #[global]Instance make_except_0_default  P: (MakeExcept0 P (\226\151\135 P)) |100.
Time Proof.
Time by rewrite /MakeExcept0.
Time Qed.
Time #[global]
Instance frame_except_0  p R P Q Q':
 (Frame p R P Q \226\134\146 MakeExcept0 Q Q' \226\134\146 Frame p R (\226\151\135 P) Q').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame /MakeExcept0 =>{+}<-
 {+}<-).
Time by rewrite except_0_sep -(except_0_intro (\226\150\161?p R)%I).
Time Qed.
Time End sbi.
