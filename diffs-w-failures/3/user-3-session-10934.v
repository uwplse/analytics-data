Time From iris.bi Require Export derived_connectives updates plainly.
Time From iris.algebra Require Import monoid.
Time
From iris.bi Require Import interface derived_laws_sbi big_op plainly updates.
Time From iris.base_logic Require Export upred.
Time Class Embed (A B : Type) :=
         embed : A \226\134\146 B.
Time Arguments embed {_} {_} {_} _%I : simpl never.
Time Notation "\226\142\161 P \226\142\164" := (embed P) : bi_scope.
Time Instance: (Params (@embed) 3) := { }.
Time Typeclasses Opaque embed.
Time Hint Mode Embed ! -: typeclass_instances.
Time Hint Mode Embed - !: typeclass_instances.
Time
Record BiEmbedMixin (PROP1 PROP2 : bi) `(Embed PROP1 PROP2) :={
 bi_embed_mixin_ne : NonExpansive (embed (A:=PROP1) (B:=PROP2));
 bi_embed_mixin_mono : Proper ((\226\138\162) ==> (\226\138\162)) (embed (A:=PROP1) (B:=PROP2));
 bi_embed_mixin_emp_valid_inj :
  forall P : PROP1, bi_emp_valid (PROP:=PROP2) \226\142\161 P \226\142\164 \226\134\146 bi_emp_valid P;
 bi_embed_mixin_emp_2 : emp \226\138\162@{ PROP2} \226\142\161 emp \226\142\164;
 bi_embed_mixin_impl_2 :
  forall P Q : PROP1, (\226\142\161 P \226\142\164 \226\134\146 \226\142\161 Q \226\142\164) \226\138\162@{ PROP2} \226\142\161 P \226\134\146 Q \226\142\164;
 bi_embed_mixin_forall_2 :
  forall A (\206\166 : A \226\134\146 PROP1), (\226\136\128 x, \226\142\161 \206\166 x \226\142\164) \226\138\162@{ PROP2} \226\142\161 \226\136\128 x, \206\166 x \226\142\164;
 bi_embed_mixin_exist_1 :
  forall A (\206\166 : A \226\134\146 PROP1), \226\142\161 \226\136\131 x, \206\166 x \226\142\164 \226\138\162@{ PROP2} \226\136\131 x, \226\142\161 \206\166 x \226\142\164;
 bi_embed_mixin_sep : forall P Q : PROP1, \226\142\161 P \226\136\151 Q \226\142\164 \226\138\163\226\138\162@{ PROP2} \226\142\161 P \226\142\164 \226\136\151 \226\142\161 Q \226\142\164;
 bi_embed_mixin_wand_2 :
  forall P Q : PROP1, (\226\142\161 P \226\142\164 -\226\136\151 \226\142\161 Q \226\142\164) \226\138\162@{ PROP2} \226\142\161 P -\226\136\151 Q \226\142\164;
 bi_embed_mixin_persistently :
  forall P : PROP1, \226\142\161 <pers> P \226\142\164 \226\138\163\226\138\162@{ PROP2} <pers> \226\142\161 P \226\142\164}.
Time
Class BiEmbed (PROP1 PROP2 : bi) :={bi_embed_embed :> Embed PROP1 PROP2;
                                    bi_embed_mixin :
                                     BiEmbedMixin PROP1 PROP2 bi_embed_embed}.
Time Hint Mode BiEmbed ! -: typeclass_instances.
Time Hint Mode BiEmbed - !: typeclass_instances.
Time Arguments bi_embed_embed : simpl never.
Time
Class BiEmbedEmp (PROP1 PROP2 : bi) `{BiEmbed PROP1 PROP2} :={
 embed_emp_1 : \226\142\161 emp : PROP1 \226\142\164 \226\138\162 emp}.
Time Hint Mode BiEmbedEmp ! - -: typeclass_instances.
Time Hint Mode BiEmbedEmp - ! -: typeclass_instances.
Time
Class SbiEmbed (PROP1 PROP2 : sbi) `{BiEmbed PROP1 PROP2} :={
 embed_internal_eq_1 : forall (A : ofeT) (x y : A), \226\142\161 x \226\137\161 y \226\142\164 \226\138\162 x \226\137\161 y;
 embed_later : forall P, \226\142\161 \226\150\183 P \226\142\164 \226\138\163\226\138\162 \226\150\183 \226\142\161 P \226\142\164;
 embed_interal_inj :
  forall (PROP' : sbi) (P Q : PROP1), \226\142\161 P \226\142\164 \226\137\161 \226\142\161 Q \226\142\164 \226\138\162@{ PROP'} P \226\137\161 Q}.
Time Hint Mode SbiEmbed ! - -: typeclass_instances.
Time Hint Mode SbiEmbed - ! -: typeclass_instances.
Time
Class BiEmbedBUpd (PROP1 PROP2 : bi) `{BiEmbed PROP1 PROP2} 
`{BiBUpd PROP1} `{BiBUpd PROP2} :={embed_bupd :
                                    forall P,
                                    \226\142\161 |==> P \226\142\164 \226\138\163\226\138\162@{ PROP2} (|==> \226\142\161 P \226\142\164)}.
Time Hint Mode BiEmbedBUpd - ! - - -: typeclass_instances.
Time Hint Mode BiEmbedBUpd ! - - - -: typeclass_instances.
Time
Class BiEmbedFUpd (PROP1 PROP2 : sbi) `{BiEmbed PROP1 PROP2} 
`{BiFUpd PROP1} `{BiFUpd PROP2} :={embed_fupd :
                                    forall E1 E2 P,
                                    \226\142\161 |={E1,E2}=> P \226\142\164
                                    \226\138\163\226\138\162@{ PROP2} (|={E1,E2}=> \226\142\161 P \226\142\164)}.
Time Hint Mode BiEmbedFUpd - ! - - -: typeclass_instances.
Time Hint Mode BiEmbedFUpd ! - - - -: typeclass_instances.
Time
Class BiEmbedPlainly (PROP1 PROP2 : sbi) `{BiEmbed PROP1 PROP2}
`{BiPlainly PROP1} `{BiPlainly PROP2} :={embed_plainly_2 :
                                          forall P : PROP1,
                                          \226\150\160 \226\142\161 P \226\142\164 \226\138\162 \226\142\161 \226\150\160 P \226\142\164 : PROP2}.
Time Hint Mode BiEmbedPlainly - ! - - -: typeclass_instances.
Time Hint Mode BiEmbedPlainly ! - - - -: typeclass_instances.
Time Section embed_laws.
Time Context `{BiEmbed PROP1 PROP2}.
Time #[local]Notation embed := (embed (A:=PROP1) (B:=PROP2)).
Time #[local]Notation "\226\142\161 P \226\142\164" := (embed P) : bi_scope.
Time Implicit Type P : PROP1.
Time #[global]Instance embed_ne : (NonExpansive embed).
Time Proof.
Time (eapply bi_embed_mixin_ne, bi_embed_mixin).
Time Qed.
Time #[global]Instance embed_mono : (Proper ((\226\138\162) ==> (\226\138\162)) embed).
Time Proof.
Time (eapply bi_embed_mixin_mono, bi_embed_mixin).
Time Qed.
Time Lemma embed_emp_valid_inj P : (\226\142\161 P \226\142\164 : PROP2)%I \226\134\146 P.
Time Proof.
Time (eapply bi_embed_mixin_emp_valid_inj, bi_embed_mixin).
Time Qed.
Time Lemma embed_emp_2 : emp \226\138\162 \226\142\161 emp \226\142\164.
Time Proof.
Time (eapply bi_embed_mixin_emp_2, bi_embed_mixin).
Time Qed.
Time Lemma embed_impl_2 P Q : (\226\142\161 P \226\142\164 \226\134\146 \226\142\161 Q \226\142\164) \226\138\162 \226\142\161 P \226\134\146 Q \226\142\164.
Time Proof.
Time (eapply bi_embed_mixin_impl_2, bi_embed_mixin).
Time Qed.
Time Lemma embed_forall_2 A (\206\166 : A \226\134\146 PROP1) : (\226\136\128 x, \226\142\161 \206\166 x \226\142\164) \226\138\162 \226\142\161 \226\136\128 x, \206\166 x \226\142\164.
Time Proof.
Time (eapply bi_embed_mixin_forall_2, bi_embed_mixin).
Time Qed.
Time Lemma embed_exist_1 A (\206\166 : A \226\134\146 PROP1) : \226\142\161 \226\136\131 x, \206\166 x \226\142\164 \226\138\162 \226\136\131 x, \226\142\161 \206\166 x \226\142\164.
Time Proof.
Time (eapply bi_embed_mixin_exist_1, bi_embed_mixin).
Time Qed.
Time Lemma embed_sep P Q : \226\142\161 P \226\136\151 Q \226\142\164 \226\138\163\226\138\162 \226\142\161 P \226\142\164 \226\136\151 \226\142\161 Q \226\142\164.
Time Proof.
Time (eapply bi_embed_mixin_sep, bi_embed_mixin).
Time Qed.
Time Lemma embed_wand_2 P Q : (\226\142\161 P \226\142\164 -\226\136\151 \226\142\161 Q \226\142\164) \226\138\162 \226\142\161 P -\226\136\151 Q \226\142\164.
Time Proof.
Time (eapply bi_embed_mixin_wand_2, bi_embed_mixin).
Time Qed.
Time Lemma embed_persistently P : \226\142\161 <pers> P \226\142\164 \226\138\163\226\138\162 <pers> \226\142\161 P \226\142\164.
Time Proof.
Time (eapply bi_embed_mixin_persistently, bi_embed_mixin).
Time Qed.
Time End embed_laws.
Time Section embed.
Time Context `{BiEmbed PROP1 PROP2}.
Time #[local]Notation embed := (embed (A:=PROP1) (B:=PROP2)).
Time #[local]Notation "\226\142\161 P \226\142\164" := (embed P) : bi_scope.
Time Implicit Types P Q R : PROP1.
Time #[global]Instance embed_proper : (Proper ((\226\137\161) ==> (\226\137\161)) embed).
Time Proof.
Time (apply (ne_proper _)).
Time Qed.
Time #[global]
Instance embed_flip_mono : (Proper (flip (\226\138\162) ==> flip (\226\138\162)) embed).
Time Proof.
Time solve_proper.
Time Import uPred_primitive.
Time Definition uPred_emp {M} : uPred M := uPred_pure True.
Time #[local]Existing Instance entails_po.
Time
Lemma uPred_bi_mixin (M : ucmraT) :
  BiMixin uPred_entails uPred_emp uPred_pure uPred_and uPred_or uPred_impl
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_wand
    uPred_persistently.
Time Proof.
Time split.
Time -
Time exact : {}entails_po {}.
Time -
Time exact : {}equiv_spec {}.
Time -
Time exact : {}pure_ne {}.
Time -
Time exact : {}and_ne {}.
Time -
Time exact : {}or_ne {}.
Time -
Time exact : {}impl_ne {}.
Time -
Time exact : {}forall_ne {}.
Time -
Time exact : {}exist_ne {}.
Time -
Time exact : {}sep_ne {}.
Time -
Time exact : {}wand_ne {}.
Time -
Time exact : {}persistently_ne {}.
Time -
Time exact : {}pure_intro {}.
Time -
Time exact : {}pure_elim' {}.
Time -
Time exact : {}@pure_forall_2 {}.
Time -
Time exact : {}and_elim_l {}.
Time -
Time exact : {}and_elim_r {}.
Time -
Time exact : {}and_intro {}.
Time -
Time exact : {}or_intro_l {}.
Time -
Time exact : {}or_intro_r {}.
Time -
Time exact : {}or_elim {}.
Time -
Time exact : {}impl_intro_r {}.
Time -
Time exact : {}impl_elim_l' {}.
Time -
Time exact : {}@forall_intro {}.
Time -
Time exact : {}@forall_elim {}.
Time -
Time exact : {}@exist_intro {}.
Time -
Time exact : {}@exist_elim {}.
Time -
Time exact : {}sep_mono {}.
Time -
Time exact : {}True_sep_1 {}.
Time -
Time exact : {}True_sep_2 {}.
Time -
Time exact : {}sep_comm' {}.
Time -
Time exact : {}sep_assoc' {}.
Time -
Time exact : {}wand_intro_r {}.
Time -
Time exact : {}wand_elim_l' {}.
Time -
Time exact : {}persistently_mono {}.
Time -
Time exact : {}persistently_idemp_2 {}.
Time -
Time trans uPred_forall (M:=M) (\206\187 _ : False, uPred_persistently uPred_emp).
Time +
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>[[]]).
Time +
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; first  exact
 : {}persistently_forall_2 {}).
Time (apply persistently_mono).
Time exact : {}pure_intro {}.
Time -
Time exact : {}@persistently_forall_2 {}.
Time -
Time exact : {}@persistently_exist_1 {}.
Time -
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; first  exact : {}sep_comm' {}).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; last  exact : {}True_sep_2 {}).
Time (<ssreflect_plugin::ssrtclseq@0> apply sep_mono ; last  done).
Time Qed.
Time #[global]Instance embed_entails_inj : (Inj (\226\138\162) (\226\138\162) embed).
Time Proof.
Time move  {}=>P Q /bi.entails_wand.
Time rewrite embed_wand_2.
Time exact : {}pure_intro {}.
Time -
Time exact : {}persistently_and_sep_l_1 {}.
Time Qed.
Time
Lemma uPred_sbi_mixin (M : ucmraT) :
  SbiMixin uPred_entails uPred_pure uPred_or uPred_impl 
    (@uPred_forall M) (@uPred_exist M) uPred_sep uPred_persistently
    (@uPred_internal_eq M) uPred_later.
Time Proof.
Time split.
Time -
Time exact : {}later_contractive {}.
Time -
Time exact : {}internal_eq_ne {}.
Time by move  {}=>/embed_emp_valid_inj/bi.wand_entails.
Time Qed.
Time #[global]Instance embed_inj : (Inj (\226\137\161) (\226\137\161) embed).
Time Proof.
Time (intros P Q EQ).
Time (apply bi.equiv_spec, conj; apply (inj embed); rewrite EQ //).
Time -
Time exact : {}@internal_eq_refl {}.
Time -
Time exact : {}@internal_eq_rewrite {}.
Time -
Time exact : {}@fun_ext {}.
Time -
Time exact : {}@sig_eq {}.
Time -
Time exact : {}@discrete_eq_1 {}.
Time -
Time exact : {}@later_eq_1 {}.
Time -
Time exact : {}@later_eq_2 {}.
Time -
Time exact : {}later_mono {}.
Time -
Time exact : {}later_intro {}.
Time -
Time exact : {}@later_forall_2 {}.
Time -
Time exact : {}@later_exist_false {}.
Time -
Time exact : {}later_sep_1 {}.
Time -
Time exact : {}later_sep_2 {}.
Time -
Time exact : {}later_persistently_1 {}.
Time -
Time exact : {}later_persistently_2 {}.
Time -
Time exact : {}later_false_em {}.
Time Qed.
Time
Canonical Structure uPredI (M : ucmraT) : bi :=
  {|
  bi_ofe_mixin := ofe_mixin_of (uPred M);
  bi_bi_mixin := uPred_bi_mixin M |}.
Time
Canonical Structure uPredSI (M : ucmraT) : sbi :=
  {|
  sbi_ofe_mixin := ofe_mixin_of (uPred M);
  sbi_bi_mixin := uPred_bi_mixin M;
  sbi_sbi_mixin := uPred_sbi_mixin M |}.
Time Coercion uPred_valid {M} : uPred M \226\134\146 Prop := bi_emp_valid.
Time Lemma uPred_plainly_mixin M : BiPlainlyMixin (uPredSI M) uPred_plainly.
Time Proof.
Time split.
Time -
Time exact : {}plainly_ne {}.
Time -
Time exact : {}plainly_mono {}.
Time -
Time exact : {}plainly_elim_persistently {}.
Time -
Time exact : {}plainly_idemp_2 {}.
Time -
Time exact : {}@plainly_forall_2 {}.
Time -
Time exact : {}persistently_impl_plainly {}.
Time -
Time exact : {}plainly_impl_plainly {}.
Time -
Time (intros P).
Time trans uPred_forall (M:=M) (\206\187 _ : False, uPred_plainly uPred_emp).
Time +
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>[[]]).
Time +
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; first  exact : {}plainly_forall_2
 {}).
Time (apply plainly_mono).
Time exact : {}pure_intro {}.
Time -
Time (intros P Q).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; last  exact : {}True_sep_2 {}).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; first  exact : {}sep_comm' {}).
Time (<ssreflect_plugin::ssrtclseq@0> apply sep_mono ; last  done).
Time exact : {}pure_intro {}.
Time -
Time exact : {}prop_ext_2 {}.
Time -
Time exact : {}later_plainly_1 {}.
Time -
Time exact : {}later_plainly_2 {}.
Time Qed.
Time Qed.
Time Lemma embed_emp_valid (P : PROP1) : \226\142\161 P \226\142\164%I \226\134\148 P.
Time #[global]
Instance uPred_plainlyC  M: (BiPlainly (uPredSI M)) :=
 {| bi_plainly_mixin := uPred_plainly_mixin M |}.
Time Lemma uPred_bupd_mixin M : BiBUpdMixin (uPredI M) uPred_bupd.
Time Proof.
Time split.
Time -
Time exact : {}bupd_ne {}.
Time -
Time exact : {}bupd_intro {}.
Time -
Time exact : {}bupd_mono {}.
Time -
Time exact : {}bupd_trans {}.
Time -
Time exact : {}bupd_frame_r {}.
Time Qed.
Time Proof.
Time rewrite /bi_emp_valid.
Time (<ssreflect_plugin::ssrtclintros@0> split =>HP).
Time -
Time by apply embed_emp_valid_inj.
Time -
Time by rewrite embed_emp_2 HP.
Time #[global]
Instance uPred_bi_bupd  M: (BiBUpd (uPredI M)) :=
 {| bi_bupd_mixin := uPred_bupd_mixin M |}.
Time #[global]Instance uPred_bi_bupd_plainly  M: (BiBUpdPlainly (uPredSI M)).
Time Proof.
Time exact : {}bupd_plainly {}.
Time Qed.
Time #[global]Instance uPred_affine  M: (BiAffine (uPredI M)) |0.
Time Proof.
Time (intros P).
Time exact : {}pure_intro {}.
Time Qed.
Time Hint Immediate uPred_affine: core.
Time #[global]
Instance uPred_plainly_exist_1  M: (BiPlainlyExist (uPredSI M)).
Time Proof.
Time exact : {}@plainly_exist_1 {}.
Time Qed.
Time Module uPred.
Time Section restate.
Time Context {M : ucmraT}.
Time Implicit Type \207\134 : Prop.
Time Implicit Types P Q : uPred M.
Time Implicit Type A : Type.
Time Notation "P \226\138\162 Q" := (bi_entails (PROP:=uPredI M) P%I Q%I).
Time Notation "P \226\138\163\226\138\162 Q" := (equiv (A:=uPredI M) P%I Q%I).
Time #[global]
Instance ownM_ne : (NonExpansive (@uPred_ownM M)) := uPred_primitive.ownM_ne.
Time #[global]
Instance cmra_valid_ne  {A : cmraT}: (NonExpansive (@uPred_cmra_valid M A))
 := uPred_primitive.cmra_valid_ne.
Time
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 \226\139\133 a2) \226\138\163\226\138\162 uPred_ownM a1 \226\136\151 uPred_ownM a2.
Time Proof.
Time exact : {}uPred_primitive.ownM_op {}.
Time Qed.
Time
Lemma persistently_ownM_core (a : M) :
  uPred_ownM a \226\138\162 <pers> uPred_ownM (core a).
Time Proof.
Time exact : {}uPred_primitive.persistently_ownM_core {}.
Time Qed.
Time Lemma ownM_unit P : P \226\138\162 uPred_ownM \206\181.
Time Proof.
Time exact : {}uPred_primitive.ownM_unit {}.
Time Qed.
Time Lemma later_ownM a : \226\150\183 uPred_ownM a \226\138\162 \226\136\131 b, uPred_ownM b \226\136\167 \226\150\183 (a \226\137\161 b).
Time Qed.
Time Lemma embed_emp `{!BiEmbedEmp PROP1 PROP2} : \226\142\161 emp \226\142\164 \226\138\163\226\138\162 emp.
Time Proof.
Time (apply (anti_symm _); eauto using embed_emp_1, embed_emp_2).
Time Qed.
Time Proof.
Time exact : {}uPred_primitive.later_ownM {}.
Time Qed.
Time
Lemma bupd_ownM_updateP x (\206\166 : M \226\134\146 Prop) :
  x ~~>: \206\166 \226\134\146 uPred_ownM x \226\138\162 |==> \226\136\131 y, \226\140\156\206\166 y\226\140\157 \226\136\167 uPred_ownM y.
Time Proof.
Time exact : {}uPred_primitive.bupd_ownM_updateP {}.
Time Qed.
Time Lemma ownM_valid (a : M) : uPred_ownM a \226\138\162 \226\156\147 a.
Time Proof.
Time exact : {}uPred_primitive.ownM_valid {}.
Time Qed.
Time Lemma cmra_valid_intro {A : cmraT} P (a : A) : \226\156\147 a \226\134\146 P \226\138\162 \226\156\147 a.
Time Proof.
Time exact : {}uPred_primitive.cmra_valid_intro {}.
Time Qed.
Time Lemma cmra_valid_elim {A : cmraT} (a : A) : \194\172 \226\156\147{0} a \226\134\146 \226\156\147 a \226\138\162 False.
Time Proof.
Time exact : {}uPred_primitive.cmra_valid_elim {}.
Time Qed.
Time Lemma embed_forall A (\206\166 : A \226\134\146 PROP1) : \226\142\161 \226\136\128 x, \206\166 x \226\142\164 \226\138\163\226\138\162 (\226\136\128 x, \226\142\161 \206\166 x \226\142\164).
Time Proof.
Time (apply bi.equiv_spec; split; [  | apply embed_forall_2 ]).
Time (<ssreflect_plugin::ssrtclintros@0> apply bi.forall_intro =>?).
Time by rewrite bi.forall_elim.
Time Lemma plainly_cmra_valid_1 {A : cmraT} (a : A) : \226\156\147 a \226\138\162 \226\150\160 \226\156\147 a.
Time Proof.
Time exact : {}uPred_primitive.plainly_cmra_valid_1 {}.
Time Qed.
Time Lemma cmra_valid_weaken {A : cmraT} (a b : A) : \226\156\147 (a \226\139\133 b) \226\138\162 \226\156\147 a.
Time Proof.
Time exact : {}uPred_primitive.cmra_valid_weaken {}.
Time Qed.
Time Lemma prod_validI {A B : cmraT} (x : A * B) : \226\156\147 x \226\138\163\226\138\162 \226\156\147 x.1 \226\136\167 \226\156\147 x.2.
Time Proof.
Time exact : {}uPred_primitive.prod_validI {}.
Time Qed.
Time
Lemma option_validI {A : cmraT} (mx : option A) :
  \226\156\147 mx \226\138\163\226\138\162 match mx with
          | Some x => \226\156\147 x
          | None => True : uPred M
          end.
Time Proof.
Time exact : {}uPred_primitive.option_validI {}.
Time Qed.
Time
Lemma discrete_valid {A : cmraT} `{!CmraDiscrete A} (a : A) : \226\156\147 a \226\138\163\226\138\162 \226\140\156\226\156\147 a\226\140\157.
Time Qed.
Time Proof.
Time exact : {}uPred_primitive.discrete_valid {}.
Time Qed.
Time
Lemma discrete_fun_validI {A} {B : A \226\134\146 ucmraT} (g : discrete_fun B) :
  \226\156\147 g \226\138\163\226\138\162 (\226\136\128 i, \226\156\147 g i).
Time Proof.
Time exact : {}uPred_primitive.discrete_fun_validI {}.
Time Qed.
Time Lemma pure_soundness \207\134 : bi_emp_valid (PROP:=uPredI M) \226\140\156\207\134\226\140\157 \226\134\146 \207\134.
Time Proof.
Time (apply pure_soundness).
Time Qed.
Time Lemma later_soundness P : bi_emp_valid (\226\150\183 P) \226\134\146 bi_emp_valid P.
Time Proof.
Time (apply later_soundness).
Time Qed.
Time End restate.
Time Lemma embed_exist A (\206\166 : A \226\134\146 PROP1) : \226\142\161 \226\136\131 x, \206\166 x \226\142\164 \226\138\163\226\138\162 (\226\136\131 x, \226\142\161 \206\166 x \226\142\164).
Time Proof.
Time (apply bi.equiv_spec; split; [ apply embed_exist_1 |  ]).
Time (<ssreflect_plugin::ssrtclintros@0> apply bi.exist_elim =>?).
Time by rewrite -bi.exist_intro.
Time
Ltac
 unseal :=
  unfold bi_emp; simpl; unfold sbi_emp; simpl;
   unfold uPred_emp, bupd, bi_bupd_bupd, bi_pure, bi_and, bi_or, bi_impl,
    bi_forall, bi_exist, bi_sep, bi_wand, bi_persistently, sbi_internal_eq,
    sbi_later; simpl;
   unfold sbi_emp, sbi_pure, sbi_and, sbi_or, sbi_impl, sbi_forall,
    sbi_exist, sbi_internal_eq, sbi_sep, sbi_wand, sbi_persistently; 
   simpl; unfold plainly, bi_plainly_plainly; simpl; uPred_primitive.unseal.
Time End uPred.
Time Qed.
Time Lemma embed_and P Q : \226\142\161 P \226\136\167 Q \226\142\164 \226\138\163\226\138\162 \226\142\161 P \226\142\164 \226\136\167 \226\142\161 Q \226\142\164.
Time Proof.
Time rewrite !bi.and_alt embed_forall.
Time by <ssreflect_plugin::ssrtclintros@0> f_equiv =>- [].
Time Qed.
Time Lemma embed_or P Q : \226\142\161 P \226\136\168 Q \226\142\164 \226\138\163\226\138\162 \226\142\161 P \226\142\164 \226\136\168 \226\142\161 Q \226\142\164.
Time Proof.
Time rewrite !bi.or_alt embed_exist.
Time by <ssreflect_plugin::ssrtclintros@0> f_equiv =>- [].
Time Qed.
Time Lemma embed_impl P Q : \226\142\161 P \226\134\146 Q \226\142\164 \226\138\163\226\138\162 (\226\142\161 P \226\142\164 \226\134\146 \226\142\161 Q \226\142\164).
Time Proof.
Time (apply bi.equiv_spec; split; [  | apply embed_impl_2 ]).
Time (apply bi.impl_intro_l).
Time by rewrite -embed_and bi.impl_elim_r.
Time Qed.
Time Lemma embed_wand P Q : \226\142\161 P -\226\136\151 Q \226\142\164 \226\138\163\226\138\162 (\226\142\161 P \226\142\164 -\226\136\151 \226\142\161 Q \226\142\164).
Time Proof.
Time (apply bi.equiv_spec; split; [  | apply embed_wand_2 ]).
Time (apply bi.wand_intro_l).
Time by rewrite -embed_sep bi.wand_elim_r.
Time Qed.
Time Lemma embed_pure \207\134 : \226\142\161 \226\140\156\207\134\226\140\157 \226\142\164 \226\138\163\226\138\162 \226\140\156\207\134\226\140\157.
Time Proof.
Time rewrite (@bi.pure_alt PROP1) (@bi.pure_alt PROP2) embed_exist.
Time (do 2 f_equiv).
Time (apply bi.equiv_spec).
Time (split; [ apply bi.True_intro |  ]).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -(_ : (emp \226\134\146 emp : PROP1) \226\138\162 True)
 ?embed_impl ; last  apply bi.True_intro).
Time (apply bi.impl_intro_l).
Time by rewrite right_id.
Time Qed.
Time Lemma embed_iff P Q : \226\142\161 P \226\134\148 Q \226\142\164 \226\138\163\226\138\162 (\226\142\161 P \226\142\164 \226\134\148 \226\142\161 Q \226\142\164).
Time Proof.
Time by rewrite embed_and !embed_impl.
Time Qed.
Time Lemma embed_wand_iff P Q : \226\142\161 P \226\136\151-\226\136\151 Q \226\142\164 \226\138\163\226\138\162 (\226\142\161 P \226\142\164 \226\136\151-\226\136\151 \226\142\161 Q \226\142\164).
Time Proof.
Time by rewrite embed_and !embed_wand.
Time Qed.
Time Lemma embed_affinely_2 P : <affine> \226\142\161 P \226\142\164 \226\138\162 \226\142\161 <affine> P \226\142\164.
Time Proof.
Time by rewrite embed_and -embed_emp_2.
Time Qed.
Time
Lemma embed_affinely `{!BiEmbedEmp PROP1 PROP2} P :
  \226\142\161 <affine> P \226\142\164 \226\138\163\226\138\162 <affine> \226\142\161 P \226\142\164.
Time Proof.
Time by rewrite /bi_intuitionistically embed_and embed_emp.
Time Qed.
Time Lemma embed_absorbingly P : \226\142\161 <absorb> P \226\142\164 \226\138\163\226\138\162 <absorb> \226\142\161 P \226\142\164.
Time Proof.
Time by rewrite embed_sep embed_pure.
Time Qed.
Time Lemma embed_intuitionistically_2 P : \226\150\161 \226\142\161 P \226\142\164 \226\138\162 \226\142\161 \226\150\161 P \226\142\164.
Time Proof.
Time by rewrite /bi_intuitionistically -embed_affinely_2 embed_persistently.
Time Qed.
Time
Lemma embed_intuitionistically `{!BiEmbedEmp PROP1 PROP2} 
  P : \226\142\161 \226\150\161 P \226\142\164 \226\138\163\226\138\162 \226\150\161 \226\142\161 P \226\142\164.
Time Proof.
Time by rewrite /bi_intuitionistically embed_affinely embed_persistently.
Time Qed.
Time Lemma embed_persistently_if P b : \226\142\161 <pers>?b P \226\142\164 \226\138\163\226\138\162 <pers>?b \226\142\161 P \226\142\164.
Time Proof.
Time (destruct b; simpl; auto using embed_persistently).
Time Qed.
Time Lemma embed_affinely_if_2 P b : <affine>?b \226\142\161 P \226\142\164 \226\138\162 \226\142\161 <affine>?b P \226\142\164.
Time Proof.
Time (destruct b; simpl; auto using embed_affinely_2).
Time Qed.
Time
Lemma embed_affinely_if `{!BiEmbedEmp PROP1 PROP2} 
  P b : \226\142\161 <affine>?b P \226\142\164 \226\138\163\226\138\162 <affine>?b \226\142\161 P \226\142\164.
Time Proof.
Time (destruct b; simpl; auto using embed_affinely).
Time Qed.
Time Lemma embed_absorbingly_if b P : \226\142\161 <absorb>?b P \226\142\164 \226\138\163\226\138\162 <absorb>?b \226\142\161 P \226\142\164.
Time Proof.
Time (destruct b; simpl; auto using embed_absorbingly).
Time Qed.
Time Lemma embed_intuitionistically_if_2 P b : \226\150\161?b \226\142\161 P \226\142\164 \226\138\162 \226\142\161 \226\150\161?b P \226\142\164.
Time Proof.
Time (destruct b; simpl; auto using embed_intuitionistically_2).
Time Qed.
Time
Lemma embed_intuitionistically_if `{!BiEmbedEmp PROP1 PROP2} 
  P b : \226\142\161 \226\150\161?b P \226\142\164 \226\138\163\226\138\162 \226\150\161?b \226\142\161 P \226\142\164.
Time Proof.
Time (destruct b; simpl; auto using embed_intuitionistically).
Time Qed.
Time #[global]
Instance embed_persistent  P: (Persistent P \226\134\146 Persistent \226\142\161 P \226\142\164).
Time Proof.
Time (intros ?).
Time by rewrite /Persistent -embed_persistently -persistent.
Time Qed.
Time #[global]
Instance embed_affine  `{!BiEmbedEmp PROP1 PROP2} 
 P: (Affine P \226\134\146 Affine \226\142\161 P \226\142\164).
Time Proof.
Time (intros ?).
Time by rewrite /Affine (affine P) embed_emp.
Time Qed.
Time #[global]Instance embed_absorbing  P: (Absorbing P \226\134\146 Absorbing \226\142\161 P \226\142\164).
Time Proof.
Time (intros ?).
Time by rewrite /Absorbing -embed_absorbingly absorbing.
Time Qed.
Time #[global]
Instance embed_and_homomorphism :
 (MonoidHomomorphism bi_and bi_and (\226\137\161) embed).
Time Proof.
Time
by
 split; [ split |  ]; try apply _;
  [ setoid_rewrite embed_and | rewrite embed_pure ].
Time Qed.
Time #[global]
Instance embed_or_homomorphism : (MonoidHomomorphism bi_or bi_or (\226\137\161) embed).
Time Proof.
Time
by
 split; [ split |  ]; try apply _;
  [ setoid_rewrite embed_or | rewrite embed_pure ].
Time Qed.
Time #[global]
Instance embed_sep_entails_homomorphism :
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) embed).
Time Proof.
Time
(split; [ split |  ]; simpl; try apply _;
  [ by setoid_rewrite embed_sep | by rewrite embed_emp_2 ]).
Time Qed.
Time
Lemma embed_big_sepL_2 {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP1) l :
  ([\226\136\151 list] k\226\134\166x \226\136\136 l, \226\142\161 \206\166 k x \226\142\164) \226\138\162 \226\142\161 [\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x \226\142\164.
Time Proof.
Time (apply (big_opL_commute (R:=flip (\226\138\162)) _)).
Time Qed.
Time
Lemma embed_big_sepM_2 `{Countable K} {A} (\206\166 : K \226\134\146 A \226\134\146 PROP1) 
  (m : gmap K A) : ([\226\136\151 map] k\226\134\166x \226\136\136 m, \226\142\161 \206\166 k x \226\142\164) \226\138\162 \226\142\161 [\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x \226\142\164.
Time Proof.
Time (apply (big_opM_commute (R:=flip (\226\138\162)) _)).
Time Qed.
Time
Lemma embed_big_sepS_2 `{Countable A} (\206\166 : A \226\134\146 PROP1) 
  (X : gset A) : ([\226\136\151 set] y \226\136\136 X, \226\142\161 \206\166 y \226\142\164) \226\138\162 \226\142\161 [\226\136\151 set] y \226\136\136 X, \206\166 y \226\142\164.
Time Proof.
Time (apply (big_opS_commute (R:=flip (\226\138\162)) _)).
Time Qed.
Time
Lemma embed_big_sepMS_2 `{Countable A} (\206\166 : A \226\134\146 PROP1) 
  (X : gmultiset A) : ([\226\136\151 mset] y \226\136\136 X, \226\142\161 \206\166 y \226\142\164) \226\138\162 \226\142\161 [\226\136\151 mset] y \226\136\136 X, \206\166 y \226\142\164.
Time Proof.
Time (apply (big_opMS_commute (R:=flip (\226\138\162)) _)).
Time Qed.
Time Section big_ops_emp.
Time Context `{!BiEmbedEmp PROP1 PROP2}.
Time #[global]
Instance embed_sep_homomorphism :
 (MonoidHomomorphism bi_sep bi_sep (\226\137\161) embed).
Time Proof.
Time
by
 split; [ split |  ]; try apply _;
  [ setoid_rewrite embed_sep | rewrite embed_emp ].
Time Qed.
Time
Lemma embed_big_sepL {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP1) l :
  \226\142\161 [\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x \226\142\164 \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \226\142\161 \206\166 k x \226\142\164).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma embed_big_sepM `{Countable K} {A} (\206\166 : K \226\134\146 A \226\134\146 PROP1) 
  (m : gmap K A) : \226\142\161 [\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x \226\142\164 \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \226\142\161 \206\166 k x \226\142\164).
Time Proof.
Time (apply (big_opM_commute _)).
Time Qed.
Time
Lemma embed_big_sepS `{Countable A} (\206\166 : A \226\134\146 PROP1) 
  (X : gset A) : \226\142\161 [\226\136\151 set] y \226\136\136 X, \206\166 y \226\142\164 \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, \226\142\161 \206\166 y \226\142\164).
Time Proof.
Time (apply (big_opS_commute _)).
Time Qed.
Time
Lemma embed_big_sepMS `{Countable A} (\206\166 : A \226\134\146 PROP1) 
  (X : gmultiset A) : \226\142\161 [\226\136\151 mset] y \226\136\136 X, \206\166 y \226\142\164 \226\138\163\226\138\162 ([\226\136\151 mset] y \226\136\136 X, \226\142\161 \206\166 y \226\142\164).
Time Proof.
Time (apply (big_opMS_commute _)).
Time Qed.
Time End big_ops_emp.
Time End embed.
Time Section sbi_embed.
Time Context `{SbiEmbed PROP1 PROP2}.
Time Implicit Types P Q R : PROP1.
Time Lemma embed_internal_eq (A : ofeT) (x y : A) : \226\142\161 x \226\137\161 y \226\142\164 \226\138\163\226\138\162 x \226\137\161 y.
Time Proof.
Time (apply bi.equiv_spec; split; [ apply embed_internal_eq_1 |  ]).
Time
(etrans;
  [ apply (bi.internal_eq_rewrite x y (\206\187 y, \226\142\161 x \226\137\161 y \226\142\164%I)); solve_proper |  ]).
Time rewrite -(bi.internal_eq_refl True%I) embed_pure.
Time (eapply bi.impl_elim; [ done |  ]).
Time (apply bi.True_intro).
Time Qed.
Time Lemma embed_laterN n P : \226\142\161 \226\150\183^n P \226\142\164 \226\138\163\226\138\162 \226\150\183^n \226\142\161 P \226\142\164.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> induction n =>//=).
Time rewrite embed_later.
Time by f_equiv.
Time Qed.
Time Lemma embed_except_0 P : \226\142\161 \226\151\135 P \226\142\164 \226\138\163\226\138\162 \226\151\135 \226\142\161 P \226\142\164.
Time Proof.
Time by rewrite embed_or embed_later embed_pure.
Time Qed.
Time
Lemma bi_embed_plainly_emp `{!BiPlainly PROP1} `{!BiPlainly PROP2} :
  BiEmbedEmp PROP1 PROP2 \226\134\146 BiEmbedPlainly PROP1 PROP2.
Time Proof.
Time (intros).
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>P).
Time rewrite !plainly_alt embed_internal_eq.
Time by rewrite -embed_affinely -embed_emp embed_interal_inj.
Time Qed.
Time
Lemma embed_plainly_1 `{!BiPlainly PROP1} `{!BiPlainly PROP2} 
  P : \226\142\161 \226\150\160 P \226\142\164 \226\138\162 \226\150\160 \226\142\161 P \226\142\164.
Time Proof.
Time
(assert (Hhelp : \226\136\128 P, <affine> \226\142\161 P \226\142\164 \226\138\163\226\138\162 (<affine> \226\142\161 <affine> P \226\142\164 : PROP2))).
Time {
Time (intros P').
Time (apply (anti_symm _)).
Time -
Time by rewrite -bi.affinely_idemp (embed_affinely_2 P').
Time -
Time by rewrite (bi.affinely_elim P').
Time }
Time (assert (Hemp : <affine> \226\142\161 emp \226\142\164 \226\138\163\226\138\162 (emp : PROP2))).
Time {
Time (apply (anti_symm _)).
Time -
Time (apply bi.affinely_elim_emp).
Time -
Time (apply bi.and_intro; auto using embed_emp_2).
Time }
Time rewrite !plainly_alt embed_internal_eq.
Time by rewrite Hhelp -Hemp -!bi.f_equiv.
Time Qed.
Time
Lemma embed_plainly `{!BiPlainly PROP1} `{!BiPlainly PROP2}
  `{!BiEmbedPlainly PROP1 PROP2} P : \226\142\161 \226\150\160 P \226\142\164 \226\138\163\226\138\162 \226\150\160 \226\142\161 P \226\142\164.
Time Proof.
Time (apply (anti_symm _)).
Time by apply embed_plainly_1.
Time by apply embed_plainly_2.
Time Qed.
Time
Lemma embed_plainly_if `{!BiPlainly PROP1} `{!BiPlainly PROP2}
  `{!BiEmbedPlainly PROP1 PROP2} p P : \226\142\161 \226\150\160?p P \226\142\164 \226\138\163\226\138\162 \226\150\160?p \226\142\161 P \226\142\164.
Time Proof.
Time (destruct p; simpl; auto using embed_plainly).
Time Qed.
Time
Lemma embed_plainly_if_1 `{!BiPlainly PROP1} `{!BiPlainly PROP2} 
  p P : \226\142\161 \226\150\160?p P \226\142\164 \226\138\162 \226\150\160?p \226\142\161 P \226\142\164.
Time Proof.
Time (destruct p; simpl; auto using embed_plainly_1).
Time Qed.
Time
Lemma embed_plain `{!BiPlainly PROP1} `{!BiPlainly PROP2} 
  (P : PROP1) : Plain P \226\134\146 Plain (PROP:=PROP2) \226\142\161 P \226\142\164.
Time Proof.
Time (intros ?).
Time by rewrite /Plain {+1}(plain P) embed_plainly_1.
Time Qed.
Time #[global]Instance embed_timeless  P: (Timeless P \226\134\146 Timeless \226\142\161 P \226\142\164).
Time Proof.
Time (intros ?).
Time by rewrite /Timeless -embed_except_0 -embed_later timeless.
Time Qed.
Time End sbi_embed.
Time
Hint Extern 4 (Plain \226\142\161 _ \226\142\164) => (eapply @embed_plain): typeclass_instances.
