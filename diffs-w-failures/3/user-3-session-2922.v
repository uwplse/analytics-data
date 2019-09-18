Time From iris.bi Require Export derived_connectives updates plainly.
Time From iris.base_logic Require Export upred.
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
Time exact : {}prop_ext {}.
Time -
Time exact : {}later_plainly_1 {}.
Time -
Time exact : {}later_plainly_2 {}.
Time Qed.
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
Time Proof.
Time exact : {}uPred_primitive.discrete_valid {}.
Time Qed.
Time
Lemma ofe_fun_validI {A} {B : A \226\134\146 ucmraT} (g : ofe_fun B) :
  \226\156\147 g \226\138\163\226\138\162 (\226\136\128 i, \226\156\147 g i).
Time Proof.
Time exact : {}uPred_primitive.ofe_fun_validI {}.
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
