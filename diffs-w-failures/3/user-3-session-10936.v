Time From stdpp Require Export telescopes.
Time From iris.base_logic Require Export bi.
Time From iris.bi Require Export bi.
Time Set Default Proof Using "Type*".
Time Import bi.
Time
Definition bi_texist {PROP : bi} {TT : tele} (\206\168 : TT \226\134\146 PROP) : PROP :=
  tele_fold (@bi_exist PROP) (\206\187 x, x) (tele_bind \206\168).
Time Arguments bi_texist {_} {!_} _ /.
Time
Definition bi_tforall {PROP : bi} {TT : tele} (\206\168 : TT \226\134\146 PROP) : PROP :=
  tele_fold (@bi_forall PROP) (\206\187 x, x) (tele_bind \206\168).
Time Arguments bi_tforall {_} {!_} _ /.
Time
Notation "'\226\136\131..' x .. y , P" :=
  (bi_texist (\206\187 x, .. (bi_texist (\206\187 y, P)) ..)%I)
  (at level 200, x binder, y binder, right associativity,
   format "\226\136\131..  x  ..  y ,  P") : bi_scope.
Time
Notation "'\226\136\128..' x .. y , P" :=
  (bi_tforall (\206\187 x, .. (bi_tforall (\206\187 y, P)) ..)%I)
  (at level 200, x binder, y binder, right associativity,
   format "\226\136\128..  x  ..  y ,  P") : bi_scope.
Time Section telescope_quantifiers.
Time Context {PROP : bi} {TT : tele}.
Time Lemma bi_tforall_forall (\206\168 : TT \226\134\146 PROP) : bi_tforall \206\168 \226\138\163\226\138\162 bi_forall \206\168.
Time Proof.
Time symmetry.
Time (unfold bi_tforall).
Time (induction TT as [| X ft IH]).
Time -
Time (simpl).
Time (apply (anti_symm _)).
Time +
Time by rewrite (forall_elim TargO).
Time +
Time (<ssreflect_plugin::ssrtclseq@0> rewrite -forall_intro ; first  done).
Time (intros p).
Time rewrite (tele_arg_O_inv p) /= //.
Time -
Time (simpl).
Time (apply (anti_symm _); apply forall_intro; intros a).
Time +
Time rewrite /= -IH.
Time (apply forall_intro; intros p).
Time by rewrite (forall_elim (TargS a p)).
Time From iris.bi Require Export bi.
Time +
Time move /tele_arg_inv: {}a {} =>[x [pf {+}->]] {a} /=.
Time setoid_rewrite  <- IH.
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
Time rewrite 2!forall_elim.
Time Qed.
Time #[global]
Instance uPred_valid_mono : (Proper ((\226\138\162) ==> impl) (@uPred_valid M)).
Time Proof.
Time solve_proper.
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
Time done.
Time
Lemma persistently_cmra_valid_1 {A : cmraT} (a : A) :
  \226\156\147 a \226\138\162 <pers> (\226\156\147 a : uPred M).
Time Proof.
Time by rewrite {+1}plainly_cmra_valid_1 plainly_elim_persistently.
Time Qed.
Time Lemma bi_texist_exist (\206\168 : TT \226\134\146 PROP) : bi_texist \206\168 \226\138\163\226\138\162 bi_exist \206\168.
Time Proof.
Time symmetry.
Time (unfold bi_texist).
Time (induction TT as [| X ft IH]).
Time -
Time (simpl).
Time (apply (anti_symm _)).
Time +
Time (apply exist_elim; intros p).
Time rewrite (tele_arg_O_inv p) //.
Time +
Time by rewrite -(exist_intro TargO).
Time -
Time (simpl).
Time (apply (anti_symm _); apply exist_elim).
Time +
Time (intros p).
Time move /tele_arg_inv: {}p {} =>[x [pf {+}->]] {p} /=.
Time by rewrite -exist_intro -IH -exist_intro.
Time Qed.
Time
Lemma intuitionistically_ownM (a : M) :
  CoreId a \226\134\146 \226\150\161 uPred_ownM a \226\138\163\226\138\162 uPred_ownM a.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /bi_intuitionistically
  affine_affinely =>?; apply (anti_symm _);
  [ by rewrite persistently_elim |  ]).
Time +
Time (intros x).
Time rewrite /= -IH.
Time by rewrite {+1}persistently_ownM_core core_id_core.
Time (apply exist_elim; intros p).
Time by rewrite -(exist_intro (TargS x p)).
Time Qed.
Time #[global]
Instance bi_tforall_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_tforall PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_tforall_forall.
Time rewrite EQ //.
Time Qed.
Time Lemma ownM_invalid (a : M) : \194\172 \226\156\147{0} a \226\134\146 uPred_ownM a \226\138\162 False.
Time Proof.
Time by intros; rewrite ownM_valid cmra_valid_elim.
Time Qed.
Time #[global]
Instance bi_tforall_proper :
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_tforall PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_tforall_forall.
Time rewrite EQ //.
Time Qed.
Time #[global]
Instance ownM_mono : (Proper (flip (\226\137\188) ==> (\226\138\162)) (@uPred_ownM M)).
Time Proof.
Time (intros a b [b' ->]).
Time Qed.
Time #[global]
Instance bi_texist_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_texist PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_texist_exist.
Time by rewrite ownM_op sep_elim_l.
Time rewrite EQ //.
Time Qed.
Time Qed.
Time Lemma ownM_unit' : uPred_ownM \206\181 \226\138\163\226\138\162 True.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm _) ; first  by
 apply pure_intro).
Time #[global]
Instance bi_texist_proper :
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_texist PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_texist_exist.
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
Time rewrite EQ //.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; apply (anti_symm _) ; first  by
 rewrite persistently_elim).
Time Qed.
Time End telescope_quantifiers.
Time apply : {}persistently_cmra_valid_1 {}.
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
Time #[global]
Instance valid_timeless  {A : cmraT} `{!CmraDiscrete A} 
 (a : A): (Timeless (\226\156\147 a : uPred M)%I).
Time Proof.
Time rewrite /Timeless !discrete_valid.
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
