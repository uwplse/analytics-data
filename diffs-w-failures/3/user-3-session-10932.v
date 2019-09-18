Time From iris.bi Require Import derived_laws_sbi big_op.
Time From iris.algebra Require Import monoid.
Time Import interface.bi derived_laws_bi.bi derived_laws_sbi.bi.
Time Class Plainly (A : Type) :=
         plainly : A \226\134\146 A.
Time Hint Mode Plainly !: typeclass_instances.
Time Instance: (Params (@plainly) 2) := { }.
Time Notation "\226\150\160 P" := (plainly P) : bi_scope.
Time
Record BiPlainlyMixin (PROP : sbi) `(Plainly PROP) :={
 bi_plainly_mixin_plainly_ne : NonExpansive (plainly (A:=PROP));
 bi_plainly_mixin_plainly_mono : forall P Q : PROP, (P \226\138\162 Q) \226\134\146 \226\150\160 P \226\138\162 \226\150\160 Q;
 bi_plainly_mixin_plainly_elim_persistently : forall P : PROP, \226\150\160 P \226\138\162 <pers> P;
 bi_plainly_mixin_plainly_idemp_2 : forall P : PROP, \226\150\160 P \226\138\162 \226\150\160 \226\150\160 P;
 bi_plainly_mixin_plainly_forall_2 :
  forall {A} (\206\168 : A \226\134\146 PROP), (\226\136\128 a, \226\150\160 \206\168 a) \226\138\162 \226\150\160 (\226\136\128 a, \206\168 a);
 bi_plainly_mixin_persistently_impl_plainly :
  forall P Q : PROP, (\226\150\160 P \226\134\146 <pers> Q) \226\138\162 <pers> (\226\150\160 P \226\134\146 Q);
 bi_plainly_mixin_plainly_impl_plainly :
  forall P Q : PROP, (\226\150\160 P \226\134\146 \226\150\160 Q) \226\138\162 \226\150\160 (\226\150\160 P \226\134\146 Q);
 bi_plainly_mixin_plainly_emp_intro : forall P : PROP, P \226\138\162 \226\150\160 emp;
 bi_plainly_mixin_plainly_absorb : forall P Q : PROP, \226\150\160 P \226\136\151 Q \226\138\162 \226\150\160 P;
 bi_plainly_mixin_prop_ext_2 :
  forall P Q : PROP, \226\150\160 ((P -\226\136\151 Q) \226\136\167 (Q -\226\136\151 P)) \226\138\162 P \226\137\161 Q;
 bi_plainly_mixin_later_plainly_1 : forall P : PROP, \226\150\183 \226\150\160 P \226\138\162 \226\150\160 \226\150\183 P;
 bi_plainly_mixin_later_plainly_2 : forall P : PROP, \226\150\160 \226\150\183 P \226\138\162 \226\150\183 \226\150\160 P}.
Time
Class BiPlainly (PROP : sbi) :={bi_plainly_plainly :> Plainly PROP;
                                bi_plainly_mixin :
                                 BiPlainlyMixin PROP bi_plainly_plainly}.
Time Hint Mode BiPlainly !: typeclass_instances.
Time Arguments bi_plainly_plainly : simpl never.
Time
Class BiPlainlyExist `{!BiPlainly PROP} :=
    plainly_exist_1 : forall A (\206\168 : A \226\134\146 PROP), \226\150\160 (\226\136\131 a, \206\168 a) \226\138\162 \226\136\131 a, \226\150\160 \206\168 a.
Time Arguments BiPlainlyExist : clear implicits.
Time Arguments BiPlainlyExist _ {_}.
Time Arguments plainly_exist_1 _ {_} {_} _.
Time Hint Mode BiPlainlyExist ! -: typeclass_instances.
Time Section plainly_laws.
Time Context `{BiPlainly PROP}.
Time Implicit Types P Q : PROP.
Time #[global]Instance plainly_ne : (NonExpansive (@plainly PROP _)).
Time Proof.
Time (eapply bi_plainly_mixin_plainly_ne, bi_plainly_mixin).
Time Qed.
Time Lemma plainly_mono P Q : (P \226\138\162 Q) \226\134\146 \226\150\160 P \226\138\162 \226\150\160 Q.
Time Proof.
Time (eapply bi_plainly_mixin_plainly_mono, bi_plainly_mixin).
Time Qed.
Time Lemma plainly_elim_persistently P : \226\150\160 P \226\138\162 <pers> P.
Time Proof.
Time (eapply bi_plainly_mixin_plainly_elim_persistently, bi_plainly_mixin).
Time Qed.
Time Lemma plainly_idemp_2 P : \226\150\160 P \226\138\162 \226\150\160 \226\150\160 P.
Time Proof.
Time (eapply bi_plainly_mixin_plainly_idemp_2, bi_plainly_mixin).
Time Qed.
Time Lemma plainly_forall_2 {A} (\206\168 : A \226\134\146 PROP) : (\226\136\128 a, \226\150\160 \206\168 a) \226\138\162 \226\150\160 (\226\136\128 a, \206\168 a).
Time Proof.
Time (eapply bi_plainly_mixin_plainly_forall_2, bi_plainly_mixin).
Time Qed.
Time
Lemma persistently_impl_plainly P Q : (\226\150\160 P \226\134\146 <pers> Q) \226\138\162 <pers> (\226\150\160 P \226\134\146 Q).
Time Proof.
Time (eapply bi_plainly_mixin_persistently_impl_plainly, bi_plainly_mixin).
Time Qed.
Time Lemma plainly_impl_plainly P Q : (\226\150\160 P \226\134\146 \226\150\160 Q) \226\138\162 \226\150\160 (\226\150\160 P \226\134\146 Q).
Time Proof.
Time (eapply bi_plainly_mixin_plainly_impl_plainly, bi_plainly_mixin).
Time Qed.
Time Lemma plainly_absorb P Q : \226\150\160 P \226\136\151 Q \226\138\162 \226\150\160 P.
Time Proof.
Time (eapply bi_plainly_mixin_plainly_absorb, bi_plainly_mixin).
Time Qed.
Time Lemma plainly_emp_intro P : P \226\138\162 \226\150\160 emp.
Time Proof.
Time (eapply bi_plainly_mixin_plainly_emp_intro, bi_plainly_mixin).
Time Qed.
Time Lemma prop_ext_2 P Q : \226\150\160 ((P -\226\136\151 Q) \226\136\167 (Q -\226\136\151 P)) \226\138\162 P \226\137\161 Q.
Time Proof.
Time (eapply bi_plainly_mixin_prop_ext_2, bi_plainly_mixin).
Time Qed.
Time Lemma later_plainly_1 P : \226\150\183 \226\150\160 P \226\138\162 \226\150\160 \226\150\183 P.
Time Proof.
Time (eapply bi_plainly_mixin_later_plainly_1, bi_plainly_mixin).
Time Qed.
Time Lemma later_plainly_2 P : \226\150\160 \226\150\183 P \226\138\162 \226\150\183 \226\150\160 P.
Time Proof.
Time (eapply bi_plainly_mixin_later_plainly_2, bi_plainly_mixin).
Time Qed.
Time End plainly_laws.
Time Class Plain `{BiPlainly PROP} (P : PROP) :=
         plain : P \226\138\162 \226\150\160 P.
Time Arguments Plain {_} {_} _%I : simpl never.
Time Arguments plain {_} {_} _%I {_}.
Time Hint Mode Plain + - !: typeclass_instances.
Time Instance: (Params (@Plain) 1) := { }.
Time
Definition plainly_if `{!BiPlainly PROP} (p : bool) 
  (P : PROP) : PROP := (if p then \226\150\160 P else P)%I.
Time Arguments plainly_if {_} {_} !_ _%I /.
Time Instance: (Params (@plainly_if) 2) := { }.
Time Typeclasses Opaque plainly_if.
Time Notation "\226\150\160? p P" := (plainly_if p P) : bi_scope.
Time Section plainly_derived.
Time Context `{BiPlainly PROP}.
Time Implicit Type P : PROP.
Time Hint Resolve pure_intro forall_intro: core.
Time Hint Resolve or_elim or_intro_l' or_intro_r': core.
Time Hint Resolve and_intro and_elim_l' and_elim_r': core.
Time #[global]
Instance plainly_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@plainly PROP _)) :=
 (ne_proper _).
Time #[global]
Instance plainly_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) (@plainly PROP _)).
Time Proof.
Time (intros P Q; apply plainly_mono).
Time Qed.
Time #[global]
Instance plainly_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@plainly PROP _)).
Time Proof.
Time (intros P Q; apply plainly_mono).
Time Qed.
Time Lemma affinely_plainly_elim P : <affine> \226\150\160 P \226\138\162 P.
Time Proof.
Time
by rewrite plainly_elim_persistently /bi_affinely persistently_and_emp_elim.
Time Qed.
Time Lemma persistently_elim_plainly P : <pers> \226\150\160 P \226\138\163\226\138\162 \226\150\160 P.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time
by rewrite persistently_into_absorbingly /bi_absorbingly comm plainly_absorb.
Time -
Time by rewrite {+1}plainly_idemp_2 plainly_elim_persistently.
Time Qed.
Time Lemma persistently_if_elim_plainly P p : <pers>?p \226\150\160 P \226\138\163\226\138\162 \226\150\160 P.
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> destruct p ; last  done).
Time exact : {}persistently_elim_plainly {}.
Time Qed.
Time Lemma plainly_persistently_elim P : \226\150\160 <pers> P \226\138\163\226\138\162 \226\150\160 P.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time rewrite -{+1}(left_id True%I bi_and (\226\150\160 _)%I) (plainly_emp_intro True%I).
Time rewrite -{+2}(persistently_and_emp_elim P).
Time rewrite !and_alt -plainly_forall_2.
Time by <ssreflect_plugin::ssrtclintros@0> apply forall_mono =>- [].
Time -
Time by rewrite {+1}plainly_idemp_2 (plainly_elim_persistently P).
Time Qed.
Time Lemma absorbingly_elim_plainly P : <absorb> \226\150\160 P \226\138\163\226\138\162 \226\150\160 P.
Time Proof.
Time by rewrite -(persistently_elim_plainly P) absorbingly_elim_persistently.
Time Qed.
Time Lemma plainly_and_sep_elim P Q : \226\150\160 P \226\136\167 Q -\226\136\151 (emp \226\136\167 P) \226\136\151 Q.
Time Proof.
Time by rewrite plainly_elim_persistently persistently_and_sep_elim_emp.
Time Qed.
Time Lemma plainly_and_sep_assoc P Q R : \226\150\160 P \226\136\167 Q \226\136\151 R \226\138\163\226\138\162 (\226\150\160 P \226\136\167 Q) \226\136\151 R.
Time Proof.
Time by rewrite -(persistently_elim_plainly P) persistently_and_sep_assoc.
Time Qed.
Time Lemma plainly_and_emp_elim P : emp \226\136\167 \226\150\160 P \226\138\162 P.
Time Proof.
Time by rewrite plainly_elim_persistently persistently_and_emp_elim.
Time Qed.
Time Lemma plainly_into_absorbingly P : \226\150\160 P \226\138\162 <absorb> P.
Time Proof.
Time by rewrite plainly_elim_persistently persistently_into_absorbingly.
Time Qed.
Time Lemma plainly_elim P `{!Absorbing P} : \226\150\160 P \226\138\162 P.
Time Proof.
Time by rewrite plainly_elim_persistently persistently_elim.
Time Qed.
Time Lemma plainly_idemp_1 P : \226\150\160 \226\150\160 P \226\138\162 \226\150\160 P.
Time Proof.
Time by rewrite plainly_into_absorbingly absorbingly_elim_plainly.
Time Qed.
Time Lemma plainly_idemp P : \226\150\160 \226\150\160 P \226\138\163\226\138\162 \226\150\160 P.
Time Proof.
Time (apply (anti_symm _); auto using plainly_idemp_1, plainly_idemp_2).
Time Qed.
Time Lemma plainly_intro' P Q : (\226\150\160 P \226\138\162 Q) \226\134\146 \226\150\160 P \226\138\162 \226\150\160 Q.
Time Proof.
Time (intros <-).
Time (apply plainly_idemp_2).
Time Qed.
Time Lemma plainly_pure \207\134 : \226\150\160 \226\140\156\207\134\226\140\157 \226\138\163\226\138\162@{ PROP} \226\140\156\207\134\226\140\157.
Time Proof.
Time (apply (anti_symm _); auto).
Time -
Time by rewrite plainly_elim_persistently persistently_pure.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim' =>H\207\134).
Time (trans (\226\136\128 x : False, \226\150\160 True : PROP)%I; [ by apply forall_intro |  ]).
Time rewrite plainly_forall_2.
Time by rewrite -(pure_intro \207\134).
Time Qed.
Time Lemma plainly_forall {A} (\206\168 : A \226\134\146 PROP) : \226\150\160 (\226\136\128 a, \206\168 a) \226\138\163\226\138\162 (\226\136\128 a, \226\150\160 \206\168 a).
Time Proof.
Time (apply (anti_symm _); auto using plainly_forall_2).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (forall_elim x).
Time Qed.
Time Lemma plainly_exist_2 {A} (\206\168 : A \226\134\146 PROP) : (\226\136\131 a, \226\150\160 \206\168 a) \226\138\162 \226\150\160 (\226\136\131 a, \206\168 a).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>x).
Time by rewrite (exist_intro x).
Time Qed.
Time
Lemma plainly_exist `{!BiPlainlyExist PROP} {A} (\206\168 : A \226\134\146 PROP) :
  \226\150\160 (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, \226\150\160 \206\168 a).
Time Proof.
Time (apply (anti_symm _); auto using plainly_exist_1, plainly_exist_2).
Time Qed.
Time Lemma plainly_and P Q : \226\150\160 (P \226\136\167 Q) \226\138\163\226\138\162 \226\150\160 P \226\136\167 \226\150\160 Q.
Time Proof.
Time rewrite !and_alt plainly_forall.
Time by <ssreflect_plugin::ssrtclintros@0> apply forall_proper =>- [].
Time Qed.
Time Lemma plainly_or_2 P Q : \226\150\160 P \226\136\168 \226\150\160 Q \226\138\162 \226\150\160 (P \226\136\168 Q).
Time Proof.
Time rewrite !or_alt -plainly_exist_2.
Time by <ssreflect_plugin::ssrtclintros@0> apply exist_mono =>- [].
Time Qed.
Time Lemma plainly_or `{!BiPlainlyExist PROP} P Q : \226\150\160 (P \226\136\168 Q) \226\138\163\226\138\162 \226\150\160 P \226\136\168 \226\150\160 Q.
Time Proof.
Time rewrite !or_alt plainly_exist.
Time by <ssreflect_plugin::ssrtclintros@0> apply exist_proper =>- [].
Time Qed.
Time Lemma plainly_impl P Q : \226\150\160 (P \226\134\146 Q) \226\138\162 \226\150\160 P \226\134\146 \226\150\160 Q.
Time Proof.
Time (apply impl_intro_l; rewrite -plainly_and).
Time (apply plainly_mono, impl_elim with P; auto).
Time Qed.
Time Lemma plainly_emp_2 : emp \226\138\162@{ PROP} \226\150\160 emp.
Time Proof.
Time (apply plainly_emp_intro).
Time Qed.
Time Lemma plainly_sep_dup P : \226\150\160 P \226\138\163\226\138\162 \226\150\160 P \226\136\151 \226\150\160 P.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time rewrite -{+1}(idemp bi_and (\226\150\160 _)%I).
Time by rewrite -{+2}(emp_sep (\226\150\160 _)%I) plainly_and_sep_assoc and_elim_l.
Time -
Time by rewrite plainly_absorb.
Time Qed.
Time Lemma plainly_and_sep_l_1 P Q : \226\150\160 P \226\136\167 Q \226\138\162 \226\150\160 P \226\136\151 Q.
Time Proof.
Time by rewrite -{+1}(emp_sep Q%I) plainly_and_sep_assoc and_elim_l.
Time Qed.
Time Lemma plainly_and_sep_r_1 P Q : P \226\136\167 \226\150\160 Q \226\138\162 P \226\136\151 \226\150\160 Q.
Time Proof.
Time by rewrite !(comm _ P) plainly_and_sep_l_1.
Time Qed.
Time Lemma plainly_True_emp : \226\150\160 True \226\138\163\226\138\162@{ PROP} \226\150\160 emp.
Time Proof.
Time (apply (anti_symm _); eauto using plainly_mono, plainly_emp_intro).
Time Qed.
Time Lemma plainly_and_sep P Q : \226\150\160 (P \226\136\167 Q) \226\138\162 \226\150\160 (P \226\136\151 Q).
Time Proof.
Time rewrite plainly_and.
Time rewrite -{+1}plainly_idemp -plainly_and -{+1}(emp_sep Q%I).
Time by rewrite plainly_and_sep_assoc (comm bi_and) plainly_and_emp_elim.
Time Qed.
Time Lemma plainly_affinely_elim P : \226\150\160 <affine> P \226\138\163\226\138\162 \226\150\160 P.
Time Proof.
Time
by rewrite /bi_affinely plainly_and -plainly_True_emp plainly_pure left_id.
Time Qed.
Time Lemma intuitionistically_plainly_elim P : \226\150\161 \226\150\160 P -\226\136\151 \226\150\161 P.
Time Proof.
Time rewrite intuitionistically_affinely plainly_elim_persistently //.
Time Qed.
Time Lemma intuitionistically_plainly P : \226\150\161 \226\150\160 P -\226\136\151 \226\150\160 \226\150\161 P.
Time Proof.
Time rewrite /bi_intuitionistically plainly_affinely_elim affinely_elim.
Time rewrite persistently_elim_plainly plainly_persistently_elim.
Time done.
Time Qed.
Time Lemma and_sep_plainly P Q : \226\150\160 P \226\136\167 \226\150\160 Q \226\138\163\226\138\162 \226\150\160 P \226\136\151 \226\150\160 Q.
Time Proof.
Time (apply (anti_symm _); auto using plainly_and_sep_l_1).
Time (apply and_intro).
Time -
Time by rewrite plainly_absorb.
Time -
Time by rewrite comm plainly_absorb.
Time Qed.
Time Lemma plainly_sep_2 P Q : \226\150\160 P \226\136\151 \226\150\160 Q \226\138\162 \226\150\160 (P \226\136\151 Q).
Time Proof.
Time by rewrite -plainly_and_sep plainly_and -and_sep_plainly.
Time Qed.
Time Lemma plainly_sep `{BiPositive PROP} P Q : \226\150\160 (P \226\136\151 Q) \226\138\163\226\138\162 \226\150\160 P \226\136\151 \226\150\160 Q.
Time Proof.
Time (apply (anti_symm _); auto using plainly_sep_2).
Time
rewrite -(plainly_affinely_elim (_ \226\136\151 _)%I) affinely_sep -and_sep_plainly.
Time (apply and_intro).
Time -
Time by rewrite (affinely_elim_emp Q) right_id affinely_elim.
Time -
Time by rewrite (affinely_elim_emp P) left_id affinely_elim.
Time Qed.
Time Lemma plainly_wand P Q : \226\150\160 (P -\226\136\151 Q) \226\138\162 \226\150\160 P -\226\136\151 \226\150\160 Q.
Time Proof.
Time (apply wand_intro_r).
Time by rewrite plainly_sep_2 wand_elim_l.
Time Qed.
Time Lemma plainly_entails_l P Q : (P \226\138\162 \226\150\160 Q) \226\134\146 P \226\138\162 \226\150\160 Q \226\136\151 P.
Time Proof.
Time (intros; rewrite -plainly_and_sep_l_1; auto).
Time Qed.
Time Lemma plainly_entails_r P Q : (P \226\138\162 \226\150\160 Q) \226\134\146 P \226\138\162 P \226\136\151 \226\150\160 Q.
Time Proof.
Time (intros; rewrite -plainly_and_sep_r_1; auto).
Time Qed.
Time Lemma plainly_impl_wand_2 P Q : \226\150\160 (P -\226\136\151 Q) \226\138\162 \226\150\160 (P \226\134\146 Q).
Time Proof.
Time (apply plainly_intro', impl_intro_r).
Time rewrite -{+2}(emp_sep P%I) plainly_and_sep_assoc.
Time by rewrite (comm bi_and) plainly_and_emp_elim wand_elim_l.
Time Qed.
Time Lemma impl_wand_plainly_2 P Q : (\226\150\160 P -\226\136\151 Q) \226\138\162 \226\150\160 P \226\134\146 Q.
Time Proof.
Time (apply impl_intro_l).
Time by rewrite plainly_and_sep_l_1 wand_elim_r.
Time Qed.
Time Lemma impl_wand_affinely_plainly P Q : (\226\150\160 P \226\134\146 Q) \226\138\163\226\138\162 (<affine> \226\150\160 P -\226\136\151 Q).
Time Proof.
Time by rewrite -(persistently_elim_plainly P) impl_wand_intuitionistically.
Time Qed.
Time
Lemma persistently_wand_affinely_plainly P Q :
  (<affine> \226\150\160 P -\226\136\151 <pers> Q) \226\138\162 <pers> (<affine> \226\150\160 P -\226\136\151 Q).
Time Proof.
Time rewrite -!impl_wand_affinely_plainly.
Time (apply persistently_impl_plainly).
Time Qed.
Time
Lemma plainly_wand_affinely_plainly P Q :
  (<affine> \226\150\160 P -\226\136\151 \226\150\160 Q) \226\138\162 \226\150\160 (<affine> \226\150\160 P -\226\136\151 Q).
Time Proof.
Time rewrite -!impl_wand_affinely_plainly.
Time (apply plainly_impl_plainly).
Time Qed.
Time Section plainly_affine_bi.
Time Context `{BiAffine PROP}.
Time Lemma plainly_emp : \226\150\160 emp \226\138\163\226\138\162@{ PROP} emp.
Time Proof.
Time by rewrite -!True_emp plainly_pure.
Time Qed.
Time Lemma plainly_and_sep_l P Q : \226\150\160 P \226\136\167 Q \226\138\163\226\138\162 \226\150\160 P \226\136\151 Q.
Time Proof.
Time
(apply (anti_symm (\226\138\162)); eauto using plainly_and_sep_l_1, sep_and
  with typeclass_instances).
Time Qed.
Time Lemma plainly_and_sep_r P Q : P \226\136\167 \226\150\160 Q \226\138\163\226\138\162 P \226\136\151 \226\150\160 Q.
Time Proof.
Time by rewrite !(comm _ P) plainly_and_sep_l.
Time Qed.
Time Lemma plainly_impl_wand P Q : \226\150\160 (P \226\134\146 Q) \226\138\163\226\138\162 \226\150\160 (P -\226\136\151 Q).
Time Proof.
Time (apply (anti_symm (\226\138\162)); auto using plainly_impl_wand_2).
Time (apply plainly_intro', wand_intro_l).
Time by rewrite -plainly_and_sep_r plainly_elim impl_elim_r.
Time Qed.
Time Lemma impl_wand_plainly P Q : (\226\150\160 P \226\134\146 Q) \226\138\163\226\138\162 (\226\150\160 P -\226\136\151 Q).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time by rewrite -impl_wand_1.
Time by rewrite impl_wand_plainly_2.
Time Qed.
Time End plainly_affine_bi.
Time #[global]
Instance plainly_if_ne  p: (NonExpansive (@plainly_if PROP _ p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance plainly_if_proper  p:
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@plainly_if PROP _ p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance plainly_if_mono'  p: (Proper ((\226\138\162) ==> (\226\138\162)) (@plainly_if PROP _ p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance plainly_if_flip_mono'  p:
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@plainly_if PROP _ p)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma plainly_if_mono p P Q : (P \226\138\162 Q) \226\134\146 \226\150\160?p P \226\138\162 \226\150\160?p Q.
Time Proof.
Time by intros ->.
Time Qed.
Time Lemma plainly_if_pure p \207\134 : \226\150\160?p \226\140\156\207\134\226\140\157 \226\138\163\226\138\162@{ PROP} \226\140\156\207\134\226\140\157.
Time Proof.
Time (destruct p; simpl; auto using plainly_pure).
Time Qed.
Time Lemma plainly_if_and p P Q : \226\150\160?p (P \226\136\167 Q) \226\138\163\226\138\162 \226\150\160?p P \226\136\167 \226\150\160?p Q.
Time Proof.
Time (destruct p; simpl; auto using plainly_and).
Time Qed.
Time Lemma plainly_if_or_2 p P Q : \226\150\160?p P \226\136\168 \226\150\160?p Q \226\138\162 \226\150\160?p (P \226\136\168 Q).
Time Proof.
Time (destruct p; simpl; auto using plainly_or_2).
Time Qed.
Time
Lemma plainly_if_or `{!BiPlainlyExist PROP} p P Q :
  \226\150\160?p (P \226\136\168 Q) \226\138\163\226\138\162 \226\150\160?p P \226\136\168 \226\150\160?p Q.
Time Proof.
Time (destruct p; simpl; auto using plainly_or).
Time Qed.
Time
Lemma plainly_if_exist_2 {A} p (\206\168 : A \226\134\146 PROP) :
  (\226\136\131 a, \226\150\160?p \206\168 a) \226\138\162 \226\150\160?p (\226\136\131 a, \206\168 a).
Time Proof.
Time (destruct p; simpl; auto using plainly_exist_2).
Time Qed.
Time
Lemma plainly_if_exist `{!BiPlainlyExist PROP} {A} 
  p (\206\168 : A \226\134\146 PROP) : \226\150\160?p (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, \226\150\160?p \206\168 a).
Time Proof.
Time (destruct p; simpl; auto using plainly_exist).
Time Qed.
Time
Lemma plainly_if_sep_2 `{!BiPositive PROP} p P Q :
  \226\150\160?p P \226\136\151 \226\150\160?p Q \226\138\162 \226\150\160?p (P \226\136\151 Q).
Time Proof.
Time (destruct p; simpl; auto using plainly_sep_2).
Time Qed.
Time Lemma plainly_if_idemp p P : \226\150\160?p \226\150\160?p P \226\138\163\226\138\162 \226\150\160?p P.
Time Proof.
Time (destruct p; simpl; auto using plainly_idemp).
Time Qed.
Time #[global]Instance Plain_proper : (Proper ((\226\137\161) ==> iff) (@Plain PROP _)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma plain_plainly_2 P `{!Plain P} : P \226\138\162 \226\150\160 P.
Time Proof.
Time done.
Time Qed.
Time Lemma plain_plainly P `{!Plain P} `{!Absorbing P} : \226\150\160 P \226\138\163\226\138\162 P.
Time Proof.
Time (apply (anti_symm _), plain_plainly_2, _).
Time by apply plainly_elim.
Time Qed.
Time Lemma plainly_intro P Q `{!Plain P} : (P \226\138\162 Q) \226\134\146 P \226\138\162 \226\150\160 Q.
Time Proof.
Time by intros <-.
Time Qed.
Time #[global]Instance plainly_absorbing  P: (Absorbing (\226\150\160 P)).
Time Proof.
Time by rewrite /Absorbing /bi_absorbingly comm plainly_absorb.
Time Qed.
Time #[global]
Instance plainly_if_absorbing  P p:
 (Absorbing P \226\134\146 Absorbing (plainly_if p P)).
Time Proof.
Time (intros; destruct p; simpl; apply _).
Time Qed.
Time Lemma plain_persistent P : Plain P \226\134\146 Persistent P.
Time Proof.
Time (intros).
Time by rewrite /Persistent -plainly_elim_persistently.
Time Qed.
Time
Lemma impl_persistent P Q :
  Absorbing P \226\134\146 Plain P \226\134\146 Persistent Q \226\134\146 Persistent (P \226\134\146 Q).
Time Proof.
Time (intros).
Time
by rewrite /Persistent {+2}(plain P) -persistently_impl_plainly
 -(persistent Q) (plainly_into_absorbingly P) absorbing.
Time Qed.
Time #[global]Instance plainly_persistent  P: (Persistent (\226\150\160 P)).
Time Proof.
Time by rewrite /Persistent persistently_elim_plainly.
Time Qed.
Time #[global]
Instance wand_persistent  P Q:
 (Plain P \226\134\146 Persistent Q \226\134\146 Absorbing Q \226\134\146 Persistent (P -\226\136\151 Q)).
Time Proof.
Time (intros).
Time rewrite /Persistent {+2}(plain P).
Time trans (<pers> (\226\150\160 P \226\134\146 Q))%I.
Time -
Time
rewrite -persistently_impl_plainly impl_wand_affinely_plainly -(persistent Q).
Time by rewrite affinely_plainly_elim.
Time -
Time (apply persistently_mono, wand_intro_l).
Time by rewrite sep_and impl_elim_r.
Time Qed.
Time #[global]
Instance limit_preserving_Plain  {A : ofeT} `{Cofe A} 
 (\206\166 : A \226\134\146 PROP): (NonExpansive \206\166 \226\134\146 LimitPreserving (\206\187 x, Plain (\206\166 x))).
Time Proof.
Time (intros).
Time (apply limit_preserving_entails; solve_proper).
Time Qed.
Time #[global]
Instance plainly_sep_weak_homomorphism  `{!BiPositive PROP}
 `{!BiAffine PROP}:
 (WeakMonoidHomomorphism bi_sep bi_sep (\226\137\161) (@plainly PROP _)).
Time Proof.
Time (split; try apply _).
Time (apply plainly_sep).
Time Qed.
Time #[global]
Instance plainly_sep_entails_weak_homomorphism :
 (WeakMonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@plainly PROP _)).
Time Proof.
Time (split; try apply _).
Time (intros P Q; by rewrite plainly_sep_2).
Time Qed.
Time #[global]
Instance plainly_sep_entails_homomorphism  `{!BiAffine PROP}:
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@plainly PROP _)).
Time Proof.
Time split.
Time (apply _).
Time (simpl).
Time rewrite plainly_emp.
Time done.
Time Qed.
Time #[global]
Instance plainly_sep_homomorphism  `{BiAffine PROP}:
 (MonoidHomomorphism bi_sep bi_sep (\226\137\161) (@plainly PROP _)).
Time Proof.
Time split.
Time (apply _).
Time (apply plainly_emp).
Time Qed.
Time #[global]
Instance plainly_and_homomorphism :
 (MonoidHomomorphism bi_and bi_and (\226\137\161) (@plainly PROP _)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply plainly_and).
Time (apply plainly_pure).
Time Qed.
Time #[global]
Instance plainly_or_homomorphism  `{!BiPlainlyExist PROP}:
 (MonoidHomomorphism bi_or bi_or (\226\137\161) (@plainly PROP _)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply plainly_or).
Time (apply plainly_pure).
Time Qed.
Time
Lemma big_sepL_plainly `{!BiAffine PROP} {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
  l : \226\150\160 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166x \226\136\136 l, \226\150\160 \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_andL_plainly {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) l :
  \226\150\160 ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\167 list] k\226\134\166x \226\136\136 l, \226\150\160 \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_orL_plainly `{!BiPlainlyExist PROP} {A} 
  (\206\166 : nat \226\134\146 A \226\134\146 PROP) l :
  \226\150\160 ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x) \226\138\163\226\138\162 ([\226\136\168 list] k\226\134\166x \226\136\136 l, \226\150\160 \206\166 k x).
Time Proof.
Time (apply (big_opL_commute _)).
Time Qed.
Time
Lemma big_sepL2_plainly `{!BiAffine PROP} {A} {B} 
  (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) l1 l2 :
  \226\150\160 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
  \226\138\163\226\138\162 ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \226\150\160 \206\166 k y1 y2).
Time Proof.
Time by rewrite !big_sepL2_alt plainly_and plainly_pure big_sepL_plainly.
Time Qed.
Time
Lemma big_sepM_plainly `{BiAffine PROP} `{Countable K} 
  {A} (\206\166 : K \226\134\146 A \226\134\146 PROP) m :
  \226\150\160 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \226\150\160 \206\166 k x).
Time Proof.
Time (apply (big_opM_commute _)).
Time Qed.
Time
Lemma big_sepM2_plainly `{BiAffine PROP} `{Countable K} 
  {A} {B} (\206\166 : K \226\134\146 A \226\134\146 B \226\134\146 PROP) m1 m2 :
  \226\150\160 ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2)
  \226\138\163\226\138\162 ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \226\150\160 \206\166 k x1 x2).
Time Proof.
Time by rewrite /big_sepM2 plainly_and plainly_pure big_sepM_plainly.
Time Qed.
Time
Lemma big_sepS_plainly `{BiAffine PROP} `{Countable A} 
  (\206\166 : A \226\134\146 PROP) X : \226\150\160 ([\226\136\151 set] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 set] y \226\136\136 X, \226\150\160 \206\166 y).
Time Proof.
Time (apply (big_opS_commute _)).
Time Qed.
Time
Lemma big_sepMS_plainly `{BiAffine PROP} `{Countable A} 
  (\206\166 : A \226\134\146 PROP) X : \226\150\160 ([\226\136\151 mset] y \226\136\136 X, \206\166 y) \226\138\163\226\138\162 ([\226\136\151 mset] y \226\136\136 X, \226\150\160 \206\166 y).
Time Proof.
Time (apply (big_opMS_commute _)).
Time Qed.
Time #[global]Instance pure_plain  \207\134: (Plain (PROP:=PROP) \226\140\156\207\134\226\140\157).
Time Proof.
Time by rewrite /Plain plainly_pure.
Time Qed.
Time #[global]Instance emp_plain : (Plain (PROP:=PROP) emp).
Time Proof.
Time (apply plainly_emp_intro).
Time Qed.
Time #[global]Instance and_plain  P Q: (Plain P \226\134\146 Plain Q \226\134\146 Plain (P \226\136\167 Q)).
Time Proof.
Time (intros).
Time by rewrite /Plain plainly_and -!plain.
Time Qed.
Time #[global]Instance or_plain  P Q: (Plain P \226\134\146 Plain Q \226\134\146 Plain (P \226\136\168 Q)).
Time Proof.
Time (intros).
Time by rewrite /Plain -plainly_or_2 -!plain.
Time Qed.
Time #[global]
Instance forall_plain  {A} (\206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, Plain (\206\168 x)) \226\134\146 Plain (\226\136\128 x, \206\168 x)).
Time Proof.
Time (intros).
Time rewrite /Plain plainly_forall.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>x).
Time by rewrite -plain.
Time Qed.
Time #[global]
Instance exist_plain  {A} (\206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, Plain (\206\168 x)) \226\134\146 Plain (\226\136\131 x, \206\168 x)).
Time Proof.
Time (intros).
Time rewrite /Plain -plainly_exist_2.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_mono =>x).
Time by rewrite -plain.
Time Qed.
Time #[global]
Instance impl_plain  P Q: (Absorbing P \226\134\146 Plain P \226\134\146 Plain Q \226\134\146 Plain (P \226\134\146 Q)).
Time Proof.
Time (intros).
Time
by rewrite /Plain {+2}(plain P) -plainly_impl_plainly -
 (plain Q) (plainly_into_absorbingly P) absorbing.
Time Qed.
Time #[global]
Instance wand_plain  P Q: (Plain P \226\134\146 Plain Q \226\134\146 Absorbing Q \226\134\146 Plain (P -\226\136\151 Q)).
Time Proof.
Time (intros).
Time rewrite /Plain {+2}(plain P).
Time trans (\226\150\160 (\226\150\160 P \226\134\146 Q))%I.
Time -
Time rewrite -plainly_impl_plainly impl_wand_affinely_plainly -(plain Q).
Time by rewrite affinely_plainly_elim.
Time -
Time (apply plainly_mono, wand_intro_l).
Time by rewrite sep_and impl_elim_r.
Time Qed.
Time #[global]Instance sep_plain  P Q: (Plain P \226\134\146 Plain Q \226\134\146 Plain (P \226\136\151 Q)).
Time Proof.
Time (intros).
Time by rewrite /Plain -plainly_sep_2 -!plain.
Time Qed.
Time #[global]Instance plainly_plain  P: (Plain (\226\150\160 P)).
Time Proof.
Time by rewrite /Plain plainly_idemp.
Time Qed.
Time #[global]Instance persistently_plain  P: (Plain P \226\134\146 Plain (<pers> P)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Plain =>HP).
Time rewrite {+1}HP plainly_persistently_elim persistently_elim_plainly //.
Time Qed.
Time #[global]Instance affinely_plain  P: (Plain P \226\134\146 Plain (<affine> P)).
Time Proof.
Time rewrite /bi_affinely.
Time (apply _).
Time Qed.
Time #[global]Instance intuitionistically_plain  P: (Plain P \226\134\146 Plain (\226\150\161 P)).
Time Proof.
Time rewrite /bi_intuitionistically.
Time (apply _).
Time Qed.
Time #[global]Instance absorbingly_plain  P: (Plain P \226\134\146 Plain (<absorb> P)).
Time Proof.
Time rewrite /bi_absorbingly.
Time (apply _).
Time Qed.
Time #[global]
Instance from_option_plain  {A} P (\206\168 : A \226\134\146 PROP) (mx : option A):
 ((\226\136\128 x, Plain (\206\168 x)) \226\134\146 Plain P \226\134\146 Plain (from_option \206\168 P mx)).
Time Proof.
Time (destruct mx; apply _).
Time Qed.
Time #[global]
Instance big_sepL_nil_plain  `{!BiAffine PROP} {A} 
 (\206\166 : nat \226\134\146 A \226\134\146 PROP): (Plain ([\226\136\151 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL_plain  `{!BiAffine PROP} {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l: ((\226\136\128 k x, Plain (\206\166 k x)) \226\134\146 Plain ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time #[global]
Instance big_andL_nil_plain  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP):
 (Plain ([\226\136\167 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_andL_plain  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) 
 l: ((\226\136\128 k x, Plain (\206\166 k x)) \226\134\146 Plain ([\226\136\167 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time #[global]
Instance big_orL_nil_plain  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP):
 (Plain ([\226\136\168 list] k\226\134\166x \226\136\136 [], \206\166 k x)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_orL_plain  {A} (\206\166 : nat \226\134\146 A \226\134\146 PROP) l:
 ((\226\136\128 k x, Plain (\206\166 k x)) \226\134\146 Plain ([\226\136\168 list] k\226\134\166x \226\136\136 l, \206\166 k x)).
Time Proof.
Time revert \206\166.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>\206\166 ? /=;
  apply _).
Time Qed.
Time #[global]
Instance big_sepL2_nil_plain  `{!BiAffine PROP} {A} 
 {B} (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP): (Plain ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 [];[], \206\166 k y1 y2)).
Time Proof.
Time (simpl; apply _).
Time Qed.
Time #[global]
Instance big_sepL2_plain  `{!BiAffine PROP} {A} {B} 
 (\206\166 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) l1 l2:
 ((\226\136\128 k x1 x2, Plain (\206\166 k x1 x2))
  \226\134\146 Plain ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)).
Time Proof.
Time rewrite big_sepL2_alt.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM_empty_plain  `{BiAffine PROP} `{Countable K} 
 {A} (\206\166 : K \226\134\146 A \226\134\146 PROP): (Plain ([\226\136\151 map] k\226\134\166x \226\136\136 \226\136\133, \206\166 k x)).
Time Proof.
Time rewrite /big_opM map_to_list_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM_plain  `{BiAffine PROP} `{Countable K} 
 {A} (\206\166 : K \226\134\146 A \226\134\146 PROP) m:
 ((\226\136\128 k x, Plain (\206\166 k x)) \226\134\146 Plain ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x)).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (big_sepL_plain _ _) =>_ 
  [? ?]; apply _).
Time Qed.
Time #[global]
Instance big_sepM2_empty_plain  `{BiAffine PROP} `{Countable K} 
 {A} {B} (\206\166 : K \226\134\146 A \226\134\146 B \226\134\146 PROP): (Plain ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 \226\136\133;\226\136\133, \206\166 k x1 x2)).
Time Proof.
Time rewrite /big_sepM2 map_zip_with_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepM2_plain  `{BiAffine PROP} `{Countable K} 
 {A} {B} (\206\166 : K \226\134\146 A \226\134\146 B \226\134\146 PROP) m1 m2:
 ((\226\136\128 k x1 x2, Plain (\206\166 k x1 x2)) \226\134\146 Plain ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2)).
Time Proof.
Time (intros).
Time rewrite /big_sepM2.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepS_empty_plain  `{BiAffine PROP} `{Countable A}
 (\206\166 : A \226\134\146 PROP): (Plain ([\226\136\151 set] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opS elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepS_plain  `{BiAffine PROP} `{Countable A} 
 (\206\166 : A \226\134\146 PROP) X: ((\226\136\128 x, Plain (\206\166 x)) \226\134\146 Plain ([\226\136\151 set] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opS.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepMS_empty_plain  `{BiAffine PROP} `{Countable A}
 (\206\166 : A \226\134\146 PROP): (Plain ([\226\136\151 mset] x \226\136\136 \226\136\133, \206\166 x)).
Time Proof.
Time rewrite /big_opMS gmultiset_elements_empty.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepMS_plain  `{BiAffine PROP} `{Countable A} 
 (\206\166 : A \226\134\146 PROP) X: ((\226\136\128 x, Plain (\206\166 x)) \226\134\146 Plain ([\226\136\151 mset] x \226\136\136 X, \206\166 x)).
Time Proof.
Time rewrite /big_opMS.
Time (apply _).
Time Qed.
Time
Lemma plainly_internal_eq {A : ofeT} (a b : A) : \226\150\160 (a \226\137\161 b) \226\138\163\226\138\162@{ PROP} a \226\137\161 b.
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time {
Time by rewrite plainly_elim.
Time }
Time
(apply (internal_eq_rewrite' a b (\206\187 b, \226\150\160 (a \226\137\161 b))%I);
  [ solve_proper | done |  ]).
Time (rewrite -(internal_eq_refl True%I a) plainly_pure; auto).
Time Qed.
Time Lemma prop_ext P Q : P \226\137\161 Q \226\138\163\226\138\162 \226\150\160 (P \226\136\151-\226\136\151 Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm (\226\138\162)) ; last  exact
 : {}prop_ext_2 {}).
Time
(apply (internal_eq_rewrite' P Q (\206\187 Q, \226\150\160 (P \226\136\151-\226\136\151 Q))%I);
  [ solve_proper | done |  ]).
Time rewrite (plainly_emp_intro (P \226\137\161 Q)%I).
Time (apply plainly_mono, wand_iff_refl).
Time Qed.
Time Lemma plainly_alt P : \226\150\160 P \226\138\163\226\138\162 <affine> P \226\137\161 emp.
Time Proof.
Time rewrite -plainly_affinely_elim.
Time (apply (anti_symm (\226\138\162))).
Time -
Time rewrite prop_ext.
Time (apply plainly_mono, and_intro; apply wand_intro_l).
Time +
Time by rewrite affinely_elim_emp left_id.
Time +
Time by rewrite left_id.
Time -
Time rewrite internal_eq_sym (internal_eq_rewrite _ _ plainly).
Time by rewrite -plainly_True_emp plainly_pure True_impl.
Time Qed.
Time Lemma plainly_alt_absorbing P `{!Absorbing P} : \226\150\160 P \226\138\163\226\138\162 P \226\137\161 True.
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time rewrite prop_ext.
Time (apply plainly_mono, and_intro; apply wand_intro_l; auto).
Time -
Time rewrite internal_eq_sym (internal_eq_rewrite _ _ plainly).
Time by rewrite plainly_pure True_impl.
Time Qed.
Time Lemma plainly_True_alt P : \226\150\160 (True -\226\136\151 P) \226\138\163\226\138\162 P \226\137\161 True.
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time rewrite prop_ext.
Time (apply plainly_mono, and_intro; apply wand_intro_l; auto).
Time by rewrite wand_elim_r.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite internal_eq_sym
 (internal_eq_rewrite _ _ (\206\187 Q, \226\150\160 (True -\226\136\151 Q))%I _) ; last  solve_proper).
Time by rewrite -entails_wand // -(plainly_emp_intro True%I) True_impl.
Time Qed.
Time Lemma later_plainly P : \226\150\183 \226\150\160 P \226\138\163\226\138\162 \226\150\160 \226\150\183 P.
Time Proof.
Time (apply (anti_symm _); auto using later_plainly_1, later_plainly_2).
Time Qed.
Time Lemma laterN_plainly n P : \226\150\183^n \226\150\160 P \226\138\163\226\138\162 \226\150\160 \226\150\183^n P.
Time Proof.
Time (induction n as [| n IH]; simpl; auto).
Time by rewrite IH later_plainly.
Time Qed.
Time Lemma later_plainly_if p P : \226\150\183 \226\150\160?p P \226\138\163\226\138\162 \226\150\160?p \226\150\183 P.
Time Proof.
Time (destruct p; simpl; auto using later_plainly).
Time Qed.
Time Lemma laterN_plainly_if n p P : \226\150\183^n \226\150\160?p P \226\138\163\226\138\162 \226\150\160?p \226\150\183^n P.
Time Proof.
Time (destruct p; simpl; auto using laterN_plainly).
Time Qed.
Time Lemma except_0_plainly_1 P : \226\151\135 \226\150\160 P \226\138\162 \226\150\160 \226\151\135 P.
Time Proof.
Time by rewrite /sbi_except_0 -plainly_or_2 -later_plainly plainly_pure.
Time Qed.
Time Lemma except_0_plainly `{!BiPlainlyExist PROP} P : \226\151\135 \226\150\160 P \226\138\163\226\138\162 \226\150\160 \226\151\135 P.
Time Proof.
Time by rewrite /sbi_except_0 plainly_or -later_plainly plainly_pure.
Time Qed.
Time #[global]
Instance internal_eq_plain  {A : ofeT} (a b : A):
 (Plain (PROP:=PROP) (a \226\137\161 b)).
Time Proof.
Time by intros; rewrite /Plain plainly_internal_eq.
Time Qed.
Time #[global]Instance later_plain  P: (Plain P \226\134\146 Plain (\226\150\183 P)).
Time Proof.
Time (intros).
Time by rewrite /Plain -later_plainly {+1}(plain P).
Time Qed.
Time #[global]Instance laterN_plain  n P: (Plain P \226\134\146 Plain (\226\150\183^n P)).
Time Proof.
Time (induction n; apply _).
Time Qed.
Time #[global]Instance except_0_plain  P: (Plain P \226\134\146 Plain (\226\151\135 P)).
Time Proof.
Time (rewrite /sbi_except_0; apply _).
Time Qed.
Time #[global]
Instance plainly_timeless  P `{!BiPlainlyExist PROP}:
 (Timeless P \226\134\146 Timeless (\226\150\160 P)).
Time Proof.
Time (intros).
Time rewrite /Timeless /sbi_except_0 later_plainly_1.
Time by rewrite (timeless P) /sbi_except_0 plainly_or {+1}plainly_elim.
Time Qed.
Time End plainly_derived.
Time Hint Immediate plain_persistent: typeclass_instances.
Time
Hint Extern 4 (Persistent (_ \226\134\146 _)) => (eapply @impl_persistent):
  typeclass_instances.
