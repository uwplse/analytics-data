Time From iris.bi Require Export derived_connectives.
Time From iris.algebra Require Import monoid.
Time Module bi.
Time Import interface.bi.
Time Section bi_derived.
Time Context {PROP : bi}.
Time Implicit Type \207\134 : Prop.
Time Implicit Types P Q R : PROP.
Time Implicit Type Ps : list PROP.
Time Implicit Type A : Type.
Time Hint Extern 100 (NonExpansive _) => solve_proper: core.
Time Notation "P \226\138\162 Q" := (P \226\138\162@{ PROP} Q).
Time Notation "P \226\138\163\226\138\162 Q" := (P \226\138\163\226\138\162@{ PROP} Q).
Time #[global]Instance entails_anti_sym : (AntiSymm (\226\138\163\226\138\162) (@bi_entails PROP)).
Time Proof.
Time (intros P Q ? ?).
Time by apply equiv_spec.
Time Qed.
Time Lemma equiv_entails P Q : P \226\138\163\226\138\162 Q \226\134\146 P \226\138\162 Q.
Time Proof.
Time (apply equiv_spec).
Time Qed.
Time Lemma equiv_entails_sym P Q : Q \226\138\163\226\138\162 P \226\134\146 P \226\138\162 Q.
Time Proof.
Time (apply equiv_spec).
Time Qed.
Time #[global]
Instance entails_proper :
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> iff) ((\226\138\162) : relation PROP)).
Time Proof.
Time
(move  {}=>P1 P2 /equiv_spec [HP1 HP2] Q1 Q2 /equiv_spec 
  [HQ1 HQ2]; <ssreflect_plugin::ssrtclintros@0> split =>?).
Time -
Time by trans P1; [  | trans Q1 ].
Time -
Time by trans P2; [  | trans Q2 ].
Time Qed.
Time Lemma entails_equiv_l P Q R : P \226\138\163\226\138\162 Q \226\134\146 (Q \226\138\162 R) \226\134\146 P \226\138\162 R.
Time Proof.
Time by intros ->.
Time Qed.
Time Lemma entails_equiv_r P Q R : (P \226\138\162 Q) \226\134\146 Q \226\138\163\226\138\162 R \226\134\146 P \226\138\162 R.
Time Proof.
Time by intros ? <-.
Time Qed.
Time #[global]
Instance bi_emp_valid_proper : (Proper ((\226\138\163\226\138\162) ==> iff) (@bi_emp_valid PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance bi_emp_valid_mono : (Proper ((\226\138\162) ==> impl) (@bi_emp_valid PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance bi_emp_valid_flip_mono :
 (Proper (flip (\226\138\162) ==> flip impl) (@bi_emp_valid PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance pure_proper : (Proper (iff ==> (\226\138\163\226\138\162)) (@bi_pure PROP)) |0.
Time Proof.
Time (intros \207\1341 \207\1342 H\207\134).
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time by apply pure_ne.
Time Qed.
Time #[global]
Instance and_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_and PROP)) :=
 (ne_proper_2 _).
Time #[global]
Instance or_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_or PROP)) :=
 (ne_proper_2 _).
Time #[global]
Instance impl_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_impl PROP)) :=
 (ne_proper_2 _).
Time #[global]
Instance sep_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_sep PROP)) :=
 (ne_proper_2 _).
Time #[global]
Instance wand_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_wand PROP)) :=
 (ne_proper_2 _).
Time #[global]
Instance forall_proper  A:
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_forall PROP A)).
Time Proof.
Time (intros \206\1661 \206\1662 H\206\166).
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_ne =>x).
Time (apply equiv_dist, H\206\166).
Time Qed.
Time #[global]
Instance exist_proper  A:
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_exist PROP A)).
Time Proof.
Time (intros \206\1661 \206\1662 H\206\166).
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_ne =>x).
Time (apply equiv_dist, H\206\166).
Time Qed.
Time #[global]
Instance persistently_proper :
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_persistently PROP)) := 
 (ne_proper _).
Time Lemma and_elim_l' P Q R : (P \226\138\162 R) \226\134\146 P \226\136\167 Q \226\138\162 R.
Time Proof.
Time by rewrite and_elim_l.
Time Qed.
Time Lemma and_elim_r' P Q R : (Q \226\138\162 R) \226\134\146 P \226\136\167 Q \226\138\162 R.
Time Proof.
Time by rewrite and_elim_r.
Time Qed.
Time Lemma or_intro_l' P Q R : (P \226\138\162 Q) \226\134\146 P \226\138\162 Q \226\136\168 R.
Time Proof.
Time (intros ->; apply or_intro_l).
Time Qed.
Time Lemma or_intro_r' P Q R : (P \226\138\162 R) \226\134\146 P \226\138\162 Q \226\136\168 R.
Time Proof.
Time (intros ->; apply or_intro_r).
Time Qed.
Time Lemma exist_intro' {A} P (\206\168 : A \226\134\146 PROP) a : (P \226\138\162 \206\168 a) \226\134\146 P \226\138\162 \226\136\131 a, \206\168 a.
Time Proof.
Time (intros ->; apply exist_intro).
Time Qed.
Time Lemma forall_elim' {A} P (\206\168 : A \226\134\146 PROP) : (P \226\138\162 \226\136\128 a, \206\168 a) \226\134\146 \226\136\128 a, P \226\138\162 \206\168 a.
Time Proof.
Time move  {}=>HP a.
Time by rewrite HP forall_elim.
Time Qed.
Time Hint Resolve pure_intro forall_intro: core.
Time Hint Resolve or_elim or_intro_l' or_intro_r': core.
Time Hint Resolve and_intro and_elim_l' and_elim_r': core.
Time Lemma impl_intro_l P Q R : (Q \226\136\167 P \226\138\162 R) \226\134\146 P \226\138\162 Q \226\134\146 R.
Time Proof.
Time (intros HR; apply impl_intro_r; rewrite -HR; auto).
Time Qed.
Time Lemma impl_elim P Q R : (P \226\138\162 Q \226\134\146 R) \226\134\146 (P \226\138\162 Q) \226\134\146 P \226\138\162 R.
Time Proof.
Time (intros).
Time (rewrite -(impl_elim_l' P Q R); auto).
Time Qed.
Time Lemma impl_elim_r' P Q R : (Q \226\138\162 P \226\134\146 R) \226\134\146 P \226\136\167 Q \226\138\162 R.
Time Proof.
Time (intros; apply impl_elim with P; auto).
Time Qed.
Time Lemma impl_elim_l P Q : (P \226\134\146 Q) \226\136\167 P \226\138\162 Q.
Time Proof.
Time by apply impl_elim_l'.
Time Qed.
Time Lemma impl_elim_r P Q : P \226\136\167 (P \226\134\146 Q) \226\138\162 Q.
Time Proof.
Time by apply impl_elim_r'.
Time Qed.
Time Lemma False_elim P : False \226\138\162 P.
Time Proof.
Time by apply (pure_elim' False).
Time Qed.
Time Lemma True_intro P : P \226\138\162 True.
Time Proof.
Time by apply pure_intro.
Time Qed.
Time Hint Immediate False_elim: core.
Time Lemma entails_eq_True P Q : (P \226\138\162 Q) \226\134\148 (P \226\134\146 Q)%I \226\137\161 True%I.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> split =>EQ).
Time -
Time (apply bi.equiv_spec; split; [ by apply True_intro |  ]).
Time (apply impl_intro_r).
Time rewrite and_elim_r //.
Time -
Time trans (P \226\136\167 True)%I.
Time +
Time (<ssreflect_plugin::ssrtclseq@0> apply and_intro ; first  done).
Time by apply pure_intro.
Time +
Time rewrite -EQ impl_elim_r.
Time done.
Time Qed.
Time Lemma entails_impl_True P Q : (P \226\138\162 Q) \226\134\148 (True \226\138\162 P \226\134\146 Q).
Time Proof.
Time (rewrite entails_eq_True equiv_spec; naive_solver).
Time Qed.
Time Lemma and_mono P P' Q Q' : (P \226\138\162 Q) \226\134\146 (P' \226\138\162 Q') \226\134\146 P \226\136\167 P' \226\138\162 Q \226\136\167 Q'.
Time Proof.
Time auto.
Time Qed.
Time Lemma and_mono_l P P' Q : (P \226\138\162 Q) \226\134\146 P \226\136\167 P' \226\138\162 Q \226\136\167 P'.
Time Proof.
Time by intros; apply and_mono.
Time Qed.
Time Lemma and_mono_r P P' Q' : (P' \226\138\162 Q') \226\134\146 P \226\136\167 P' \226\138\162 P \226\136\167 Q'.
Time Proof.
Time by apply and_mono.
Time Qed.
Time Lemma or_mono P P' Q Q' : (P \226\138\162 Q) \226\134\146 (P' \226\138\162 Q') \226\134\146 P \226\136\168 P' \226\138\162 Q \226\136\168 Q'.
Time Proof.
Time auto.
Time Qed.
Time Lemma or_mono_l P P' Q : (P \226\138\162 Q) \226\134\146 P \226\136\168 P' \226\138\162 Q \226\136\168 P'.
Time Proof.
Time by intros; apply or_mono.
Time Qed.
Time Lemma or_mono_r P P' Q' : (P' \226\138\162 Q') \226\134\146 P \226\136\168 P' \226\138\162 P \226\136\168 Q'.
Time Proof.
Time by apply or_mono.
Time Qed.
Time Lemma impl_mono P P' Q Q' : (Q \226\138\162 P) \226\134\146 (P' \226\138\162 Q') \226\134\146 (P \226\134\146 P') \226\138\162 Q \226\134\146 Q'.
Time Proof.
Time (intros HP HQ'; apply impl_intro_l; rewrite -HQ').
Time (apply impl_elim with P; eauto).
Time Qed.
Time
Lemma forall_mono {A} (\206\166 \206\168 : A \226\134\146 PROP) :
  (\226\136\128 a, \206\166 a \226\138\162 \206\168 a) \226\134\146 (\226\136\128 a, \206\166 a) \226\138\162 \226\136\128 a, \206\168 a.
Time Proof.
Time (intros HP).
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a; rewrite -(HP a);
  apply forall_elim).
Time Qed.
Time
Lemma exist_mono {A} (\206\166 \206\168 : A \226\134\146 PROP) :
  (\226\136\128 a, \206\166 a \226\138\162 \206\168 a) \226\134\146 (\226\136\131 a, \206\166 a) \226\138\162 \226\136\131 a, \206\168 a.
Time Proof.
Time (intros H\206\166).
Time
(<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a; rewrite (H\206\166 a);
  apply exist_intro).
Time Qed.
Time #[global]
Instance and_mono' : (Proper ((\226\138\162) ==> (\226\138\162) ==> (\226\138\162)) (@bi_and PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply and_mono.
Time Qed.
Time #[global]
Instance and_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162) ==> flip (\226\138\162)) (@bi_and PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply and_mono.
Time Qed.
Time #[global]
Instance or_mono' : (Proper ((\226\138\162) ==> (\226\138\162) ==> (\226\138\162)) (@bi_or PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply or_mono.
Time Qed.
Time #[global]
Instance or_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162) ==> flip (\226\138\162)) (@bi_or PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply or_mono.
Time Qed.
Time #[global]
Instance impl_mono' : (Proper (flip (\226\138\162) ==> (\226\138\162) ==> (\226\138\162)) (@bi_impl PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply impl_mono.
Time Qed.
Time #[global]
Instance impl_flip_mono' :
 (Proper ((\226\138\162) ==> flip (\226\138\162) ==> flip (\226\138\162)) (@bi_impl PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply impl_mono.
Time Qed.
Time #[global]
Instance forall_mono'  A:
 (Proper (pointwise_relation _ (\226\138\162) ==> (\226\138\162)) (@bi_forall PROP A)).
Time Proof.
Time (intros P1 P2; apply forall_mono).
Time Qed.
Time #[global]
Instance forall_flip_mono'  A:
 (Proper (pointwise_relation _ (flip (\226\138\162)) ==> flip (\226\138\162)) (@bi_forall PROP A)).
Time Proof.
Time (intros P1 P2; apply forall_mono).
Time Qed.
Time #[global]
Instance exist_mono'  A:
 (Proper (pointwise_relation _ (\226\138\162) ==> (\226\138\162)) (@bi_exist PROP A)).
Time Proof.
Time (intros P1 P2; apply exist_mono).
Time Qed.
Time #[global]
Instance exist_flip_mono'  A:
 (Proper (pointwise_relation _ (flip (\226\138\162)) ==> flip (\226\138\162)) (@bi_exist PROP A)).
Time Proof.
Time (intros P1 P2; apply exist_mono).
Time Qed.
Time #[global]Instance and_idem : (IdemP (\226\138\163\226\138\162) (@bi_and PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance or_idem : (IdemP (\226\138\163\226\138\162) (@bi_or PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance and_comm : (Comm (\226\138\163\226\138\162) (@bi_and PROP)).
Time Proof.
Time (intros P Q; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance True_and : (LeftId (\226\138\163\226\138\162) True%I (@bi_and PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance and_True : (RightId (\226\138\163\226\138\162) True%I (@bi_and PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance False_and : (LeftAbsorb (\226\138\163\226\138\162) False%I (@bi_and PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance and_False : (RightAbsorb (\226\138\163\226\138\162) False%I (@bi_and PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance True_or : (LeftAbsorb (\226\138\163\226\138\162) True%I (@bi_or PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance or_True : (RightAbsorb (\226\138\163\226\138\162) True%I (@bi_or PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance False_or : (LeftId (\226\138\163\226\138\162) False%I (@bi_or PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance or_False : (RightId (\226\138\163\226\138\162) False%I (@bi_or PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance and_assoc : (Assoc (\226\138\163\226\138\162) (@bi_and PROP)).
Time Proof.
Time (intros P Q R; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance or_comm : (Comm (\226\138\163\226\138\162) (@bi_or PROP)).
Time Proof.
Time (intros P Q; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance or_assoc : (Assoc (\226\138\163\226\138\162) (@bi_or PROP)).
Time Proof.
Time (intros P Q R; apply (anti_symm (\226\138\162)); auto).
Time Qed.
Time #[global]Instance True_impl : (LeftId (\226\138\163\226\138\162) True%I (@bi_impl PROP)).
Time Proof.
Time (intros P; apply (anti_symm (\226\138\162))).
Time -
Time by rewrite -(left_id True%I (\226\136\167)%I (_ \226\134\146 _)%I) impl_elim_r.
Time -
Time by apply impl_intro_l; rewrite left_id.
Time Qed.
Time Lemma False_impl P : (False \226\134\146 P) \226\138\163\226\138\162 True.
Time Proof.
Time (apply (anti_symm (\226\138\162)); [ by auto |  ]).
Time (apply impl_intro_l).
Time rewrite left_absorb.
Time auto.
Time Qed.
Time
Lemma exist_impl_forall {A} P (\206\168 : A \226\134\146 PROP) :
  ((\226\136\131 x : A, \206\168 x) \226\134\146 P) \226\138\163\226\138\162 (\226\136\128 x : A, \206\168 x \226\134\146 P).
Time Proof.
Time (apply equiv_spec; split).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite -exist_intro.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply impl_intro_r, impl_elim_r', exist_elim =>x).
Time (apply impl_intro_r).
Time by rewrite (forall_elim x) impl_elim_r.
Time Qed.
Time Lemma forall_unit (\206\168 : unit \226\134\146 PROP) : (\226\136\128 x, \206\168 x) \226\138\163\226\138\162 \206\168 ().
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time rewrite (forall_elim ()) //.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>[[]]).
Time done.
Time Qed.
Time Lemma exist_unit (\206\168 : unit \226\134\146 PROP) : (\226\136\131 x, \206\168 x) \226\138\163\226\138\162 \206\168 ().
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>[[]]).
Time done.
Time -
Time rewrite -(exist_intro ()).
Time done.
Time Qed.
Time Lemma impl_curry P Q R : (P \226\134\146 Q \226\134\146 R) \226\138\163\226\138\162 (P \226\136\167 Q \226\134\146 R).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (apply impl_intro_l).
Time by rewrite (comm _ P) -and_assoc !impl_elim_r.
Time -
Time (do 2 apply impl_intro_l).
Time by rewrite assoc (comm _ Q) impl_elim_r.
Time Qed.
Time Lemma or_and_l P Q R : P \226\136\168 Q \226\136\167 R \226\138\163\226\138\162 (P \226\136\168 Q) \226\136\167 (P \226\136\168 R).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> apply (anti_symm (\226\138\162)) ; first  auto).
Time (do 2 (apply impl_elim_l', or_elim; apply impl_intro_l); auto).
Time Qed.
Time Lemma or_and_r P Q R : P \226\136\167 Q \226\136\168 R \226\138\163\226\138\162 (P \226\136\168 R) \226\136\167 (Q \226\136\168 R).
Time Proof.
Time by rewrite -!(comm _ R) or_and_l.
Time Qed.
Time Lemma and_or_l P Q R : P \226\136\167 (Q \226\136\168 R) \226\138\163\226\138\162 P \226\136\167 Q \226\136\168 P \226\136\167 R.
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> apply (anti_symm (\226\138\162)) ; last  auto).
Time (apply impl_elim_r', or_elim; apply impl_intro_l; auto).
Time Qed.
Time Lemma and_or_r P Q R : (P \226\136\168 Q) \226\136\167 R \226\138\163\226\138\162 P \226\136\167 R \226\136\168 Q \226\136\167 R.
Time Proof.
Time by rewrite -!(comm _ R) and_or_l.
Time Qed.
Time
Lemma and_exist_l {A} P (\206\168 : A \226\134\146 PROP) : P \226\136\167 (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, P \226\136\167 \206\168 a).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time (apply impl_elim_r').
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a).
Time (apply impl_intro_l).
Time by rewrite -(exist_intro a).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a).
Time
(<ssreflect_plugin::ssrtclseq@0> apply and_intro ; first  by rewrite
 and_elim_l).
Time by rewrite -(exist_intro a) and_elim_r.
Time Qed.
Time
Lemma and_exist_r {A} P (\206\166 : A \226\134\146 PROP) : (\226\136\131 a, \206\166 a) \226\136\167 P \226\138\163\226\138\162 (\226\136\131 a, \206\166 a \226\136\167 P).
Time Proof.
Time rewrite -(comm _ P) and_exist_l.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_proper =>a).
Time by rewrite comm.
Time Qed.
Time
Lemma or_exist {A} (\206\166 \206\168 : A \226\134\146 PROP) :
  (\226\136\131 a, \206\166 a \226\136\168 \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, \206\166 a) \226\136\168 (\226\136\131 a, \206\168 a).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a).
Time by rewrite -!(exist_intro a).
Time -
Time
(apply or_elim; <ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a;
  rewrite -(exist_intro a); auto).
Time Qed.
Time Lemma and_alt P Q : P \226\136\167 Q \226\138\163\226\138\162 (\226\136\128 b : bool, if b then P else Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm _) ; first 
  <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>- 
  []; auto).
Time
by
 apply and_intro;
  [ rewrite (forall_elim true) | rewrite (forall_elim false) ].
Time Qed.
Time Lemma or_alt P Q : P \226\136\168 Q \226\138\163\226\138\162 (\226\136\131 b : bool, if b then P else Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm _) ; last 
  <ssreflect_plugin::ssrtclintros@0> apply exist_elim =>- 
  []; auto).
Time
by
 apply or_elim;
  [ rewrite -(exist_intro true) | rewrite -(exist_intro false) ].
Time Qed.
Time Lemma entails_equiv_and P Q : (P \226\138\163\226\138\162 Q \226\136\167 P) \226\134\148 (P \226\138\162 Q).
Time Proof.
Time split.
Time by intros ->; auto.
Time (intros; apply (anti_symm _); auto).
Time Qed.
Time #[global]Instance iff_ne : (NonExpansive2 (@bi_iff PROP)).
Time Proof.
Time (unfold bi_iff; solve_proper).
Time Qed.
Time #[global]
Instance iff_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_iff PROP)) :=
 (ne_proper_2 _).
Time Lemma iff_refl Q P : Q \226\138\162 P \226\134\148 P.
Time Proof.
Time (rewrite /bi_iff; apply and_intro; apply impl_intro_l; auto).
Time Qed.
Time Hint Resolve sep_mono: core.
Time Lemma sep_mono_l P P' Q : (P \226\138\162 Q) \226\134\146 P \226\136\151 P' \226\138\162 Q \226\136\151 P'.
Time Proof.
Time by intros; apply sep_mono.
Time Qed.
Time Lemma sep_mono_r P P' Q' : (P' \226\138\162 Q') \226\134\146 P \226\136\151 P' \226\138\162 P \226\136\151 Q'.
Time Proof.
Time by apply sep_mono.
Time Qed.
Time #[global]
Instance sep_mono' : (Proper ((\226\138\162) ==> (\226\138\162) ==> (\226\138\162)) (@bi_sep PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply sep_mono.
Time Qed.
Time #[global]
Instance sep_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162) ==> flip (\226\138\162)) (@bi_sep PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply sep_mono.
Time Qed.
Time Lemma wand_mono P P' Q Q' : (Q \226\138\162 P) \226\134\146 (P' \226\138\162 Q') \226\134\146 (P -\226\136\151 P') \226\138\162 Q -\226\136\151 Q'.
Time Proof.
Time (intros HP HQ; apply wand_intro_r).
Time rewrite HP -HQ.
Time by apply wand_elim_l'.
Time Qed.
Time #[global]
Instance wand_mono' : (Proper (flip (\226\138\162) ==> (\226\138\162) ==> (\226\138\162)) (@bi_wand PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply wand_mono.
Time Qed.
Time #[global]
Instance wand_flip_mono' :
 (Proper ((\226\138\162) ==> flip (\226\138\162) ==> flip (\226\138\162)) (@bi_wand PROP)).
Time Proof.
Time by intros P P' HP Q Q' HQ; apply wand_mono.
Time Qed.
Time #[global]Instance sep_comm : (Comm (\226\138\163\226\138\162) (@bi_sep PROP)).
Time Proof.
Time (intros P Q; apply (anti_symm _); auto using sep_comm').
Time Qed.
Time #[global]Instance sep_assoc : (Assoc (\226\138\163\226\138\162) (@bi_sep PROP)).
Time Proof.
Time (intros P Q R; apply (anti_symm _); auto using sep_assoc').
Time by rewrite !(comm _ P) !(comm _ _ R) sep_assoc'.
Time Qed.
Time #[global]Instance emp_sep : (LeftId (\226\138\163\226\138\162) emp%I (@bi_sep PROP)).
Time Proof.
Time (intros P; apply (anti_symm _); auto using emp_sep_1, emp_sep_2).
Time Qed.
Time #[global]Instance sep_emp : (RightId (\226\138\163\226\138\162) emp%I (@bi_sep PROP)).
Time Proof.
Time by intros P; rewrite comm left_id.
Time Qed.
Time #[global]Instance sep_False : (LeftAbsorb (\226\138\163\226\138\162) False%I (@bi_sep PROP)).
Time Proof.
Time (intros P; apply (anti_symm _); auto using wand_elim_l').
Time Qed.
Time #[global]Instance False_sep : (RightAbsorb (\226\138\163\226\138\162) False%I (@bi_sep PROP)).
Time Proof.
Time (intros P).
Time by rewrite comm left_absorb.
Time Qed.
Time Lemma True_sep_2 P : P \226\138\162 True \226\136\151 P.
Time Proof.
Time rewrite -{+1}[P](left_id emp%I bi_sep).
Time auto using sep_mono.
Time Qed.
Time Lemma sep_True_2 P : P \226\138\162 P \226\136\151 True.
Time Proof.
Time by rewrite comm -True_sep_2.
Time Qed.
Time Lemma sep_intro_emp_valid_l P Q R : P \226\134\146 (R \226\138\162 Q) \226\134\146 R \226\138\162 P \226\136\151 Q.
Time Proof.
Time (intros ? ->).
Time rewrite -{+1}(left_id emp%I _ Q).
Time by apply sep_mono.
Time Qed.
Time Lemma sep_intro_emp_valid_r P Q R : (R \226\138\162 P) \226\134\146 Q \226\134\146 R \226\138\162 P \226\136\151 Q.
Time Proof.
Time (intros -> ?).
Time rewrite comm.
Time by apply sep_intro_emp_valid_l.
Time Qed.
Time Lemma sep_elim_emp_valid_l P Q R : P \226\134\146 (P \226\136\151 R \226\138\162 Q) \226\134\146 R \226\138\162 Q.
Time Proof.
Time (intros <- <-).
Time by rewrite left_id.
Time Qed.
Time Lemma sep_elim_emp_valid_r P Q R : P \226\134\146 (R \226\136\151 P \226\138\162 Q) \226\134\146 R \226\138\162 Q.
Time Proof.
Time (intros <- <-).
Time by rewrite right_id.
Time Qed.
Time Lemma wand_intro_l P Q R : (Q \226\136\151 P \226\138\162 R) \226\134\146 P \226\138\162 Q -\226\136\151 R.
Time Proof.
Time (rewrite comm; apply wand_intro_r).
Time Qed.
Time Lemma wand_elim_l P Q : (P -\226\136\151 Q) \226\136\151 P \226\138\162 Q.
Time Proof.
Time by apply wand_elim_l'.
Time Qed.
Time Lemma wand_elim_r P Q : P \226\136\151 (P -\226\136\151 Q) \226\138\162 Q.
Time Proof.
Time (rewrite (comm _ P); apply wand_elim_l).
Time Qed.
Time Lemma wand_elim_r' P Q R : (Q \226\138\162 P -\226\136\151 R) \226\134\146 P \226\136\151 Q \226\138\162 R.
Time Proof.
Time (intros ->; apply wand_elim_r).
Time Qed.
Time Lemma wand_apply P Q R S : (P \226\138\162 Q -\226\136\151 R) \226\134\146 (S \226\138\162 P \226\136\151 Q) \226\134\146 S \226\138\162 R.
Time Proof.
Time (intros HR%wand_elim_l' HQ).
Time by rewrite HQ.
Time Qed.
Time Lemma wand_frame_l P Q R : (Q -\226\136\151 R) \226\138\162 P \226\136\151 Q -\226\136\151 P \226\136\151 R.
Time Proof.
Time (apply wand_intro_l).
Time rewrite -assoc.
Time (apply sep_mono_r, wand_elim_r).
Time Qed.
Time Lemma wand_frame_r P Q R : (Q -\226\136\151 R) \226\138\162 Q \226\136\151 P -\226\136\151 R \226\136\151 P.
Time Proof.
Time (apply wand_intro_l).
Time rewrite ![(_ \226\136\151 P)%I]comm -assoc.
Time (apply sep_mono_r, wand_elim_r).
Time Qed.
Time #[global]Instance emp_wand : (LeftId (\226\138\163\226\138\162) emp%I (@bi_wand PROP)).
Time Proof.
Time (intros P).
Time (apply (anti_symm _)).
Time -
Time by rewrite -[(emp -\226\136\151 P)%I]left_id wand_elim_r.
Time -
Time (apply wand_intro_l).
Time by rewrite left_id.
Time Qed.
Time Lemma False_wand P : (False -\226\136\151 P) \226\138\163\226\138\162 True.
Time Proof.
Time (apply (anti_symm (\226\138\162)); [ by auto |  ]).
Time (apply wand_intro_l).
Time rewrite left_absorb.
Time auto.
Time Qed.
Time Lemma wand_trans P Q R : (P -\226\136\151 Q) \226\136\151 (Q -\226\136\151 R) \226\138\162 P -\226\136\151 R.
Time Proof.
Time (apply wand_intro_l).
Time by rewrite assoc !wand_elim_r.
Time Qed.
Time Lemma wand_curry P Q R : (P -\226\136\151 Q -\226\136\151 R) \226\138\163\226\138\162 (P \226\136\151 Q -\226\136\151 R).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (apply wand_intro_l).
Time by rewrite (comm _ P) -assoc !wand_elim_r.
Time -
Time (do 2 apply wand_intro_l).
Time by rewrite assoc (comm _ Q) wand_elim_r.
Time Qed.
Time Lemma sep_and_l P Q R : P \226\136\151 Q \226\136\167 R \226\138\162 (P \226\136\151 Q) \226\136\167 P \226\136\151 R.
Time Proof.
Time auto.
Time Qed.
Time Lemma sep_and_r P Q R : (P \226\136\167 Q) \226\136\151 R \226\138\162 (P \226\136\151 R) \226\136\167 Q \226\136\151 R.
Time Proof.
Time auto.
Time Qed.
Time Lemma sep_or_l P Q R : P \226\136\151 (Q \226\136\168 R) \226\138\163\226\138\162 P \226\136\151 Q \226\136\168 P \226\136\151 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm (\226\138\162)) ; last  by eauto  8).
Time (apply wand_elim_r', or_elim; apply wand_intro_l; auto).
Time Qed.
Time Lemma sep_or_r P Q R : (P \226\136\168 Q) \226\136\151 R \226\138\163\226\138\162 P \226\136\151 R \226\136\168 Q \226\136\151 R.
Time Proof.
Time by rewrite -!(comm _ R) sep_or_l.
Time Qed.
Time
Lemma sep_exist_l {A} P (\206\168 : A \226\134\146 PROP) : P \226\136\151 (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, P \226\136\151 \206\168 a).
Time Proof.
Time (intros; apply (anti_symm (\226\138\162))).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply wand_elim_r', exist_elim =>a).
Time (apply wand_intro_l).
Time by rewrite -(exist_intro a).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a; apply sep_mono;
  auto using exist_intro).
Time Qed.
Time
Lemma sep_exist_r {A} (\206\166 : A \226\134\146 PROP) Q : (\226\136\131 a, \206\166 a) \226\136\151 Q \226\138\163\226\138\162 (\226\136\131 a, \206\166 a \226\136\151 Q).
Time Proof.
Time (setoid_rewrite (comm _ _ Q); apply sep_exist_l).
Time Qed.
Time Lemma sep_forall_l {A} P (\206\168 : A \226\134\146 PROP) : P \226\136\151 (\226\136\128 a, \206\168 a) \226\138\162 \226\136\128 a, P \226\136\151 \206\168 a.
Time Proof.
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a; rewrite
  forall_elim.
Time Qed.
Time Lemma sep_forall_r {A} (\206\166 : A \226\134\146 PROP) Q : (\226\136\128 a, \206\166 a) \226\136\151 Q \226\138\162 \226\136\128 a, \206\166 a \226\136\151 Q.
Time Proof.
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a; rewrite
  forall_elim.
Time Qed.
Time #[global]Instance wand_iff_ne : (NonExpansive2 (@bi_wand_iff PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance wand_iff_proper :
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_wand_iff PROP)) := 
 (ne_proper_2 _).
Time Lemma wand_iff_refl P : emp \226\138\162 P \226\136\151-\226\136\151 P.
Time Proof.
Time (apply and_intro; apply wand_intro_l; by rewrite right_id).
Time Qed.
Time Lemma wand_entails P Q : (P -\226\136\151 Q)%I \226\134\146 P \226\138\162 Q.
Time Proof.
Time (intros).
Time rewrite -[P]emp_sep.
Time by apply wand_elim_l'.
Time Qed.
Time Lemma entails_wand P Q : (P \226\138\162 Q) \226\134\146 (P -\226\136\151 Q)%I.
Time Proof.
Time (intros ->).
Time (apply wand_intro_r).
Time by rewrite left_id.
Time Qed.
Time Lemma entails_wand' P Q : (P \226\138\162 Q) \226\134\146 emp \226\138\162 P -\226\136\151 Q.
Time Proof.
Time (apply entails_wand).
Time Qed.
Time Lemma equiv_wand_iff P Q : P \226\138\163\226\138\162 Q \226\134\146 (P \226\136\151-\226\136\151 Q)%I.
Time Proof.
Time (intros ->; apply wand_iff_refl).
Time Qed.
Time Lemma wand_iff_equiv P Q : (P \226\136\151-\226\136\151 Q)%I \226\134\146 P \226\138\163\226\138\162 Q.
Time Proof.
Time
(intros HPQ; apply (anti_symm (\226\138\162)); apply wand_entails; rewrite /bi_emp_valid
  HPQ /bi_wand_iff; auto).
Time Qed.
Time Lemma entails_impl P Q : (P \226\138\162 Q) \226\134\146 (P \226\134\146 Q)%I.
Time Proof.
Time (intros ->).
Time (apply impl_intro_l).
Time auto.
Time Qed.
Time Lemma impl_entails P Q `{!Affine P} : (P \226\134\146 Q)%I \226\134\146 P \226\138\162 Q.
Time Proof.
Time (intros HPQ).
Time (<ssreflect_plugin::ssrtclintros@0> apply impl_elim with P =>//).
Time by rewrite {+1}(affine P).
Time Qed.
Time Lemma equiv_iff P Q : P \226\138\163\226\138\162 Q \226\134\146 (P \226\134\148 Q)%I.
Time Proof.
Time (intros ->; apply iff_refl).
Time Qed.
Time Lemma iff_equiv P Q `{!Affine P} `{!Affine Q} : (P \226\134\148 Q)%I \226\134\146 P \226\138\163\226\138\162 Q.
Time Proof.
Time
(intros HPQ; apply (anti_symm (\226\138\162)); apply : {}impl_entails {}; rewrite
  /bi_emp_valid HPQ /bi_iff; auto).
Time Qed.
Time
Lemma and_parallel P1 P2 Q1 Q2 :
  P1 \226\136\167 P2 -\226\136\151 (P1 -\226\136\151 Q1) \226\136\167 (P2 -\226\136\151 Q2) -\226\136\151 Q1 \226\136\167 Q2.
Time Proof.
Time (apply wand_intro_r, and_intro).
Time -
Time rewrite !and_elim_l wand_elim_r.
Time done.
Time -
Time rewrite !and_elim_r wand_elim_r.
Time done.
Time Qed.
Time
Lemma wandM_sound (mP : option PROP) Q : (mP -\226\136\151? Q) \226\138\163\226\138\162 (default emp mP -\226\136\151 Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> destruct mP; simpl ; first  done).
Time rewrite emp_wand //.
Time Qed.
Time Lemma pure_elim \207\134 Q R : (Q \226\138\162 \226\140\156\207\134\226\140\157) \226\134\146 (\207\134 \226\134\146 Q \226\138\162 R) \226\134\146 Q \226\138\162 R.
Time Proof.
Time (intros HQ HQR).
Time rewrite -(idemp (\226\136\167)%I Q) {+1}HQ.
Time (<ssreflect_plugin::ssrtclintros@0> apply impl_elim_l', pure_elim' =>?).
Time (apply impl_intro_l).
Time (rewrite and_elim_l; auto).
Time Qed.
Time Lemma pure_mono \207\1341 \207\1342 : (\207\1341 \226\134\146 \207\1342) \226\134\146 \226\140\156\207\1341\226\140\157 \226\138\162 \226\140\156\207\1342\226\140\157.
Time Proof.
Time auto using pure_elim', pure_intro.
Time Qed.
Time #[global]Instance pure_mono' : (Proper (impl ==> (\226\138\162)) (@bi_pure PROP)).
Time Proof.
Time (intros \207\1341 \207\1342; apply pure_mono).
Time Qed.
Time #[global]
Instance pure_flip_mono : (Proper (flip impl ==> flip (\226\138\162)) (@bi_pure PROP)).
Time Proof.
Time (intros \207\1341 \207\1342; apply pure_mono).
Time Qed.
Time Lemma pure_iff \207\1341 \207\1342 : \207\1341 \226\134\148 \207\1342 \226\134\146 \226\140\156\207\1341\226\140\157 \226\138\163\226\138\162 \226\140\156\207\1342\226\140\157.
Time Proof.
Time (intros [? ?]; apply (anti_symm _); auto using pure_mono).
Time Qed.
Time Lemma pure_elim_l \207\134 Q R : (\207\134 \226\134\146 Q \226\138\162 R) \226\134\146 \226\140\156\207\134\226\140\157 \226\136\167 Q \226\138\162 R.
Time Proof.
Time (intros; apply pure_elim with \207\134; eauto).
Time Qed.
Time Lemma pure_elim_r \207\134 Q R : (\207\134 \226\134\146 Q \226\138\162 R) \226\134\146 Q \226\136\167 \226\140\156\207\134\226\140\157 \226\138\162 R.
Time Proof.
Time (intros; apply pure_elim with \207\134; eauto).
Time Qed.
Time Lemma pure_True (\207\134 : Prop) : \207\134 \226\134\146 \226\140\156\207\134\226\140\157 \226\138\163\226\138\162 True.
Time Proof.
Time (intros; apply (anti_symm _); auto).
Time Qed.
Time Lemma pure_False (\207\134 : Prop) : \194\172 \207\134 \226\134\146 \226\140\156\207\134\226\140\157 \226\138\163\226\138\162 False.
Time Proof.
Time (intros; apply (anti_symm _); eauto using pure_mono).
Time Qed.
Time Lemma pure_and \207\1341 \207\1342 : \226\140\156\207\1341 \226\136\167 \207\1342\226\140\157 \226\138\163\226\138\162 \226\140\156\207\1341\226\140\157 \226\136\167 \226\140\156\207\1342\226\140\157.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (apply and_intro; apply pure_mono; tauto).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> eapply (pure_elim \207\1341); [ auto |  ] =>?).
Time rewrite and_elim_r.
Time auto using pure_mono.
Time Qed.
Time Lemma pure_or \207\1341 \207\1342 : \226\140\156\207\1341 \226\136\168 \207\1342\226\140\157 \226\138\163\226\138\162 \226\140\156\207\1341\226\140\157 \226\136\168 \226\140\156\207\1342\226\140\157.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> eapply pure_elim =>// - 
  [?|?]; auto using pure_mono).
Time -
Time (apply or_elim; eauto using pure_mono).
Time Qed.
Time Lemma pure_impl \207\1341 \207\1342 : \226\140\156\207\1341 \226\134\146 \207\1342\226\140\157 \226\138\163\226\138\162 (\226\140\156\207\1341\226\140\157 \226\134\146 \226\140\156\207\1342\226\140\157).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (apply impl_intro_l).
Time rewrite -pure_and.
Time (apply pure_mono).
Time naive_solver.
Time -
Time rewrite -pure_forall_2.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>?).
Time
by rewrite -(left_id True bi_and (_ \226\134\146 _))%I (pure_True \207\1341) // impl_elim_r.
Time Qed.
Time Lemma pure_forall {A} (\207\134 : A \226\134\146 Prop) : \226\140\156\226\136\128 x, \207\134 x\226\140\157 \226\138\163\226\138\162 (\226\136\128 x, \226\140\156\207\134 x\226\140\157).
Time Proof.
Time (apply (anti_symm _); auto using pure_forall_2).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time eauto using pure_mono.
Time Qed.
Time Lemma pure_exist {A} (\207\134 : A \226\134\146 Prop) : \226\140\156\226\136\131 x, \207\134 x\226\140\157 \226\138\163\226\138\162 (\226\136\131 x, \226\140\156\207\134 x\226\140\157).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> eapply pure_elim =>// - [x ?]).
Time (rewrite -(exist_intro x); auto using pure_mono).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>x).
Time eauto using pure_mono.
Time Qed.
Time Lemma pure_impl_forall \207\134 P : (\226\140\156\207\134\226\140\157 \226\134\146 P) \226\138\163\226\138\162 (\226\136\128 _ : \207\134, P).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>?).
Time by rewrite pure_True // left_id.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>H\207\134).
Time by rewrite (forall_elim H\207\134).
Time Qed.
Time Lemma pure_alt \207\134 : \226\140\156\207\134\226\140\157 \226\138\163\226\138\162 (\226\136\131 _ : \207\134, True).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (eapply pure_elim; <ssreflect_plugin::ssrtclintros@0> eauto =>H).
Time (rewrite -(exist_intro H); auto).
Time -
Time by apply exist_elim, pure_intro.
Time Qed.
Time Lemma pure_wand_forall \207\134 P `{!Absorbing P} : (\226\140\156\207\134\226\140\157 -\226\136\151 P) \226\138\163\226\138\162 (\226\136\128 _ : \207\134, P).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>H\207\134).
Time rewrite -(pure_intro \207\134 emp%I) // emp_wand //.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply wand_intro_l, wand_elim_l', pure_elim' =>H\207\134).
Time (apply wand_intro_l).
Time rewrite (forall_elim H\207\134) comm.
Time by apply absorbing.
Time Qed.
Time #[global]Instance affinely_ne : (NonExpansive (@bi_affinely PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance affinely_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_affinely PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance affinely_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_affinely PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance affinely_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_affinely PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma affinely_elim_emp P : <affine> P \226\138\162 emp.
Time Proof.
Time (rewrite /bi_affinely; auto).
Time Qed.
Time Lemma affinely_elim P : <affine> P \226\138\162 P.
Time Proof.
Time (rewrite /bi_affinely; auto).
Time Qed.
Time Lemma affinely_mono P Q : (P \226\138\162 Q) \226\134\146 <affine> P \226\138\162 <affine> Q.
Time Proof.
Time by intros ->.
Time Qed.
Time Lemma affinely_idemp P : <affine> <affine> P \226\138\163\226\138\162 <affine> P.
Time Proof.
Time by rewrite /bi_affinely assoc idemp.
Time Qed.
Time Lemma affinely_intro' P Q : (<affine> P \226\138\162 Q) \226\134\146 <affine> P \226\138\162 <affine> Q.
Time Proof.
Time (intros <-).
Time by rewrite affinely_idemp.
Time Qed.
Time Lemma affinely_False : <affine> False \226\138\163\226\138\162 False.
Time Proof.
Time by rewrite /bi_affinely right_absorb.
Time Qed.
Time Lemma affinely_emp : <affine> emp \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite /bi_affinely (idemp bi_and).
Time Qed.
Time Lemma affinely_or P Q : <affine> (P \226\136\168 Q) \226\138\163\226\138\162 <affine> P \226\136\168 <affine> Q.
Time Proof.
Time by rewrite /bi_affinely and_or_l.
Time Qed.
Time Lemma affinely_and P Q : <affine> (P \226\136\167 Q) \226\138\163\226\138\162 <affine> P \226\136\167 <affine> Q.
Time Proof.
Time rewrite /bi_affinely -(comm _ P) (assoc _ (_ \226\136\167 _)%I) -!(assoc _ P).
Time by rewrite idemp !assoc (comm _ P).
Time Qed.
Time Lemma affinely_sep_2 P Q : <affine> P \226\136\151 <affine> Q \226\138\162 <affine> (P \226\136\151 Q).
Time Proof.
Time rewrite /bi_affinely.
Time (apply and_intro).
Time -
Time by rewrite !and_elim_l right_id.
Time -
Time by rewrite !and_elim_r.
Time Qed.
Time
Lemma affinely_sep `{BiPositive PROP} P Q :
  <affine> (P \226\136\151 Q) \226\138\163\226\138\162 <affine> P \226\136\151 <affine> Q.
Time Proof.
Time (apply (anti_symm _), affinely_sep_2).
Time
by rewrite -{+1}affinely_idemp bi_positive !(comm _ (<affine> P)%I)
 bi_positive.
Time Qed.
Time
Lemma affinely_forall {A} (\206\166 : A \226\134\146 PROP) :
  <affine> (\226\136\128 a, \206\166 a) \226\138\162 \226\136\128 a, <affine> \206\166 a.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a).
Time by rewrite (forall_elim a).
Time Qed.
Time
Lemma affinely_exist {A} (\206\166 : A \226\134\146 PROP) :
  <affine> (\226\136\131 a, \206\166 a) \226\138\163\226\138\162 (\226\136\131 a, <affine> \206\166 a).
Time Proof.
Time by rewrite /bi_affinely and_exist_l.
Time Qed.
Time Lemma affinely_True_emp : <affine> True \226\138\163\226\138\162 <affine> emp.
Time Proof.
Time (apply (anti_symm _); rewrite /bi_affinely; auto).
Time Qed.
Time Lemma affinely_and_l P Q : <affine> P \226\136\167 Q \226\138\163\226\138\162 <affine> (P \226\136\167 Q).
Time Proof.
Time by rewrite /bi_affinely assoc.
Time Qed.
Time Lemma affinely_and_r P Q : P \226\136\167 <affine> Q \226\138\163\226\138\162 <affine> (P \226\136\167 Q).
Time Proof.
Time by rewrite /bi_affinely !assoc (comm _ P).
Time Qed.
Time Lemma affinely_and_lr P Q : <affine> P \226\136\167 Q \226\138\163\226\138\162 P \226\136\167 <affine> Q.
Time Proof.
Time by rewrite affinely_and_l affinely_and_r.
Time Qed.
Time #[global]
Instance absorbingly_ne : (NonExpansive (@bi_absorbingly PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance absorbingly_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_absorbingly PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance absorbingly_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_absorbingly PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance absorbingly_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_absorbingly PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma absorbingly_intro P : P \226\138\162 <absorb> P.
Time Proof.
Time by rewrite /bi_absorbingly -True_sep_2.
Time Qed.
Time Lemma absorbingly_mono P Q : (P \226\138\162 Q) \226\134\146 <absorb> P \226\138\162 <absorb> Q.
Time Proof.
Time by intros ->.
Time Qed.
Time Lemma absorbingly_idemp P : <absorb> <absorb> P \226\138\163\226\138\162 <absorb> P.
Time Proof.
Time (apply (anti_symm _), absorbingly_intro).
Time rewrite /bi_absorbingly assoc.
Time (apply sep_mono; auto).
Time Qed.
Time Lemma absorbingly_pure \207\134 : <absorb> \226\140\156\207\134\226\140\157 \226\138\163\226\138\162 \226\140\156\207\134\226\140\157.
Time Proof.
Time (apply (anti_symm _), absorbingly_intro).
Time (<ssreflect_plugin::ssrtclintros@0> apply wand_elim_r', pure_elim' =>?).
Time (apply wand_intro_l; auto).
Time Qed.
Time Lemma absorbingly_or P Q : <absorb> (P \226\136\168 Q) \226\138\163\226\138\162 <absorb> P \226\136\168 <absorb> Q.
Time Proof.
Time by rewrite /bi_absorbingly sep_or_l.
Time Qed.
Time
Lemma absorbingly_and_1 P Q : <absorb> (P \226\136\167 Q) \226\138\162 <absorb> P \226\136\167 <absorb> Q.
Time Proof.
Time (apply and_intro; apply absorbingly_mono; auto).
Time Qed.
Time
Lemma absorbingly_forall {A} (\206\166 : A \226\134\146 PROP) :
  <absorb> (\226\136\128 a, \206\166 a) \226\138\162 \226\136\128 a, <absorb> \206\166 a.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a).
Time by rewrite (forall_elim a).
Time Qed.
Time
Lemma absorbingly_exist {A} (\206\166 : A \226\134\146 PROP) :
  <absorb> (\226\136\131 a, \206\166 a) \226\138\163\226\138\162 (\226\136\131 a, <absorb> \206\166 a).
Time Proof.
Time by rewrite /bi_absorbingly sep_exist_l.
Time Qed.
Time Lemma absorbingly_sep P Q : <absorb> (P \226\136\151 Q) \226\138\163\226\138\162 <absorb> P \226\136\151 <absorb> Q.
Time Proof.
Time
by rewrite -{+1}absorbingly_idemp /bi_absorbingly !assoc -!(comm _ P) !assoc.
Time Qed.
Time Lemma absorbingly_True_emp : <absorb> True \226\138\163\226\138\162 <absorb> emp.
Time Proof.
Time by rewrite absorbingly_pure /bi_absorbingly right_id.
Time Qed.
Time
Lemma absorbingly_wand P Q : <absorb> (P -\226\136\151 Q) \226\138\162 <absorb> P -\226\136\151 <absorb> Q.
Time Proof.
Time (apply wand_intro_l).
Time by rewrite -absorbingly_sep wand_elim_r.
Time Qed.
Time Lemma absorbingly_sep_l P Q : <absorb> P \226\136\151 Q \226\138\163\226\138\162 <absorb> (P \226\136\151 Q).
Time Proof.
Time by rewrite /bi_absorbingly assoc.
Time Qed.
Time Lemma absorbingly_sep_r P Q : P \226\136\151 <absorb> Q \226\138\163\226\138\162 <absorb> (P \226\136\151 Q).
Time Proof.
Time by rewrite /bi_absorbingly !assoc (comm _ P).
Time Qed.
Time Lemma absorbingly_sep_lr P Q : <absorb> P \226\136\151 Q \226\138\163\226\138\162 P \226\136\151 <absorb> Q.
Time Proof.
Time by rewrite absorbingly_sep_l absorbingly_sep_r.
Time Qed.
Time
Lemma affinely_absorbingly_elim `{!BiPositive PROP} 
  P : <affine> <absorb> P \226\138\163\226\138\162 <affine> P.
Time Proof.
Time (apply (anti_symm _), affinely_mono, absorbingly_intro).
Time
by rewrite /bi_absorbingly affinely_sep affinely_True_emp affinely_emp
 left_id.
Time Qed.
Time #[global]
Instance Affine_proper : (Proper ((\226\138\163\226\138\162) ==> iff) (@Affine PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance Absorbing_proper : (Proper ((\226\138\163\226\138\162) ==> iff) (@Absorbing PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma affine_affinely P `{!Affine P} : <affine> P \226\138\163\226\138\162 P.
Time Proof.
Time rewrite /bi_affinely.
Time (apply (anti_symm _); auto).
Time Qed.
Time Lemma absorbing_absorbingly P `{!Absorbing P} : <absorb> P \226\138\163\226\138\162 P.
Time Proof.
Time by apply (anti_symm _), absorbingly_intro.
Time Qed.
Time Lemma True_affine_all_affine P : Affine (PROP:=PROP) True \226\134\146 Affine P.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Affine =>{+}<-; auto).
Time Qed.
Time
Lemma emp_absorbing_all_absorbing P :
  Absorbing (PROP:=PROP) emp \226\134\146 Absorbing P.
Time Proof.
Time (intros).
Time rewrite /Absorbing -{+2}(emp_sep P).
Time rewrite -(absorbing emp) absorbingly_sep_l left_id //.
Time Qed.
Time Lemma sep_elim_l P Q `{H : TCOr (Affine Q) (Absorbing P)} : P \226\136\151 Q \226\138\162 P.
Time Proof.
Time (destruct H).
Time -
Time by rewrite (affine Q) right_id.
Time -
Time by rewrite (True_intro Q) comm.
Time Qed.
Time Lemma sep_elim_r P Q `{H : TCOr (Affine P) (Absorbing Q)} : P \226\136\151 Q \226\138\162 Q.
Time Proof.
Time by rewrite comm sep_elim_l.
Time Qed.
Time
Lemma sep_and P Q :
  TCOr (Affine P) (Absorbing Q)
  \226\134\146 TCOr (Absorbing P) (Affine Q) \226\134\146 P \226\136\151 Q \226\138\162 P \226\136\167 Q.
Time Proof.
Time
(intros [?| ?] [?| ?]; apply and_intro;
  apply : {}sep_elim_l {} || apply : {}sep_elim_r {}).
Time Qed.
Time Lemma affinely_intro P Q `{!Affine P} : (P \226\138\162 Q) \226\134\146 P \226\138\162 <affine> Q.
Time Proof.
Time (intros <-).
Time by rewrite affine_affinely.
Time Qed.
Time Lemma emp_and P `{!Affine P} : emp \226\136\167 P \226\138\163\226\138\162 P.
Time Proof.
Time (apply (anti_symm _); auto).
Time Qed.
Time Lemma and_emp P `{!Affine P} : P \226\136\167 emp \226\138\163\226\138\162 P.
Time Proof.
Time (apply (anti_symm _); auto).
Time Qed.
Time Lemma emp_or P `{!Affine P} : emp \226\136\168 P \226\138\163\226\138\162 emp.
Time Proof.
Time (apply (anti_symm _); auto).
Time Qed.
Time Lemma or_emp P `{!Affine P} : P \226\136\168 emp \226\138\163\226\138\162 emp.
Time Proof.
Time (apply (anti_symm _); auto).
Time Qed.
Time Lemma True_sep P `{!Absorbing P} : True \226\136\151 P \226\138\163\226\138\162 P.
Time Proof.
Time (apply (anti_symm _); auto using True_sep_2).
Time Qed.
Time Lemma sep_True P `{!Absorbing P} : P \226\136\151 True \226\138\163\226\138\162 P.
Time Proof.
Time by rewrite comm True_sep.
Time Qed.
Time Lemma True_emp_iff_BiAffine : BiAffine PROP \226\134\148 (True \226\138\162 emp).
Time Proof.
Time split.
Time -
Time (intros ?).
Time exact : {}affine {}.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /BiAffine /Affine =>Hemp ?).
Time rewrite -Hemp.
Time exact : {}True_intro {}.
Time Qed.
Time Section bi_affine.
Time Context `{BiAffine PROP}.
Time #[global]Instance bi_affine_absorbing  P: (Absorbing P) |0.
Time Proof.
Time by rewrite /Absorbing /bi_absorbingly (affine True%I) left_id.
Time Qed.
Time #[global]Instance bi_affine_positive : (BiPositive PROP).
Time Proof.
Time (intros P Q).
Time by rewrite !affine_affinely.
Time Qed.
Time Lemma True_emp : True \226\138\163\226\138\162 emp.
Time Proof.
Time (apply (anti_symm _); auto using affine).
Time Qed.
Time #[global]Instance emp_and' : (LeftId (\226\138\163\226\138\162) emp%I (@bi_and PROP)).
Time Proof.
Time (intros P).
Time by rewrite -True_emp left_id.
Time Qed.
Time #[global]Instance and_emp' : (RightId (\226\138\163\226\138\162) emp%I (@bi_and PROP)).
Time Proof.
Time (intros P).
Time by rewrite -True_emp right_id.
Time Qed.
Time #[global]Instance True_sep' : (LeftId (\226\138\163\226\138\162) True%I (@bi_sep PROP)).
Time Proof.
Time (intros P).
Time by rewrite True_emp left_id.
Time Qed.
Time #[global]Instance sep_True' : (RightId (\226\138\163\226\138\162) True%I (@bi_sep PROP)).
Time Proof.
Time (intros P).
Time by rewrite True_emp right_id.
Time Qed.
Time Lemma impl_wand_1 P Q : (P \226\134\146 Q) \226\138\162 P -\226\136\151 Q.
Time Proof.
Time (apply wand_intro_l).
Time by rewrite sep_and impl_elim_r.
Time Qed.
Time
Lemma decide_emp \207\134 `{!Decision \207\134} (P : PROP) :
  (if decide \207\134 then P else emp) \226\138\163\226\138\162 (\226\140\156\207\134\226\140\157 \226\134\146 P).
Time Proof.
Time (destruct (decide _)).
Time -
Time by rewrite pure_True // True_impl.
Time -
Time by rewrite pure_False // False_impl True_emp.
Time Qed.
Time End bi_affine.
Time Hint Resolve persistently_mono: core.
Time #[global]
Instance persistently_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_persistently PROP)).
Time Proof.
Time (intros P Q; apply persistently_mono).
Time Qed.
Time #[global]
Instance persistently_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_persistently PROP)).
Time Proof.
Time (intros P Q; apply persistently_mono).
Time Qed.
Time Lemma absorbingly_elim_persistently P : <absorb> <pers> P \226\138\163\226\138\162 <pers> P.
Time Proof.
Time (apply (anti_symm _), absorbingly_intro).
Time by rewrite /bi_absorbingly comm persistently_absorbing.
Time Qed.
Time
Lemma persistently_forall {A} (\206\168 : A \226\134\146 PROP) :
  <pers> (\226\136\128 a, \206\168 a) \226\138\163\226\138\162 (\226\136\128 a, <pers> \206\168 a).
Time Proof.
Time (apply (anti_symm _); auto using persistently_forall_2).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (forall_elim x).
Time Qed.
Time
Lemma persistently_exist {A} (\206\168 : A \226\134\146 PROP) :
  <pers> (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, <pers> \206\168 a).
Time Proof.
Time (apply (anti_symm _); auto using persistently_exist_1).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>x).
Time by rewrite (exist_intro x).
Time Qed.
Time Lemma persistently_and P Q : <pers> (P \226\136\167 Q) \226\138\163\226\138\162 <pers> P \226\136\167 <pers> Q.
Time Proof.
Time rewrite !and_alt persistently_forall.
Time by <ssreflect_plugin::ssrtclintros@0> apply forall_proper =>- [].
Time Qed.
Time Lemma persistently_or P Q : <pers> (P \226\136\168 Q) \226\138\163\226\138\162 <pers> P \226\136\168 <pers> Q.
Time Proof.
Time rewrite !or_alt persistently_exist.
Time by <ssreflect_plugin::ssrtclintros@0> apply exist_proper =>- [].
Time Qed.
Time Lemma persistently_impl P Q : <pers> (P \226\134\146 Q) \226\138\162 <pers> P \226\134\146 <pers> Q.
Time Proof.
Time (apply impl_intro_l; rewrite -persistently_and).
Time (apply persistently_mono, impl_elim with P; auto).
Time Qed.
Time Lemma persistently_emp_intro P : P \226\138\162 <pers> emp.
Time Proof.
Time
by rewrite -(left_id emp%I bi_sep P) {+1}persistently_emp_2
 persistently_absorbing.
Time Qed.
Time Lemma persistently_True_emp : <pers> True \226\138\163\226\138\162 <pers> emp.
Time Proof.
Time (apply (anti_symm _); auto using persistently_emp_intro).
Time Qed.
Time Lemma persistently_and_emp P : <pers> P \226\138\163\226\138\162 <pers> (emp \226\136\167 P).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm (\226\138\162)) ; last  by rewrite
 and_elim_r).
Time rewrite persistently_and.
Time (<ssreflect_plugin::ssrtclseq@0> apply and_intro ; last  done).
Time (apply persistently_emp_intro).
Time Qed.
Time Lemma persistently_and_sep_elim_emp P Q : <pers> P \226\136\167 Q \226\138\162 (emp \226\136\167 P) \226\136\151 Q.
Time Proof.
Time rewrite persistently_and_emp.
Time (apply persistently_and_sep_elim).
Time Qed.
Time
Lemma persistently_and_sep_assoc P Q R :
  <pers> P \226\136\167 Q \226\136\151 R \226\138\163\226\138\162 (<pers> P \226\136\167 Q) \226\136\151 R.
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time rewrite {+1}persistently_idemp_2 persistently_and_sep_elim_emp assoc.
Time (apply sep_mono_l, and_intro).
Time +
Time by rewrite and_elim_r persistently_absorbing.
Time +
Time by rewrite and_elim_l left_id.
Time -
Time (apply and_intro).
Time +
Time by rewrite and_elim_l persistently_absorbing.
Time +
Time by rewrite and_elim_r.
Time Qed.
Time Lemma persistently_and_emp_elim P : emp \226\136\167 <pers> P \226\138\162 P.
Time Proof.
Time by rewrite comm persistently_and_sep_elim_emp right_id and_elim_r.
Time Qed.
Time Lemma persistently_into_absorbingly P : <pers> P \226\138\162 <absorb> P.
Time Proof.
Time rewrite -(right_id True%I _ (<pers> _)%I) -{+1}(emp_sep True%I).
Time
rewrite persistently_and_sep_assoc (comm bi_and) persistently_and_emp_elim
 comm //.
Time Qed.
Time Lemma persistently_elim P `{!Absorbing P} : <pers> P \226\138\162 P.
Time Proof.
Time by rewrite persistently_into_absorbingly absorbing_absorbingly.
Time Qed.
Time Lemma persistently_idemp_1 P : <pers> <pers> P \226\138\162 <pers> P.
Time Proof.
Time by rewrite persistently_into_absorbingly absorbingly_elim_persistently.
Time Qed.
Time Lemma persistently_idemp P : <pers> <pers> P \226\138\163\226\138\162 <pers> P.
Time Proof.
Time
(apply (anti_symm _); auto using persistently_idemp_1, persistently_idemp_2).
Time Qed.
Time Lemma persistently_intro' P Q : (<pers> P \226\138\162 Q) \226\134\146 <pers> P \226\138\162 <pers> Q.
Time Proof.
Time (intros <-).
Time (apply persistently_idemp_2).
Time Qed.
Time Lemma persistently_pure \207\134 : <pers> \226\140\156\207\134\226\140\157 \226\138\163\226\138\162 \226\140\156\207\134\226\140\157.
Time Proof.
Time (apply (anti_symm _)).
Time {
Time by rewrite persistently_into_absorbingly absorbingly_pure.
Time }
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim' =>H\207\134).
Time
(trans (\226\136\128 x : False, <pers> True : PROP)%I; [ by apply forall_intro |  ]).
Time rewrite persistently_forall_2.
Time auto using persistently_mono, pure_intro.
Time Qed.
Time Lemma persistently_sep_dup P : <pers> P \226\138\163\226\138\162 <pers> P \226\136\151 <pers> P.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time rewrite -{+1}(idemp bi_and (<pers> _)%I).
Time
by rewrite -{+2}(emp_sep (<pers> _)%I) persistently_and_sep_assoc and_elim_l.
Time -
Time by rewrite persistently_absorbing.
Time Qed.
Time Lemma persistently_and_sep_l_1 P Q : <pers> P \226\136\167 Q \226\138\162 <pers> P \226\136\151 Q.
Time Proof.
Time by rewrite -{+1}(emp_sep Q%I) persistently_and_sep_assoc and_elim_l.
Time Qed.
Time Lemma persistently_and_sep_r_1 P Q : P \226\136\167 <pers> Q \226\138\162 P \226\136\151 <pers> Q.
Time Proof.
Time by rewrite !(comm _ P) persistently_and_sep_l_1.
Time Qed.
Time Lemma persistently_and_sep P Q : <pers> (P \226\136\167 Q) \226\138\162 <pers> (P \226\136\151 Q).
Time Proof.
Time rewrite persistently_and.
Time rewrite -{+1}persistently_idemp -persistently_and -{+1}(emp_sep Q%I).
Time
by rewrite persistently_and_sep_assoc (comm bi_and) persistently_and_emp_elim.
Time Qed.
Time Lemma persistently_affinely_elim P : <pers> <affine> P \226\138\163\226\138\162 <pers> P.
Time Proof.
Time
by rewrite /bi_affinely persistently_and -persistently_True_emp
 persistently_pure left_id.
Time Qed.
Time
Lemma and_sep_persistently P Q : <pers> P \226\136\167 <pers> Q \226\138\163\226\138\162 <pers> P \226\136\151 <pers> Q.
Time Proof.
Time (apply (anti_symm _); auto using persistently_and_sep_l_1).
Time (apply and_intro).
Time -
Time by rewrite persistently_absorbing.
Time -
Time by rewrite comm persistently_absorbing.
Time Qed.
Time Lemma persistently_sep_2 P Q : <pers> P \226\136\151 <pers> Q \226\138\162 <pers> (P \226\136\151 Q).
Time Proof.
Time by rewrite -persistently_and_sep persistently_and -and_sep_persistently.
Time Qed.
Time
Lemma persistently_sep `{BiPositive PROP} P Q :
  <pers> (P \226\136\151 Q) \226\138\163\226\138\162 <pers> P \226\136\151 <pers> Q.
Time Proof.
Time (apply (anti_symm _); auto using persistently_sep_2).
Time rewrite -persistently_affinely_elim affinely_sep -and_sep_persistently.
Time (apply and_intro).
Time -
Time by rewrite (affinely_elim_emp Q) right_id affinely_elim.
Time -
Time by rewrite (affinely_elim_emp P) left_id affinely_elim.
Time Qed.
Time Lemma persistently_alt_fixpoint P : <pers> P \226\138\163\226\138\162 P \226\136\151 <pers> P.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time rewrite -persistently_and_sep_elim.
Time (apply and_intro; done).
Time -
Time rewrite comm persistently_absorbing.
Time done.
Time Qed.
Time Lemma persistently_alt_fixpoint' P : <pers> P \226\138\163\226\138\162 <affine> P \226\136\151 <pers> P.
Time Proof.
Time
rewrite -{+1}persistently_affinely_elim {+1}persistently_alt_fixpoint
 persistently_affinely_elim //.
Time Qed.
Time Lemma persistently_wand P Q : <pers> (P -\226\136\151 Q) \226\138\162 <pers> P -\226\136\151 <pers> Q.
Time Proof.
Time (apply wand_intro_r).
Time by rewrite persistently_sep_2 wand_elim_l.
Time Qed.
Time Lemma persistently_entails_l P Q : (P \226\138\162 <pers> Q) \226\134\146 P \226\138\162 <pers> Q \226\136\151 P.
Time Proof.
Time (intros; rewrite -persistently_and_sep_l_1; auto).
Time Qed.
Time Lemma persistently_entails_r P Q : (P \226\138\162 <pers> Q) \226\134\146 P \226\138\162 P \226\136\151 <pers> Q.
Time Proof.
Time (intros; rewrite -persistently_and_sep_r_1; auto).
Time Qed.
Time Lemma persistently_impl_wand_2 P Q : <pers> (P -\226\136\151 Q) \226\138\162 <pers> (P \226\134\146 Q).
Time Proof.
Time (apply persistently_intro', impl_intro_r).
Time rewrite -{+2}(emp_sep P%I) persistently_and_sep_assoc.
Time by rewrite (comm bi_and) persistently_and_emp_elim wand_elim_l.
Time Qed.
Time Lemma impl_wand_persistently_2 P Q : (<pers> P -\226\136\151 Q) \226\138\162 <pers> P \226\134\146 Q.
Time Proof.
Time (apply impl_intro_l).
Time by rewrite persistently_and_sep_l_1 wand_elim_r.
Time Qed.
Time Section persistently_affine_bi.
Time Context `{BiAffine PROP}.
Time Lemma persistently_emp : <pers> emp \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite -!True_emp persistently_pure.
Time Qed.
Time Lemma persistently_and_sep_l P Q : <pers> P \226\136\167 Q \226\138\163\226\138\162 <pers> P \226\136\151 Q.
Time Proof.
Time
(apply (anti_symm (\226\138\162)); eauto using persistently_and_sep_l_1, sep_and
  with typeclass_instances).
Time Qed.
Time Lemma persistently_and_sep_r P Q : P \226\136\167 <pers> Q \226\138\163\226\138\162 P \226\136\151 <pers> Q.
Time Proof.
Time by rewrite !(comm _ P) persistently_and_sep_l.
Time Qed.
Time Lemma persistently_impl_wand P Q : <pers> (P \226\134\146 Q) \226\138\163\226\138\162 <pers> (P -\226\136\151 Q).
Time Proof.
Time (apply (anti_symm (\226\138\162)); auto using persistently_impl_wand_2).
Time (apply persistently_intro', wand_intro_l).
Time by rewrite -persistently_and_sep_r persistently_elim impl_elim_r.
Time Qed.
Time Lemma impl_wand_persistently P Q : (<pers> P \226\134\146 Q) \226\138\163\226\138\162 (<pers> P -\226\136\151 Q).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time by rewrite -impl_wand_1.
Time (apply impl_wand_persistently_2).
Time Qed.
Time Lemma wand_alt P Q : (P -\226\136\151 Q) \226\138\163\226\138\162 (\226\136\131 R, R \226\136\151 <pers> (P \226\136\151 R \226\134\146 Q)).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time rewrite -(right_id True%I bi_sep (P -\226\136\151 Q)%I) -(exist_intro (P -\226\136\151 Q)%I).
Time (apply sep_mono_r).
Time rewrite -persistently_pure.
Time (apply persistently_intro', impl_intro_l).
Time by rewrite wand_elim_r persistently_pure right_id.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>R).
Time (apply wand_intro_l).
Time rewrite assoc -persistently_and_sep_r.
Time by rewrite persistently_elim impl_elim_r.
Time Qed.
Time End persistently_affine_bi.
Time #[global]
Instance intuitionistically_ne : (NonExpansive (@bi_intuitionistically PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance intuitionistically_proper :
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_intuitionistically PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance intuitionistically_mono' :
 (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_intuitionistically PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance intuitionistically_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_intuitionistically PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma intuitionistically_elim P : \226\150\161 P \226\138\162 P.
Time Proof.
Time (apply persistently_and_emp_elim).
Time Qed.
Time Lemma intuitionistically_elim_emp P : \226\150\161 P \226\138\162 emp.
Time Proof.
Time rewrite /bi_intuitionistically affinely_elim_emp //.
Time Qed.
Time Lemma intuitionistically_intro' P Q : (\226\150\161 P \226\138\162 Q) \226\134\146 \226\150\161 P \226\138\162 \226\150\161 Q.
Time Proof.
Time (intros <-).
Time
by rewrite /bi_intuitionistically persistently_affinely_elim
 persistently_idemp.
Time Qed.
Time Lemma intuitionistically_emp : \226\150\161 emp \226\138\163\226\138\162 emp.
Time Proof.
Time
by rewrite /bi_intuitionistically -persistently_True_emp persistently_pure
 affinely_True_emp affinely_emp.
Time Qed.
Time Lemma intuitionistically_False : \226\150\161 False \226\138\163\226\138\162 False.
Time Proof.
Time by rewrite /bi_intuitionistically persistently_pure affinely_False.
Time Qed.
Time Lemma intuitionistically_True_emp : \226\150\161 True \226\138\163\226\138\162 emp.
Time Proof.
Time
rewrite -intuitionistically_emp /bi_intuitionistically persistently_True_emp
 //.
Time Qed.
Time Lemma intuitionistically_and P Q : \226\150\161 (P \226\136\167 Q) \226\138\163\226\138\162 \226\150\161 P \226\136\167 \226\150\161 Q.
Time Proof.
Time by rewrite /bi_intuitionistically persistently_and affinely_and.
Time Qed.
Time
Lemma intuitionistically_forall {A} (\206\166 : A \226\134\146 PROP) :
  \226\150\161 (\226\136\128 x, \206\166 x) \226\138\162 \226\136\128 x, \226\150\161 \206\166 x.
Time Proof.
Time by rewrite /bi_intuitionistically persistently_forall affinely_forall.
Time Qed.
Time Lemma intuitionistically_or P Q : \226\150\161 (P \226\136\168 Q) \226\138\163\226\138\162 \226\150\161 P \226\136\168 \226\150\161 Q.
Time Proof.
Time by rewrite /bi_intuitionistically persistently_or affinely_or.
Time Qed.
Time
Lemma intuitionistically_exist {A} (\206\166 : A \226\134\146 PROP) :
  \226\150\161 (\226\136\131 x, \206\166 x) \226\138\163\226\138\162 (\226\136\131 x, \226\150\161 \206\166 x).
Time Proof.
Time by rewrite /bi_intuitionistically persistently_exist affinely_exist.
Time Qed.
Time Lemma intuitionistically_sep_2 P Q : \226\150\161 P \226\136\151 \226\150\161 Q \226\138\162 \226\150\161 (P \226\136\151 Q).
Time Proof.
Time by rewrite /bi_intuitionistically affinely_sep_2 persistently_sep_2.
Time Qed.
Time
Lemma intuitionistically_sep `{BiPositive PROP} P Q : \226\150\161 (P \226\136\151 Q) \226\138\163\226\138\162 \226\150\161 P \226\136\151 \226\150\161 Q.
Time Proof.
Time by rewrite /bi_intuitionistically -affinely_sep -persistently_sep.
Time Qed.
Time Lemma intuitionistically_idemp P : \226\150\161 \226\150\161 P \226\138\163\226\138\162 \226\150\161 P.
Time Proof.
Time
by rewrite /bi_intuitionistically persistently_affinely_elim
 persistently_idemp.
Time Qed.
Time Lemma intuitionistically_into_persistently_1 P : \226\150\161 P \226\138\162 <pers> P.
Time Proof.
Time rewrite /bi_intuitionistically affinely_elim //.
Time Qed.
Time Lemma intuitionistically_persistently_elim P : \226\150\161 <pers> P \226\138\163\226\138\162 \226\150\161 P.
Time Proof.
Time rewrite /bi_intuitionistically persistently_idemp //.
Time Qed.
Time
Lemma intuitionistic_intuitionistically P :
  Affine P \226\134\146 Persistent P \226\134\146 \226\150\161 P \226\138\163\226\138\162 P.
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm _) ; first  exact
 : {}intuitionistically_elim {}).
Time rewrite -{+1}(affine_affinely P) {+1}(persistent P) //.
Time Qed.
Time Lemma intuitionistically_affinely P : \226\150\161 P \226\138\162 <affine> P.
Time Proof.
Time rewrite /bi_intuitionistically /bi_affinely.
Time (apply and_intro).
Time -
Time rewrite and_elim_l //.
Time -
Time (apply persistently_and_emp_elim).
Time Qed.
Time Lemma intuitionistically_affinely_elim P : \226\150\161 <affine> P \226\138\163\226\138\162 \226\150\161 P.
Time Proof.
Time rewrite /bi_intuitionistically persistently_affinely_elim //.
Time Qed.
Time
Lemma persistently_and_intuitionistically_sep_l P Q : <pers> P \226\136\167 Q \226\138\163\226\138\162 \226\150\161 P \226\136\151 Q.
Time Proof.
Time rewrite /bi_intuitionistically.
Time (apply (anti_symm _)).
Time -
Time
by rewrite /bi_affinely -(comm bi_and (<pers> P)%I)
 -persistently_and_sep_assoc left_id.
Time -
Time (apply and_intro).
Time +
Time by rewrite affinely_elim persistently_absorbing.
Time +
Time by rewrite affinely_elim_emp left_id.
Time Qed.
Time
Lemma persistently_and_intuitionistically_sep_r P Q : P \226\136\167 <pers> Q \226\138\163\226\138\162 P \226\136\151 \226\150\161 Q.
Time Proof.
Time by rewrite !(comm _ P) persistently_and_intuitionistically_sep_l.
Time Qed.
Time Lemma and_sep_intuitionistically P Q : \226\150\161 P \226\136\167 \226\150\161 Q \226\138\163\226\138\162 \226\150\161 P \226\136\151 \226\150\161 Q.
Time Proof.
Time
by rewrite -persistently_and_intuitionistically_sep_l -affinely_and
 affinely_and_r.
Time Qed.
Time Lemma intuitionistically_sep_dup P : \226\150\161 P \226\138\163\226\138\162 \226\150\161 P \226\136\151 \226\150\161 P.
Time Proof.
Time
by rewrite -persistently_and_intuitionistically_sep_l affinely_and_r idemp.
Time Qed.
Time Lemma impl_wand_intuitionistically P Q : (<pers> P \226\134\146 Q) \226\138\163\226\138\162 (\226\150\161 P -\226\136\151 Q).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time (apply wand_intro_l).
Time by rewrite -persistently_and_intuitionistically_sep_l impl_elim_r.
Time -
Time (apply impl_intro_l).
Time by rewrite persistently_and_intuitionistically_sep_l wand_elim_r.
Time Qed.
Time Lemma intuitionistically_alt_fixpoint P : \226\150\161 P \226\138\163\226\138\162 emp \226\136\167 P \226\136\151 \226\150\161 P.
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> apply and_intro ; first  exact
 : {}affinely_elim_emp {}).
Time rewrite {+1}intuitionistically_sep_dup.
Time (<ssreflect_plugin::ssrtclseq@0> apply sep_mono ; last  done).
Time (apply intuitionistically_elim).
Time -
Time (<ssreflect_plugin::ssrtclseq@0> apply and_mono ; first  done).
Time rewrite /bi_intuitionistically {+2}persistently_alt_fixpoint.
Time (<ssreflect_plugin::ssrtclseq@0> apply sep_mono ; first  done).
Time (apply and_elim_r).
Time Qed.
Time Lemma impl_alt P Q : (P \226\134\146 Q) \226\138\163\226\138\162 (\226\136\131 R, R \226\136\167 <pers> (P \226\136\167 R -\226\136\151 Q)).
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time -
Time rewrite -(right_id True%I bi_and (P \226\134\146 Q)%I) -(exist_intro (P \226\134\146 Q)%I).
Time (apply and_mono_r).
Time rewrite impl_elim_r -entails_wand //.
Time (apply persistently_emp_intro).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>R).
Time (apply impl_intro_l).
Time rewrite assoc persistently_and_intuitionistically_sep_r.
Time by rewrite intuitionistically_elim wand_elim_r.
Time Qed.
Time Section bi_affine_intuitionistically.
Time Context `{BiAffine PROP}.
Time Lemma intuitionistically_into_persistently P : \226\150\161 P \226\138\163\226\138\162 <pers> P.
Time Proof.
Time rewrite /bi_intuitionistically affine_affinely //.
Time Qed.
Time End bi_affine_intuitionistically.
Time #[global]
Instance affinely_if_ne  p: (NonExpansive (@bi_affinely_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance affinely_if_proper  p:
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_affinely_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance affinely_if_mono'  p:
 (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_affinely_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance affinely_if_flip_mono'  p:
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_affinely_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma affinely_if_mono p P Q : (P \226\138\162 Q) \226\134\146 <affine>?p P \226\138\162 <affine>?p Q.
Time Proof.
Time by intros ->.
Time Qed.
Time
Lemma affinely_if_flag_mono (p q : bool) P :
  (q \226\134\146 p) \226\134\146 <affine>?p P \226\138\162 <affine>?q P.
Time Proof.
Time (destruct p, q; naive_solver auto using affinely_elim).
Time Qed.
Time Lemma affinely_if_elim p P : <affine>?p P \226\138\162 P.
Time Proof.
Time (destruct p; simpl; auto using affinely_elim).
Time Qed.
Time Lemma affinely_affinely_if p P : <affine> P \226\138\162 <affine>?p P.
Time Proof.
Time (destruct p; simpl; auto using affinely_elim).
Time Qed.
Time
Lemma affinely_if_intro' p P Q :
  (<affine>?p P \226\138\162 Q) \226\134\146 <affine>?p P \226\138\162 <affine>?p Q.
Time Proof.
Time (destruct p; simpl; auto using affinely_intro').
Time Qed.
Time Lemma affinely_if_emp p : <affine>?p emp \226\138\163\226\138\162 emp.
Time Proof.
Time (destruct p; simpl; auto using affinely_emp).
Time Qed.
Time
Lemma affinely_if_and p P Q :
  <affine>?p (P \226\136\167 Q) \226\138\163\226\138\162 <affine>?p P \226\136\167 <affine>?p Q.
Time Proof.
Time (destruct p; simpl; auto using affinely_and).
Time Qed.
Time
Lemma affinely_if_or p P Q :
  <affine>?p (P \226\136\168 Q) \226\138\163\226\138\162 <affine>?p P \226\136\168 <affine>?p Q.
Time Proof.
Time (destruct p; simpl; auto using affinely_or).
Time Qed.
Time
Lemma affinely_if_exist {A} p (\206\168 : A \226\134\146 PROP) :
  <affine>?p (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, <affine>?p \206\168 a).
Time Proof.
Time (destruct p; simpl; auto using affinely_exist).
Time Qed.
Time
Lemma affinely_if_sep_2 p P Q :
  <affine>?p P \226\136\151 <affine>?p Q \226\138\162 <affine>?p (P \226\136\151 Q).
Time Proof.
Time (destruct p; simpl; auto using affinely_sep_2).
Time Qed.
Time
Lemma affinely_if_sep `{BiPositive PROP} p P Q :
  <affine>?p (P \226\136\151 Q) \226\138\163\226\138\162 <affine>?p P \226\136\151 <affine>?p Q.
Time Proof.
Time (destruct p; simpl; auto using affinely_sep).
Time Qed.
Time Lemma affinely_if_idemp p P : <affine>?p <affine>?p P \226\138\163\226\138\162 <affine>?p P.
Time Proof.
Time (destruct p; simpl; auto using affinely_idemp).
Time Qed.
Time Lemma affinely_if_and_l p P Q : <affine>?p P \226\136\167 Q \226\138\163\226\138\162 <affine>?p (P \226\136\167 Q).
Time Proof.
Time (destruct p; simpl; auto using affinely_and_l).
Time Qed.
Time Lemma affinely_if_and_r p P Q : P \226\136\167 <affine>?p Q \226\138\163\226\138\162 <affine>?p (P \226\136\167 Q).
Time Proof.
Time (destruct p; simpl; auto using affinely_and_r).
Time Qed.
Time Lemma affinely_if_and_lr p P Q : <affine>?p P \226\136\167 Q \226\138\163\226\138\162 P \226\136\167 <affine>?p Q.
Time Proof.
Time (destruct p; simpl; auto using affinely_and_lr).
Time Qed.
Time #[global]
Instance absorbingly_if_ne  p: (NonExpansive (@bi_absorbingly_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance absorbingly_if_proper  p:
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_absorbingly_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance absorbingly_if_mono'  p:
 (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_absorbingly_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance absorbingly_if_flip_mono'  p:
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_absorbingly_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma absorbingly_if_absorbingly p P : <absorb>?p P \226\138\162 <absorb> P.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_intro).
Time Qed.
Time Lemma absorbingly_if_intro p P : P \226\138\162 <absorb>?p P.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_intro).
Time Qed.
Time Lemma absorbingly_if_mono p P Q : (P \226\138\162 Q) \226\134\146 <absorb>?p P \226\138\162 <absorb>?p Q.
Time Proof.
Time by intros ->.
Time Qed.
Time
Lemma absorbingly_if_flag_mono (p q : bool) P :
  (p \226\134\146 q) \226\134\146 <absorb>?p P \226\138\162 <absorb>?q P.
Time Proof.
Time (destruct p, q; try naive_solver auto using absorbingly_intro).
Time Qed.
Time
Lemma absorbingly_if_idemp p P : <absorb>?p <absorb>?p P \226\138\163\226\138\162 <absorb>?p P.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_idemp).
Time Qed.
Time Lemma absorbingly_if_pure p \207\134 : <absorb>?p \226\140\156\207\134\226\140\157 \226\138\163\226\138\162 \226\140\156\207\134\226\140\157.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_pure).
Time Qed.
Time
Lemma absorbingly_if_or p P Q :
  <absorb>?p (P \226\136\168 Q) \226\138\163\226\138\162 <absorb>?p P \226\136\168 <absorb>?p Q.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_or).
Time Qed.
Time
Lemma absorbingly_if_and_1 p P Q :
  <absorb>?p (P \226\136\167 Q) \226\138\162 <absorb>?p P \226\136\167 <absorb>?p Q.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_and_1).
Time Qed.
Time
Lemma absorbingly_if_forall {A} p (\206\166 : A \226\134\146 PROP) :
  <absorb>?p (\226\136\128 a, \206\166 a) \226\138\162 \226\136\128 a, <absorb>?p \206\166 a.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_forall).
Time Qed.
Time
Lemma absorbingly_if_exist {A} p (\206\166 : A \226\134\146 PROP) :
  <absorb>?p (\226\136\131 a, \206\166 a) \226\138\163\226\138\162 (\226\136\131 a, <absorb>?p \206\166 a).
Time Proof.
Time (destruct p; simpl; auto using absorbingly_exist).
Time Qed.
Time
Lemma absorbingly_if_sep p P Q :
  <absorb>?p (P \226\136\151 Q) \226\138\163\226\138\162 <absorb>?p P \226\136\151 <absorb>?p Q.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_sep).
Time Qed.
Time
Lemma absorbingly_if_wand p P Q :
  <absorb>?p (P -\226\136\151 Q) \226\138\162 <absorb>?p P -\226\136\151 <absorb>?p Q.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_wand).
Time Qed.
Time
Lemma absorbingly_if_sep_l p P Q : <absorb>?p P \226\136\151 Q \226\138\163\226\138\162 <absorb>?p (P \226\136\151 Q).
Time Proof.
Time (destruct p; simpl; auto using absorbingly_sep_l).
Time Qed.
Time
Lemma absorbingly_if_sep_r p P Q : P \226\136\151 <absorb>?p Q \226\138\163\226\138\162 <absorb>?p (P \226\136\151 Q).
Time Proof.
Time (destruct p; simpl; auto using absorbingly_sep_r).
Time Qed.
Time
Lemma absorbingly_if_sep_lr p P Q : <absorb>?p P \226\136\151 Q \226\138\163\226\138\162 P \226\136\151 <absorb>?p Q.
Time Proof.
Time (destruct p; simpl; auto using absorbingly_sep_lr).
Time Qed.
Time
Lemma affinely_if_absorbingly_if_elim `{!BiPositive PROP} 
  p P : <affine>?p <absorb>?p P \226\138\163\226\138\162 <affine>?p P.
Time Proof.
Time (destruct p; simpl; auto using affinely_absorbingly_elim).
Time Qed.
Time #[global]
Instance persistently_if_ne  p: (NonExpansive (@bi_persistently_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance persistently_if_proper  p:
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_persistently_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance persistently_if_mono'  p:
 (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_persistently_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance persistently_if_flip_mono'  p:
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_persistently_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma persistently_if_mono p P Q : (P \226\138\162 Q) \226\134\146 <pers>?p P \226\138\162 <pers>?p Q.
Time Proof.
Time by intros ->.
Time Qed.
Time Lemma persistently_if_pure p \207\134 : <pers>?p \226\140\156\207\134\226\140\157 \226\138\163\226\138\162 \226\140\156\207\134\226\140\157.
Time Proof.
Time (destruct p; simpl; auto using persistently_pure).
Time Qed.
Time
Lemma persistently_if_and p P Q : <pers>?p (P \226\136\167 Q) \226\138\163\226\138\162 <pers>?p P \226\136\167 <pers>?p Q.
Time Proof.
Time (destruct p; simpl; auto using persistently_and).
Time Qed.
Time
Lemma persistently_if_or p P Q : <pers>?p (P \226\136\168 Q) \226\138\163\226\138\162 <pers>?p P \226\136\168 <pers>?p Q.
Time Proof.
Time (destruct p; simpl; auto using persistently_or).
Time Qed.
Time
Lemma persistently_if_exist {A} p (\206\168 : A \226\134\146 PROP) :
  <pers>?p (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, <pers>?p \206\168 a).
Time Proof.
Time (destruct p; simpl; auto using persistently_exist).
Time Qed.
Time
Lemma persistently_if_sep_2 p P Q :
  <pers>?p P \226\136\151 <pers>?p Q \226\138\162 <pers>?p (P \226\136\151 Q).
Time Proof.
Time (destruct p; simpl; auto using persistently_sep_2).
Time Qed.
Time
Lemma persistently_if_sep `{BiPositive PROP} p P Q :
  <pers>?p (P \226\136\151 Q) \226\138\163\226\138\162 <pers>?p P \226\136\151 <pers>?p Q.
Time Proof.
Time (destruct p; simpl; auto using persistently_sep).
Time Qed.
Time Lemma persistently_if_idemp p P : <pers>?p <pers>?p P \226\138\163\226\138\162 <pers>?p P.
Time Proof.
Time (destruct p; simpl; auto using persistently_idemp).
Time Qed.
Time #[global]
Instance intuitionistically_if_ne  p:
 (NonExpansive (@bi_intuitionistically_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance intuitionistically_if_proper  p:
 (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_intuitionistically_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance intuitionistically_if_mono'  p:
 (Proper ((\226\138\162) ==> (\226\138\162)) (@bi_intuitionistically_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance intuitionistically_if_flip_mono'  p:
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@bi_intuitionistically_if PROP p)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma intuitionistically_if_mono p P Q : (P \226\138\162 Q) \226\134\146 \226\150\161?p P \226\138\162 \226\150\161?p Q.
Time Proof.
Time by intros ->.
Time Qed.
Time
Lemma intuitionistically_if_flag_mono (p q : bool) 
  P : (q \226\134\146 p) \226\134\146 \226\150\161?p P \226\138\162 \226\150\161?q P.
Time Proof.
Time (destruct p, q; naive_solver auto using intuitionistically_elim).
Time Qed.
Time Lemma intuitionistically_if_elim p P : \226\150\161?p P \226\138\162 P.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_elim).
Time Qed.
Time Lemma intuitionistically_intuitionistically_if p P : \226\150\161 P \226\138\162 \226\150\161?p P.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_elim).
Time Qed.
Time Lemma intuitionistically_if_intro' p P Q : (\226\150\161?p P \226\138\162 Q) \226\134\146 \226\150\161?p P \226\138\162 \226\150\161?p Q.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_intro').
Time Qed.
Time Lemma intuitionistically_if_emp p : \226\150\161?p emp \226\138\163\226\138\162 emp.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_emp).
Time Qed.
Time Lemma intuitionistically_if_False p : \226\150\161?p False \226\138\163\226\138\162 False.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_False).
Time Qed.
Time Lemma intuitionistically_if_and p P Q : \226\150\161?p (P \226\136\167 Q) \226\138\163\226\138\162 \226\150\161?p P \226\136\167 \226\150\161?p Q.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_and).
Time Qed.
Time Lemma intuitionistically_if_or p P Q : \226\150\161?p (P \226\136\168 Q) \226\138\163\226\138\162 \226\150\161?p P \226\136\168 \226\150\161?p Q.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_or).
Time Qed.
Time
Lemma intuitionistically_if_exist {A} p (\206\168 : A \226\134\146 PROP) :
  \226\150\161?p (\226\136\131 a, \206\168 a) \226\138\163\226\138\162 (\226\136\131 a, \226\150\161?p \206\168 a).
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_exist).
Time Qed.
Time Lemma intuitionistically_if_sep_2 p P Q : \226\150\161?p P \226\136\151 \226\150\161?p Q \226\138\162 \226\150\161?p (P \226\136\151 Q).
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_sep_2).
Time Qed.
Time
Lemma intuitionistically_if_sep `{BiPositive PROP} 
  p P Q : \226\150\161?p (P \226\136\151 Q) \226\138\163\226\138\162 \226\150\161?p P \226\136\151 \226\150\161?p Q.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_sep).
Time Qed.
Time Lemma intuitionistically_if_idemp p P : \226\150\161?p \226\150\161?p P \226\138\163\226\138\162 \226\150\161?p P.
Time Proof.
Time (destruct p; simpl; auto using intuitionistically_idemp).
Time Qed.
Time Lemma intuitionistically_if_unfold p P : \226\150\161?p P \226\138\163\226\138\162 <affine>?p <pers>?p P.
Time Proof.
Time by destruct p.
Time Qed.
Time #[global]
Instance Persistent_proper : (Proper ((\226\137\161) ==> iff) (@Persistent PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma persistent_persistently_2 P `{!Persistent P} : P \226\138\162 <pers> P.
Time Proof.
Time done.
Time Qed.
Time
Lemma persistent_persistently P `{!Persistent P} `{!Absorbing P} :
  <pers> P \226\138\163\226\138\162 P.
Time Proof.
Time
(apply (anti_symm _); auto using persistent_persistently_2, persistently_elim).
Time Qed.
Time Lemma persistently_intro P Q `{!Persistent P} : (P \226\138\162 Q) \226\134\146 P \226\138\162 <pers> Q.
Time Proof.
Time (intros HP).
Time by rewrite (persistent P) HP.
Time Qed.
Time
Lemma persistent_and_affinely_sep_l_1 P Q `{!Persistent P} :
  P \226\136\167 Q \226\138\162 <affine> P \226\136\151 Q.
Time Proof.
Time
rewrite {+1}(persistent_persistently_2 P)
 persistently_and_intuitionistically_sep_l.
Time rewrite intuitionistically_affinely //.
Time Qed.
Time
Lemma persistent_and_affinely_sep_r_1 P Q `{!Persistent Q} :
  P \226\136\167 Q \226\138\162 P \226\136\151 <affine> Q.
Time Proof.
Time by rewrite !(comm _ P) persistent_and_affinely_sep_l_1.
Time Qed.
Time
Lemma persistent_and_affinely_sep_l P Q `{!Persistent P} 
  `{!Absorbing P} : P \226\136\167 Q \226\138\163\226\138\162 <affine> P \226\136\151 Q.
Time Proof.
Time
by rewrite -(persistent_persistently P)
 persistently_and_intuitionistically_sep_l.
Time Qed.
Time
Lemma persistent_and_affinely_sep_r P Q `{!Persistent Q} 
  `{!Absorbing Q} : P \226\136\167 Q \226\138\163\226\138\162 P \226\136\151 <affine> Q.
Time Proof.
Time
by rewrite -(persistent_persistently Q)
 persistently_and_intuitionistically_sep_r.
Time Qed.
Time
Lemma persistent_and_sep_1 P Q `{HPQ : !TCOr (Persistent P) (Persistent Q)} :
  P \226\136\167 Q \226\138\162 P \226\136\151 Q.
Time Proof.
Time (destruct HPQ).
Time -
Time by rewrite persistent_and_affinely_sep_l_1 affinely_elim.
Time -
Time by rewrite persistent_and_affinely_sep_r_1 affinely_elim.
Time Qed.
Time
Lemma persistent_sep_dup P `{!Persistent P} `{!Absorbing P} : P \226\138\163\226\138\162 P \226\136\151 P.
Time Proof.
Time by rewrite -(persistent_persistently P) -persistently_sep_dup.
Time Qed.
Time Lemma persistent_entails_l P Q `{!Persistent Q} : (P \226\138\162 Q) \226\134\146 P \226\138\162 Q \226\136\151 P.
Time Proof.
Time (intros).
Time (rewrite -persistent_and_sep_1; auto).
Time Qed.
Time Lemma persistent_entails_r P Q `{!Persistent Q} : (P \226\138\162 Q) \226\134\146 P \226\138\162 P \226\136\151 Q.
Time Proof.
Time (intros).
Time (rewrite -persistent_and_sep_1; auto).
Time Qed.
Time
Lemma absorbingly_intuitionistically_into_persistently 
  P : <absorb> \226\150\161 P \226\138\163\226\138\162 <pers> P.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time
by rewrite intuitionistically_into_persistently_1
 absorbingly_elim_persistently.
Time -
Time
rewrite -{+1}(idemp bi_and (<pers> _)%I)
 persistently_and_intuitionistically_sep_r.
Time by rewrite {+1}(True_intro (<pers> _)%I).
Time Qed.
Time
Lemma persistent_absorbingly_affinely_2 P `{!Persistent P} :
  P \226\138\162 <absorb> <affine> P.
Time Proof.
Time
rewrite {+1}(persistent P) -absorbingly_intuitionistically_into_persistently.
Time by rewrite intuitionistically_affinely.
Time Qed.
Time
Lemma persistent_absorbingly_affinely P `{!Persistent P} 
  `{!Absorbing P} : <absorb> <affine> P \226\138\163\226\138\162 P.
Time Proof.
Time
by rewrite -(persistent_persistently P)
 absorbingly_intuitionistically_into_persistently.
Time Qed.
Time
Lemma persistent_and_sep_assoc P `{!Persistent P} 
  `{!Absorbing P} Q R : P \226\136\167 Q \226\136\151 R \226\138\163\226\138\162 (P \226\136\167 Q) \226\136\151 R.
Time Proof.
Time by rewrite -(persistent_persistently P) persistently_and_sep_assoc.
Time Qed.
Time Lemma impl_wand_2 P `{!Persistent P} Q : (P -\226\136\151 Q) \226\138\162 P \226\134\146 Q.
Time Proof.
Time (apply impl_intro_l).
Time by rewrite persistent_and_sep_1 wand_elim_r.
Time Qed.
Time Section persistent_bi_absorbing.
Time Context `{BiAffine PROP}.
Time
Lemma persistent_and_sep P Q `{HPQ : !TCOr (Persistent P) (Persistent Q)} :
  P \226\136\167 Q \226\138\163\226\138\162 P \226\136\151 Q.
Time Proof.
Time (destruct HPQ).
Time -
Time by rewrite -(persistent_persistently P) persistently_and_sep_l.
Time -
Time by rewrite -(persistent_persistently Q) persistently_and_sep_r.
Time Qed.
Time Lemma impl_wand P `{!Persistent P} Q : (P \226\134\146 Q) \226\138\163\226\138\162 (P -\226\136\151 Q).
Time Proof.
Time (apply (anti_symm _); auto using impl_wand_1, impl_wand_2).
Time Qed.
Time End persistent_bi_absorbing.
Time #[global]Instance emp_affine : (Affine (PROP:=PROP) emp).
Time Proof.
Time by rewrite /Affine.
Time Qed.
Time #[global]Instance False_affine : (Affine (PROP:=PROP) False).
Time Proof.
Time by rewrite /Affine False_elim.
Time Qed.
Time #[global]Instance and_affine_l  P Q: (Affine P \226\134\146 Affine (P \226\136\167 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Affine =>{+}->; auto).
Time Qed.
Time #[global]Instance and_affine_r  P Q: (Affine Q \226\134\146 Affine (P \226\136\167 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Affine =>{+}->; auto).
Time Qed.
Time #[global]
Instance or_affine  P Q: (Affine P \226\134\146 Affine Q \226\134\146 Affine (P \226\136\168 Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Affine =>{+}-> {+}->; auto).
Time Qed.
Time #[global]
Instance forall_affine  `{Inhabited A} (\206\166 : A \226\134\146 PROP):
 ((\226\136\128 x, Affine (\206\166 x)) \226\134\146 Affine (\226\136\128 x, \206\166 x)).
Time Proof.
Time (intros).
Time rewrite /Affine (forall_elim inhabitant).
Time apply : {}affine {}.
Time Qed.
Time #[global]
Instance exist_affine  {A} (\206\166 : A \226\134\146 PROP):
 ((\226\136\128 x, Affine (\206\166 x)) \226\134\146 Affine (\226\136\131 x, \206\166 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Affine =>H).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a).
Time by rewrite H.
Time Qed.
Time #[global]
Instance sep_affine  P Q: (Affine P \226\134\146 Affine Q \226\134\146 Affine (P \226\136\151 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Affine =>{+}-> {+}->).
Time by rewrite left_id.
Time Qed.
Time #[global]Instance affinely_affine  P: (Affine (<affine> P)).
Time Proof.
Time rewrite /bi_affinely.
Time (apply _).
Time Qed.
Time #[global]
Instance affinely_if_affine  p P: (Affine P \226\134\146 Affine (<affine>?p P)).
Time Proof.
Time (destruct p; simpl; apply _).
Time Qed.
Time #[global]Instance intuitionistically_affine  P: (Affine (\226\150\161 P)).
Time Proof.
Time rewrite /bi_intuitionistically.
Time (apply _).
Time Qed.
Time #[global]Instance pure_absorbing  \207\134: (Absorbing (PROP:=PROP) \226\140\156\207\134\226\140\157).
Time Proof.
Time by rewrite /Absorbing absorbingly_pure.
Time Qed.
Time #[global]
Instance and_absorbing  P Q: (Absorbing P \226\134\146 Absorbing Q \226\134\146 Absorbing (P \226\136\167 Q)).
Time Proof.
Time (intros).
Time by rewrite /Absorbing absorbingly_and_1 !absorbing.
Time Qed.
Time #[global]
Instance or_absorbing  P Q: (Absorbing P \226\134\146 Absorbing Q \226\134\146 Absorbing (P \226\136\168 Q)).
Time Proof.
Time (intros).
Time by rewrite /Absorbing absorbingly_or !absorbing.
Time Qed.
Time #[global]
Instance forall_absorbing  {A} (\206\166 : A \226\134\146 PROP):
 ((\226\136\128 x, Absorbing (\206\166 x)) \226\134\146 Absorbing (\226\136\128 x, \206\166 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Absorbing =>?).
Time rewrite absorbingly_forall.
Time auto using forall_mono.
Time Qed.
Time #[global]
Instance exist_absorbing  {A} (\206\166 : A \226\134\146 PROP):
 ((\226\136\128 x, Absorbing (\206\166 x)) \226\134\146 Absorbing (\226\136\131 x, \206\166 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Absorbing =>?).
Time rewrite absorbingly_exist.
Time auto using exist_mono.
Time Qed.
Time #[global]
Instance impl_absorbing  P Q:
 (Persistent P \226\134\146 Absorbing P \226\134\146 Absorbing Q \226\134\146 Absorbing (P \226\134\146 Q)).
Time Proof.
Time (intros).
Time rewrite /Absorbing.
Time (apply impl_intro_l).
Time rewrite persistent_and_affinely_sep_l_1 absorbingly_sep_r.
Time by rewrite -persistent_and_affinely_sep_l impl_elim_r.
Time Qed.
Time #[global]
Instance sep_absorbing_l  P Q: (Absorbing P \226\134\146 Absorbing (P \226\136\151 Q)).
Time Proof.
Time (intros).
Time by rewrite /Absorbing -absorbingly_sep_l absorbing.
Time Qed.
Time #[global]
Instance sep_absorbing_r  P Q: (Absorbing Q \226\134\146 Absorbing (P \226\136\151 Q)).
Time Proof.
Time (intros).
Time by rewrite /Absorbing -absorbingly_sep_r absorbing.
Time Qed.
Time #[global]
Instance wand_absorbing_l  P Q: (Absorbing P \226\134\146 Absorbing (P -\226\136\151 Q)).
Time Proof.
Time (intros).
Time rewrite /Absorbing /bi_absorbingly.
Time (apply wand_intro_l).
Time by rewrite assoc (sep_elim_l P) wand_elim_r.
Time Qed.
Time #[global]
Instance wand_absorbing_r  P Q: (Absorbing Q \226\134\146 Absorbing (P -\226\136\151 Q)).
Time Proof.
Time (intros).
Time by rewrite /Absorbing absorbingly_wand !absorbing -absorbingly_intro.
Time Qed.
Time #[global]Instance absorbingly_absorbing  P: (Absorbing (<absorb> P)).
Time Proof.
Time rewrite /bi_absorbingly.
Time (apply _).
Time Qed.
Time #[global]Instance persistently_absorbing  P: (Absorbing (<pers> P)).
Time Proof.
Time by rewrite /Absorbing absorbingly_elim_persistently.
Time Qed.
Time #[global]
Instance persistently_if_absorbing  P p:
 (Absorbing P \226\134\146 Absorbing (<pers>?p P)).
Time Proof.
Time (intros; destruct p; simpl; apply _).
Time Qed.
Time #[global]Instance pure_persistent  \207\134: (Persistent (PROP:=PROP) \226\140\156\207\134\226\140\157).
Time Proof.
Time by rewrite /Persistent persistently_pure.
Time Qed.
Time #[global]Instance emp_persistent : (Persistent (PROP:=PROP) emp).
Time Proof.
Time rewrite /Persistent.
Time (apply persistently_emp_intro).
Time Qed.
Time #[global]
Instance and_persistent  P Q:
 (Persistent P \226\134\146 Persistent Q \226\134\146 Persistent (P \226\136\167 Q)).
Time Proof.
Time (intros).
Time by rewrite /Persistent persistently_and -!persistent.
Time Qed.
Time #[global]
Instance or_persistent  P Q:
 (Persistent P \226\134\146 Persistent Q \226\134\146 Persistent (P \226\136\168 Q)).
Time Proof.
Time (intros).
Time by rewrite /Persistent persistently_or -!persistent.
Time Qed.
Time #[global]
Instance forall_persistent  {A} (\206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, Persistent (\206\168 x)) \226\134\146 Persistent (\226\136\128 x, \206\168 x)).
Time Proof.
Time (intros).
Time rewrite /Persistent persistently_forall.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>x).
Time by rewrite -!persistent.
Time Qed.
Time #[global]
Instance exist_persistent  {A} (\206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, Persistent (\206\168 x)) \226\134\146 Persistent (\226\136\131 x, \206\168 x)).
Time Proof.
Time (intros).
Time rewrite /Persistent persistently_exist.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_mono =>x).
Time by rewrite -!persistent.
Time Qed.
Time #[global]
Instance sep_persistent  P Q:
 (Persistent P \226\134\146 Persistent Q \226\134\146 Persistent (P \226\136\151 Q)).
Time Proof.
Time (intros).
Time by rewrite /Persistent -persistently_sep_2 -!persistent.
Time Qed.
Time #[global]Instance persistently_persistent  P: (Persistent (<pers> P)).
Time Proof.
Time by rewrite /Persistent persistently_idemp.
Time Qed.
Time #[global]
Instance affinely_persistent  P: (Persistent P \226\134\146 Persistent (<affine> P)).
Time Proof.
Time rewrite /bi_affinely.
Time (apply _).
Time Qed.
Time #[global]
Instance affinely_if_persistent  p P:
 (Persistent P \226\134\146 Persistent (<affine>?p P)).
Time Proof.
Time (destruct p; simpl; apply _).
Time Qed.
Time #[global]Instance intuitionistically_persistent  P: (Persistent (\226\150\161 P)).
Time Proof.
Time rewrite /bi_intuitionistically.
Time (apply _).
Time Qed.
Time #[global]
Instance absorbingly_persistent  P: (Persistent P \226\134\146 Persistent (<absorb> P)).
Time Proof.
Time rewrite /bi_absorbingly.
Time (apply _).
Time Qed.
Time #[global]
Instance absorbingly_if_persistent  p P:
 (Persistent P \226\134\146 Persistent (<absorb>?p P)).
Time Proof.
Time (destruct p; simpl; apply _).
Time Qed.
Time #[global]
Instance from_option_persistent  {A} P (\206\168 : A \226\134\146 PROP) 
 (mx : option A):
 ((\226\136\128 x, Persistent (\206\168 x)) \226\134\146 Persistent P \226\134\146 Persistent (from_option \206\168 P mx)).
Time Proof.
Time (destruct mx; apply _).
Time Qed.
Time #[global]
Instance bi_and_monoid : (Monoid (@bi_and PROP)) :=
 {| monoid_unit := True%I |}.
Time #[global]
Instance bi_or_monoid : (Monoid (@bi_or PROP)) :=
 {| monoid_unit := False%I |}.
Time #[global]
Instance bi_sep_monoid : (Monoid (@bi_sep PROP)) :=
 {| monoid_unit := emp%I |}.
Time #[global]
Instance bi_persistently_and_homomorphism :
 (MonoidHomomorphism bi_and bi_and (\226\137\161) (@bi_persistently PROP)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply persistently_and).
Time (apply persistently_pure).
Time Qed.
Time #[global]
Instance bi_persistently_or_homomorphism :
 (MonoidHomomorphism bi_or bi_or (\226\137\161) (@bi_persistently PROP)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply persistently_or).
Time (apply persistently_pure).
Time Qed.
Time #[global]
Instance bi_persistently_sep_weak_homomorphism  `{BiPositive PROP}:
 (WeakMonoidHomomorphism bi_sep bi_sep (\226\137\161) (@bi_persistently PROP)).
Time Proof.
Time (split; try apply _).
Time (apply persistently_sep).
Time Qed.
Time #[global]
Instance bi_persistently_sep_homomorphism  `{BiAffine PROP}:
 (MonoidHomomorphism bi_sep bi_sep (\226\137\161) (@bi_persistently PROP)).
Time Proof.
Time split.
Time (apply _).
Time (apply persistently_emp).
Time Qed.
Time #[global]
Instance bi_persistently_sep_entails_weak_homomorphism :
 (WeakMonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@bi_persistently PROP)).
Time Proof.
Time (split; try apply _).
Time (intros P Q; by rewrite persistently_sep_2).
Time Qed.
Time #[global]
Instance bi_persistently_sep_entails_homomorphism :
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@bi_persistently PROP)).
Time Proof.
Time split.
Time (apply _).
Time (simpl).
Time (apply persistently_emp_intro).
Time Qed.
Time
Lemma limit_preserving_entails {A : ofeT} `{Cofe A} 
  (\206\166 \206\168 : A \226\134\146 PROP) :
  NonExpansive \206\166 \226\134\146 NonExpansive \206\168 \226\134\146 LimitPreserving (\206\187 x, \206\166 x \226\138\162 \206\168 x).
Time Proof.
Time (intros H\206\166 H\206\168 c Hc).
Time
(<ssreflect_plugin::ssrtclintros@0> apply entails_eq_True, equiv_dist =>n).
Time rewrite conv_compl.
Time (apply equiv_dist, entails_eq_True).
Time done.
Time Qed.
Time
Lemma limit_preserving_equiv {A : ofeT} `{Cofe A} 
  (\206\166 \206\168 : A \226\134\146 PROP) :
  NonExpansive \206\166 \226\134\146 NonExpansive \206\168 \226\134\146 LimitPreserving (\206\187 x, \206\166 x \226\138\163\226\138\162 \206\168 x).
Time Proof.
Time (intros H\206\166 H\206\168).
Time (eapply limit_preserving_ext).
Time {
Time (intros x).
Time (symmetry; apply equiv_spec).
Time }
Time (apply limit_preserving_and; by apply limit_preserving_entails).
Time Qed.
Time #[global]
Instance limit_preserving_Persistent  {A : ofeT} `{Cofe A} 
 (\206\166 : A \226\134\146 PROP): (NonExpansive \206\166 \226\134\146 LimitPreserving (\206\187 x, Persistent (\206\166 x))).
Time Proof.
Time (intros).
Time (apply limit_preserving_entails; solve_proper).
Time Qed.
Time End bi_derived.
Time End bi.
