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
