Time From stdpp Require Import nat_cancel.
Time From iris.bi Require Import bi tactics.
Time
From iris.proofmode Require Import base modality_instances classes
  class_instances_bi ltac_tactics.
Time Set Default Proof Using "Type".
Time Import bi.
Time Section sbi_instances.
Time Context {PROP : sbi}.
Time Implicit Types P Q R : PROP.
Time #[global]
Instance from_assumption_later  p P Q:
 (FromAssumption p P Q \226\134\146 KnownRFromAssumption p P (\226\150\183 Q)%I).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption =>{+}->).
Time (apply later_intro).
Time Qed.
Time #[global]
Instance from_assumption_laterN  n p P Q:
 (FromAssumption p P Q \226\134\146 KnownRFromAssumption p P (\226\150\183^n Q)%I).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption =>{+}->).
Time (apply laterN_intro).
Time Qed.
Time #[global]
Instance from_assumption_except_0  p P Q:
 (FromAssumption p P Q \226\134\146 KnownRFromAssumption p P (\226\151\135 Q)%I).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption =>{+}->).
Time (apply except_0_intro).
Time Qed.
Time #[global]
Instance from_assumption_fupd  `{BiBUpdFUpd PROP} 
 E p P Q:
 (FromAssumption p P (|==> Q) \226\134\146 KnownRFromAssumption p P (|={E}=> Q)%I).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownRFromAssumption
 /FromAssumption =>{+}->).
Time (apply bupd_fupd).
Time Qed.
Time #[global]
Instance from_assumption_plainly_l_true  `{BiPlainly PROP} 
 P Q: (FromAssumption true P Q \226\134\146 KnownLFromAssumption true (\226\150\160 P) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption /= =>{+}<-).
Time rewrite intuitionistically_plainly_elim //.
Time Qed.
Time #[global]
Instance from_assumption_plainly_l_false  `{BiPlainly PROP} 
 `{BiAffine PROP} P Q:
 (FromAssumption true P Q \226\134\146 KnownLFromAssumption false (\226\150\160 P) Q).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /KnownLFromAssumption
 /FromAssumption /= =>{+}<-).
Time
rewrite plainly_elim_persistently intuitionistically_into_persistently //.
Time Qed.
Time #[global]
Instance from_pure_internal_eq  {A : ofeT} (a b : A):
 (@FromPure PROP false (a \226\137\161 b) (a \226\137\161 b)).
Time Proof.
Time by rewrite /FromPure pure_internal_eq.
Time Qed.
Time #[global]
Instance from_pure_later  a P \207\134: (FromPure a P \207\134 \226\134\146 FromPure a (\226\150\183 P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}->).
Time (apply later_intro).
Time Qed.
Time #[global]
Instance from_pure_laterN  a n P \207\134: (FromPure a P \207\134 \226\134\146 FromPure a (\226\150\183^n P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}->).
Time (apply laterN_intro).
Time Qed.
Time #[global]
Instance from_pure_except_0  a P \207\134: (FromPure a P \207\134 \226\134\146 FromPure a (\226\151\135 P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}->).
Time (apply except_0_intro).
Time Qed.
Time #[global]
Instance from_pure_fupd  `{BiFUpd PROP} a E P \207\134:
 (FromPure a P \207\134 \226\134\146 FromPure a (|={E}=> P) \207\134).
Time Proof.
Time rewrite /FromPure.
Time (intros <-).
Time (apply fupd_intro).
Time Qed.
Time #[global]
Instance from_pure_plainly  `{BiPlainly PROP} P \207\134:
 (FromPure false P \207\134 \226\134\146 FromPure false (\226\150\160 P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromPure =>{+}<-).
Time by rewrite plainly_pure.
Time Qed.
Time #[global]
Instance into_pure_eq  {A : ofeT} (a b : A):
 (Discrete a \226\134\146 @IntoPure PROP (a \226\137\161 b) (a \226\137\161 b)).
Time Proof.
Time (intros).
Time by rewrite /IntoPure discrete_eq.
Time Qed.
Time #[global]
Instance into_pure_plainly  `{BiPlainly PROP} P \207\134:
 (IntoPure P \207\134 \226\134\146 IntoPure (\226\150\160 P) \207\134).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoPure =>{+}->).
Time apply : {}plainly_elim {}.
Time Qed.
Time #[global]
Instance into_wand_later  p q R P Q:
 (IntoWand p q R P Q \226\134\146 IntoWand p q (\226\150\183 R) (\226\150\183 P) (\226\150\183 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>HR).
Time by rewrite !later_intuitionistically_if_2 -later_wand HR.
Time Qed.
Time #[global]
Instance into_wand_later_args  p q R P Q:
 (IntoWand p q R P Q \226\134\146 IntoWand' p q R (\226\150\183 P) (\226\150\183 Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand' /IntoWand /= =>HR).
Time
by rewrite !later_intuitionistically_if_2 (later_intro (\226\150\161?p R)%I) -later_wand
 HR.
Time Qed.
Time #[global]
Instance into_wand_laterN  n p q R P Q:
 (IntoWand p q R P Q \226\134\146 IntoWand p q (\226\150\183^n R) (\226\150\183^n P) (\226\150\183^n Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>HR).
Time by rewrite !laterN_intuitionistically_if_2 -laterN_wand HR.
Time Qed.
Time #[global]
Instance into_wand_laterN_args  n p q R P Q:
 (IntoWand p q R P Q \226\134\146 IntoWand' p q R (\226\150\183^n P) (\226\150\183^n Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand' /IntoWand /= =>HR).
Time
by rewrite !laterN_intuitionistically_if_2 (laterN_intro _ (\226\150\161?p R)%I)
 -laterN_wand HR.
Time Qed.
Time #[global]
Instance into_wand_fupd  `{BiFUpd PROP} E p q R P 
 Q:
 (IntoWand false false R P Q
  \226\134\146 IntoWand p q (|={E}=> R) (|={E}=> P) (|={E}=> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>HR).
Time rewrite !intuitionistically_if_elim HR.
Time (apply wand_intro_l).
Time by rewrite fupd_sep wand_elim_r.
Time Qed.
Time #[global]
Instance into_wand_fupd_persistent  `{BiFUpd PROP} 
 E1 E2 p q R P Q:
 (IntoWand false q R P Q \226\134\146 IntoWand p q (|={E1,E2}=> R) P (|={E1,E2}=> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand /= =>HR).
Time rewrite intuitionistically_if_elim HR.
Time (apply wand_intro_l).
Time by rewrite fupd_frame_l wand_elim_r.
Time Qed.
Time #[global]
Instance into_wand_fupd_args  `{BiFUpd PROP} E1 E2 
 p q R P Q:
 (IntoWand p false R P Q \226\134\146 IntoWand' p q R (|={E1,E2}=> P) (|={E1,E2}=> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoWand' /IntoWand /= =>{+}->).
Time (apply wand_intro_l).
Time by rewrite intuitionistically_if_elim fupd_wand_r.
Time Qed.
Time #[global]
Instance into_wand_plainly_true  `{BiPlainly PROP} 
 q R P Q: (IntoWand true q R P Q \226\134\146 IntoWand true q (\226\150\160 R) P Q).
Time Proof.
Time rewrite /IntoWand /= intuitionistically_plainly_elim //.
Time Qed.
Time #[global]
Instance into_wand_plainly_false  `{BiPlainly PROP} 
 q R P Q: (Absorbing R \226\134\146 IntoWand false q R P Q \226\134\146 IntoWand false q (\226\150\160 R) P Q).
Time Proof.
Time (intros ?).
Time by rewrite /IntoWand plainly_elim.
Time Qed.
Time #[global]
Instance from_and_later  P Q1 Q2:
 (FromAnd P Q1 Q2 \226\134\146 FromAnd (\226\150\183 P) (\226\150\183 Q1) (\226\150\183 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromAnd =>{+}<-).
Time by rewrite later_and.
Time Qed.
Time #[global]
Instance from_and_laterN  n P Q1 Q2:
 (FromAnd P Q1 Q2 \226\134\146 FromAnd (\226\150\183^n P) (\226\150\183^n Q1) (\226\150\183^n Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromAnd =>{+}<-).
Time by rewrite laterN_and.
Time Qed.
Time #[global]
Instance from_and_except_0  P Q1 Q2:
 (FromAnd P Q1 Q2 \226\134\146 FromAnd (\226\151\135 P) (\226\151\135 Q1) (\226\151\135 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromAnd =>{+}<-).
Time by rewrite except_0_and.
Time Qed.
Time #[global]
Instance from_and_plainly  `{BiPlainly PROP} P Q1 
 Q2: (FromAnd P Q1 Q2 \226\134\146 FromAnd (\226\150\160 P) (\226\150\160 Q1) (\226\150\160 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromAnd =>{+}<-).
Time by rewrite plainly_and.
Time Qed.
Time #[global]
Instance from_sep_later  P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (\226\150\183 P) (\226\150\183 Q1) (\226\150\183 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite later_sep.
Time Qed.
Time #[global]
Instance from_sep_laterN  n P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (\226\150\183^n P) (\226\150\183^n Q1) (\226\150\183^n Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite laterN_sep.
Time Qed.
Time #[global]
Instance from_sep_except_0  P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (\226\151\135 P) (\226\151\135 Q1) (\226\151\135 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite except_0_sep.
Time Qed.
Time #[global]
Instance from_sep_fupd  `{BiFUpd PROP} E P Q1 Q2:
 (FromSep P Q1 Q2 \226\134\146 FromSep (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time (apply fupd_sep).
Time Qed.
Time #[global]
Instance from_sep_plainly  `{BiPlainly PROP} P Q1 
 Q2: (FromSep P Q1 Q2 \226\134\146 FromSep (\226\150\160 P) (\226\150\160 Q1) (\226\150\160 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>{+}<-).
Time by rewrite plainly_sep_2.
Time Qed.
Time #[global]
Instance into_and_later  p P Q1 Q2:
 (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (\226\150\183 P) (\226\150\183 Q1) (\226\150\183 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoAnd =>HP).
Time (apply intuitionistically_if_intro').
Time
by rewrite later_intuitionistically_if_2 HP intuitionistically_if_elim
 later_and.
Time Qed.
Time #[global]
Instance into_and_laterN  n p P Q1 Q2:
 (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (\226\150\183^n P) (\226\150\183^n Q1) (\226\150\183^n Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoAnd =>HP).
Time (apply intuitionistically_if_intro').
Time
by rewrite laterN_intuitionistically_if_2 HP intuitionistically_if_elim
 laterN_and.
Time Qed.
Time #[global]
Instance into_and_except_0  p P Q1 Q2:
 (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (\226\151\135 P) (\226\151\135 Q1) (\226\151\135 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoAnd =>HP).
Time (apply intuitionistically_if_intro').
Time
by rewrite except_0_intuitionistically_if_2 HP intuitionistically_if_elim
 except_0_and.
Time Qed.
Time #[global]
Instance into_and_plainly  `{BiPlainly PROP} p P Q1 
 Q2: (IntoAnd p P Q1 Q2 \226\134\146 IntoAnd p (\226\150\160 P) (\226\150\160 Q1) (\226\150\160 Q2)).
Time Proof.
Time rewrite /IntoAnd /=.
Time (destruct p; simpl).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -plainly_and
 -[(\226\150\161 \226\150\160 P)%I]intuitionistically_idemp intuitionistically_plainly =>{+}->).
Time rewrite [(\226\150\161 (_ \226\136\167 _))%I]intuitionistically_elim //.
Time -
Time (intros ->).
Time by rewrite plainly_and.
Time Qed.
Time #[global]
Instance into_sep_later  P Q1 Q2:
 (IntoSep P Q1 Q2 \226\134\146 IntoSep (\226\150\183 P) (\226\150\183 Q1) (\226\150\183 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep =>{+}->).
Time by rewrite later_sep.
Time Qed.
Time #[global]
Instance into_sep_laterN  n P Q1 Q2:
 (IntoSep P Q1 Q2 \226\134\146 IntoSep (\226\150\183^n P) (\226\150\183^n Q1) (\226\150\183^n Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep =>{+}->).
Time by rewrite laterN_sep.
Time Qed.
Time #[global]
Instance into_sep_except_0  P Q1 Q2:
 (IntoSep P Q1 Q2 \226\134\146 IntoSep (\226\151\135 P) (\226\151\135 Q1) (\226\151\135 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep =>{+}->).
Time by rewrite except_0_sep.
Time Qed.
Time #[global]
Instance into_sep_affinely_later  `{!Timeless (PROP:=PROP) emp} 
 P Q1 Q2:
 (IntoSep P Q1 Q2
  \226\134\146 Affine Q1
    \226\134\146 Affine Q2 \226\134\146 IntoSep (<affine> \226\150\183 P) (<affine> \226\150\183 Q1) (<affine> \226\150\183 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}-> ? ?).
Time
rewrite -{+1}(affine_affinely Q1) -{+1}(affine_affinely Q2) later_sep
 !later_affinely_1.
Time rewrite -except_0_sep /sbi_except_0 affinely_or.
Time (apply or_elim, affinely_elim).
Time rewrite -(idemp bi_and (<affine> \226\150\183 False)%I) persistent_and_sep_1.
Time by rewrite -(False_elim Q1) -(False_elim Q2).
Time Qed.
Time #[global]
Instance into_sep_plainly  `{BiPlainly PROP} `{BiPositive PROP} 
 P Q1 Q2: (IntoSep P Q1 Q2 \226\134\146 IntoSep (\226\150\160 P) (\226\150\160 Q1) (\226\150\160 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}->).
Time by rewrite plainly_sep.
Time Qed.
Time #[global]
Instance into_sep_plainly_affine  `{BiPlainly PROP} 
 P Q1 Q2:
 (IntoSep P Q1 Q2
  \226\134\146 TCOr (Affine Q1) (Absorbing Q2)
    \226\134\146 TCOr (Absorbing Q1) (Affine Q2) \226\134\146 IntoSep (\226\150\160 P) (\226\150\160 Q1) (\226\150\160 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSep /= =>{+}-> ? ?).
Time by rewrite sep_and plainly_and plainly_and_sep_l_1.
Time Qed.
Time #[global]
Instance from_or_later  P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (\226\150\183 P) (\226\150\183 Q1) (\226\150\183 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite later_or.
Time Qed.
Time #[global]
Instance from_or_laterN  n P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (\226\150\183^n P) (\226\150\183^n Q1) (\226\150\183^n Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite laterN_or.
Time Qed.
Time #[global]
Instance from_or_except_0  P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (\226\151\135 P) (\226\151\135 Q1) (\226\151\135 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite except_0_or.
Time Qed.
Time #[global]
Instance from_or_fupd  `{BiFUpd PROP} E1 E2 P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time
(apply or_elim; apply fupd_mono;
  [ apply bi.or_intro_l | apply bi.or_intro_r ]).
Time Qed.
Time #[global]
Instance from_or_plainly  `{BiPlainly PROP} P Q1 Q2:
 (FromOr P Q1 Q2 \226\134\146 FromOr (\226\150\160 P) (\226\150\160 Q1) (\226\150\160 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromOr =>{+}<-).
Time by rewrite -plainly_or_2.
Time Qed.
Time #[global]
Instance into_or_later  P Q1 Q2:
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (\226\150\183 P) (\226\150\183 Q1) (\226\150\183 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite later_or.
Time Qed.
Time #[global]
Instance into_or_laterN  n P Q1 Q2:
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (\226\150\183^n P) (\226\150\183^n Q1) (\226\150\183^n Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite laterN_or.
Time Qed.
Time #[global]
Instance into_or_except_0  P Q1 Q2:
 (IntoOr P Q1 Q2 \226\134\146 IntoOr (\226\151\135 P) (\226\151\135 Q1) (\226\151\135 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite except_0_or.
Time Qed.
Time #[global]
Instance into_or_plainly  `{BiPlainly PROP} `{BiPlainlyExist PROP} 
 P Q1 Q2: (IntoOr P Q1 Q2 \226\134\146 IntoOr (\226\150\160 P) (\226\150\160 Q1) (\226\150\160 Q2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoOr =>{+}->).
Time by rewrite plainly_or.
Time Qed.
Time #[global]
Instance from_exist_later  {A} P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (\226\150\183 P) (\206\187 a, \226\150\183 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>x).
Time (apply later_mono, exist_intro).
Time Qed.
Time #[global]
Instance from_exist_laterN  {A} n P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (\226\150\183^n P) (\206\187 a, \226\150\183^n \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>x).
Time (apply laterN_mono, exist_intro).
Time Qed.
Time #[global]
Instance from_exist_except_0  {A} P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (\226\151\135 P) (\206\187 a, \226\151\135 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time by rewrite except_0_exist_2.
Time Qed.
Time #[global]
Instance from_exist_fupd  `{BiFUpd PROP} {A} E1 E2 
 P (\206\166 : A \226\134\146 PROP):
 (FromExist P \206\166 \226\134\146 FromExist (|={E1,E2}=> P) (\206\187 a, |={E1,E2}=> \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a).
Time by rewrite -(exist_intro a).
Time Qed.
Time #[global]
Instance from_exist_plainly  `{BiPlainly PROP} {A} 
 P (\206\166 : A \226\134\146 PROP): (FromExist P \206\166 \226\134\146 FromExist (\226\150\160 P) (\206\187 a, \226\150\160 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromExist =>{+}<-).
Time by rewrite -plainly_exist_2.
Time Qed.
Time #[global]
Instance into_exist_later  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoExist P \206\166 \226\134\146 Inhabited A \226\134\146 IntoExist (\226\150\183 P) (\206\187 a, \226\150\183 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP ?).
Time by rewrite HP later_exist.
Time Qed.
Time #[global]
Instance into_exist_laterN  {A} n P (\206\166 : A \226\134\146 PROP):
 (IntoExist P \206\166 \226\134\146 Inhabited A \226\134\146 IntoExist (\226\150\183^n P) (\206\187 a, \226\150\183^n \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP ?).
Time by rewrite HP laterN_exist.
Time Qed.
Time #[global]
Instance into_exist_except_0  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoExist P \206\166 \226\134\146 Inhabited A \226\134\146 IntoExist (\226\151\135 P) (\206\187 a, \226\151\135 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP ?).
Time by rewrite HP except_0_exist.
Time Qed.
Time #[global]
Instance into_exist_plainly  `{BiPlainlyExist PROP} 
 {A} P (\206\166 : A \226\134\146 PROP): (IntoExist P \206\166 \226\134\146 IntoExist (\226\150\160 P) (\206\187 a, \226\150\160 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExist =>HP).
Time by rewrite HP plainly_exist.
Time Qed.
Time #[global]
Instance into_forall_later  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoForall P \206\166 \226\134\146 IntoForall (\226\150\183 P) (\206\187 a, \226\150\183 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall =>HP).
Time by rewrite HP later_forall.
Time Qed.
Time #[global]
Instance into_forall_laterN  {A} P (\206\166 : A \226\134\146 PROP) 
 n: (IntoForall P \206\166 \226\134\146 IntoForall (\226\150\183^n P) (\206\187 a, \226\150\183^n \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall =>HP).
Time by rewrite HP laterN_forall.
Time Qed.
Time #[global]
Instance into_forall_except_0  {A} P (\206\166 : A \226\134\146 PROP):
 (IntoForall P \206\166 \226\134\146 IntoForall (\226\151\135 P) (\206\187 a, \226\151\135 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall =>HP).
Time by rewrite HP except_0_forall.
Time Qed.
Time #[global]
Instance into_forall_plainly  `{BiPlainly PROP} {A} 
 P (\206\166 : A \226\134\146 PROP): (IntoForall P \206\166 \226\134\146 IntoForall (\226\150\160 P) (\206\187 a, \226\150\160 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoForall =>HP).
Time by rewrite HP plainly_forall.
Time Qed.
Time #[global]
Instance from_forall_later  {A} P (\206\166 : A \226\134\146 PROP):
 (FromForall P \206\166 \226\134\146 FromForall (\226\150\183 P)%I (\206\187 a, \226\150\183 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>{+}<-).
Time by rewrite later_forall.
Time Qed.
Time #[global]
Instance from_forall_laterN  {A} P (\206\166 : A \226\134\146 PROP) 
 n: (FromForall P \206\166 \226\134\146 FromForall (\226\150\183^n P)%I (\206\187 a, \226\150\183^n \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>{+}<-).
Time by rewrite laterN_forall.
Time Qed.
Time #[global]
Instance from_forall_except_0  {A} P (\206\166 : A \226\134\146 PROP):
 (FromForall P \206\166 \226\134\146 FromForall (\226\151\135 P)%I (\206\187 a, \226\151\135 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>{+}<-).
Time by rewrite except_0_forall.
Time Qed.
Time #[global]
Instance from_forall_plainly  `{BiPlainly PROP} {A} 
 P (\206\166 : A \226\134\146 PROP): (FromForall P \206\166 \226\134\146 FromForall (\226\150\160 P)%I (\206\187 a, \226\150\160 \206\166 a)%I).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>{+}<-).
Time by rewrite plainly_forall.
Time Qed.
Time #[global]
Instance from_forall_fupd  `{BiFUpdPlainly PROP} E1 
 E2 {A} P (\206\166 : A \226\134\146 PROP):
 (TCOr (TCEq E1 E2) (TCOr (TCEq E1 \226\138\164) (TCEq E2 \226\136\133))
  \226\134\146 FromForall P \206\166
    \226\134\146 (\226\136\128 x, Plain (\206\166 x))
      \226\134\146 FromForall (|={E1,E2}=> P)%I (\206\187 a, |={E1,E2}=> \206\166 a)%I).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>-
  [{+}->|[{+}->|{+}->]] {+}<- ?; rewrite fupd_plain_forall; set_solver).
Time Qed.
Time #[global]
Instance from_forall_step_fupd  `{BiFUpdPlainly PROP} 
 E1 E2 {A} P (\206\166 : A \226\134\146 PROP):
 (TCOr (TCEq E1 E2) (TCOr (TCEq E1 \226\138\164) (TCEq E2 \226\136\133))
  \226\134\146 FromForall P \206\166
    \226\134\146 (\226\136\128 x, Plain (\206\166 x))
      \226\134\146 FromForall (|={E1,E2}\226\150\183=> P)%I (\206\187 a, |={E1,E2}\226\150\183=> \206\166 a)%I).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromForall =>-
  [{+}->|[{+}->|{+}->]] {+}<- ?; rewrite step_fupd_plain_forall; set_solver).
Time Qed.
Time #[global]Instance is_except_0_except_0  P: (IsExcept0 (\226\151\135 P)).
Time Proof.
Time by rewrite /IsExcept0 except_0_idemp.
Time Qed.
Time #[global]Instance is_except_0_later  P: (IsExcept0 (\226\150\183 P)).
Time Proof.
Time by rewrite /IsExcept0 except_0_later.
Time Qed.
Time #[global]
Instance is_except_0_embed  `{SbiEmbed PROP PROP'} 
 P: (IsExcept0 P \226\134\146 IsExcept0 \226\142\161 P \226\142\164).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /IsExcept0 -embed_except_0
 =>{+}->.
Time Qed.
Time #[global]
Instance is_except_0_bupd  `{BiBUpd PROP} P:
 (IsExcept0 P \226\134\146 IsExcept0 (|==> P)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsExcept0 =>HP).
Time
by rewrite -{+2}HP -(except_0_idemp P) -except_0_bupd -(except_0_intro P).
Time Qed.
Time #[global]
Instance is_except_0_fupd  `{BiFUpd PROP} E1 E2 P:
 (IsExcept0 (|={E1,E2}=> P)).
Time Proof.
Time by rewrite /IsExcept0 except_0_fupd.
Time Qed.
Time #[global]
Instance from_modal_later  P: (FromModal (modality_laterN 1) (\226\150\183^1 P) (\226\150\183 P) P).
Time Proof.
Time by rewrite /FromModal.
Time Qed.
Time #[global]
Instance from_modal_laterN  n P:
 (FromModal (modality_laterN n) (\226\150\183^n P) (\226\150\183^n P) P).
Time Proof.
Time by rewrite /FromModal.
Time Qed.
Time #[global]
Instance from_modal_except_0  P: (FromModal modality_id (\226\151\135 P) (\226\151\135 P) P).
Time Proof.
Time by rewrite /FromModal /= -except_0_intro.
Time Qed.
Time #[global]
Instance from_modal_fupd  E P `{BiFUpd PROP}:
 (FromModal modality_id (|={E}=> P) (|={E}=> P) P).
Time Proof.
Time by rewrite /FromModal /= -fupd_intro.
Time Qed.
Time #[global]
Instance from_modal_later_embed  `{SbiEmbed PROP PROP'} 
 `(sel : A) n P Q:
 (FromModal (modality_laterN n) sel P Q
  \226\134\146 FromModal (modality_laterN n) sel \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromModal /= =>{+}<-).
Time by rewrite embed_laterN.
Time Qed.
Time #[global]
Instance from_modal_plainly  `{BiPlainly PROP} P:
 (FromModal modality_plainly (\226\150\160 P) (\226\150\160 P) P) |2.
Time Proof.
Time by rewrite /FromModal.
Time Qed.
Time #[global]
Instance from_modal_plainly_embed  `{BiPlainly PROP} 
 `{BiPlainly PROP'} `{BiEmbedPlainly PROP PROP'} `{!SbiEmbed PROP PROP'}
 `(sel : A) P Q:
 (FromModal modality_plainly sel P Q
  \226\134\146 FromModal (PROP2:=PROP') modality_plainly sel \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164) |100.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FromModal /= =>{+}<-).
Time by rewrite embed_plainly.
Time Qed.
Time #[global]
Instance into_internal_eq_internal_eq  {A : ofeT} 
 (x y : A): (@IntoInternalEq PROP A (x \226\137\161 y) x y).
Time Proof.
Time by rewrite /IntoInternalEq.
Time Qed.
Time #[global]
Instance into_internal_eq_affinely  {A : ofeT} (x y : A) 
 P: (IntoInternalEq P x y \226\134\146 IntoInternalEq (<affine> P) x y).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoInternalEq =>{+}->).
Time by rewrite affinely_elim.
Time Qed.
Time #[global]
Instance into_internal_eq_intuitionistically  {A : ofeT} 
 (x y : A) P: (IntoInternalEq P x y \226\134\146 IntoInternalEq (\226\150\161 P) x y).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoInternalEq =>{+}->).
Time by rewrite intuitionistically_elim.
Time Qed.
Time #[global]
Instance into_internal_eq_absorbingly  {A : ofeT} 
 (x y : A) P: (IntoInternalEq P x y \226\134\146 IntoInternalEq (<absorb> P) x y).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoInternalEq =>{+}->).
Time by rewrite absorbingly_internal_eq.
Time Qed.
Time #[global]
Instance into_internal_eq_plainly  `{BiPlainly PROP} 
 {A : ofeT} (x y : A) P: (IntoInternalEq P x y \226\134\146 IntoInternalEq (\226\150\160 P) x y).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoInternalEq =>{+}->).
Time by rewrite plainly_elim.
Time Qed.
Time #[global]
Instance into_internal_eq_persistently  {A : ofeT} 
 (x y : A) P: (IntoInternalEq P x y \226\134\146 IntoInternalEq (<pers> P) x y).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoInternalEq =>{+}->).
Time by rewrite persistently_elim.
Time Qed.
Time #[global]
Instance into_internal_eq_embed  `{SbiEmbed PROP PROP'} 
 {A : ofeT} (x y : A) P: (IntoInternalEq P x y \226\134\146 IntoInternalEq \226\142\161 P \226\142\164 x y).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoInternalEq =>{+}->).
Time by rewrite embed_internal_eq.
Time Qed.
Time #[global]Instance into_except_0_except_0  P: (IntoExcept0 (\226\151\135 P) P).
Time Proof.
Time by rewrite /IntoExcept0.
Time Qed.
Time #[global]
Instance into_except_0_later  P: (Timeless P \226\134\146 IntoExcept0 (\226\150\183 P) P).
Time Proof.
Time by rewrite /IntoExcept0.
Time Qed.
Time #[global]
Instance into_except_0_later_if  p P: (Timeless P \226\134\146 IntoExcept0 (\226\150\183?p P) P).
Time Proof.
Time rewrite /IntoExcept0.
Time (destruct p; auto using except_0_intro).
Time Qed.
Time #[global]
Instance into_except_0_affinely  P Q:
 (IntoExcept0 P Q \226\134\146 IntoExcept0 (<affine> P) (<affine> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExcept0 =>{+}->).
Time by rewrite except_0_affinely_2.
Time Qed.
Time #[global]
Instance into_except_0_intuitionistically  P Q:
 (IntoExcept0 P Q \226\134\146 IntoExcept0 (\226\150\161 P) (\226\150\161 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExcept0 =>{+}->).
Time by rewrite except_0_intuitionistically_2.
Time Qed.
Time #[global]
Instance into_except_0_absorbingly  P Q:
 (IntoExcept0 P Q \226\134\146 IntoExcept0 (<absorb> P) (<absorb> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExcept0 =>{+}->).
Time by rewrite except_0_absorbingly.
Time Qed.
Time #[global]
Instance into_except_0_plainly  `{BiPlainly PROP} 
 `{BiPlainlyExist PROP} P Q: (IntoExcept0 P Q \226\134\146 IntoExcept0 (\226\150\160 P) (\226\150\160 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExcept0 =>{+}->).
Time by rewrite except_0_plainly.
Time Qed.
Time #[global]
Instance into_except_0_persistently  P Q:
 (IntoExcept0 P Q \226\134\146 IntoExcept0 (<pers> P) (<pers> Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExcept0 =>{+}->).
Time by rewrite except_0_persistently.
Time Qed.
Time #[global]
Instance into_except_0_embed  `{SbiEmbed PROP PROP'} 
 P Q: (IntoExcept0 P Q \226\134\146 IntoExcept0 \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoExcept0 =>{+}->).
Time by rewrite embed_except_0.
Time Qed.
Time #[global]
Instance elim_modal_timeless  p P Q:
 (IntoExcept0 P P' \226\134\146 IsExcept0 Q \226\134\146 ElimModal True p p P P' Q Q).
Time Proof.
Time (intros).
Time rewrite /ElimModal (except_0_intro (_ -\226\136\151 _)%I) (into_except_0 P).
Time by rewrite except_0_intuitionistically_if_2 -except_0_sep wand_elim_r.
Time Qed.
Time #[global]
Instance elim_modal_bupd_plain_goal  `{BiBUpdPlainly PROP} 
 p P Q: (Plain Q \226\134\146 ElimModal True p false (|==> P) P Q Q).
Time Proof.
Time (intros).
Time
by rewrite /ElimModal intuitionistically_if_elim bupd_frame_r wand_elim_r
 bupd_plain.
Time Qed.
Time #[global]
Instance elim_modal_bupd_plain  `{BiBUpdPlainly PROP} 
 p P Q: (Plain P \226\134\146 ElimModal True p p (|==> P) P Q Q).
Time Proof.
Time (intros).
Time by rewrite /ElimModal bupd_plain wand_elim_r.
Time Qed.
Time #[global]
Instance elim_modal_bupd_fupd  `{BiBUpdFUpd PROP} 
 p E1 E2 P Q:
 (ElimModal True p false (|==> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q)) |10.
Time Proof.
Time
by rewrite /ElimModal intuitionistically_if_elim (bupd_fupd E1) fupd_frame_r
 wand_elim_r fupd_trans.
Time Qed.
Time #[global]
Instance elim_modal_fupd_fupd  `{BiFUpd PROP} p E1 
 E2 E3 P Q:
 (ElimModal True p false (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q)).
Time Proof.
Time
by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r
 fupd_trans.
Time Qed.
Time #[global]
Instance elim_modal_embed_fupd_goal  `{BiEmbedFUpd PROP PROP'} 
 p p' \207\134 E1 E2 E3 (P P' : PROP') (Q Q' : PROP):
 (ElimModal \207\134 p p' P P' (|={E1,E3}=> \226\142\161 Q \226\142\164)%I (|={E2,E3}=> \226\142\161 Q' \226\142\164)%I
  \226\134\146 ElimModal \207\134 p p' P P' \226\142\161 |={E1,E3}=> Q \226\142\164 \226\142\161 |={E2,E3}=> Q' \226\142\164).
Time Proof.
Time by rewrite /ElimModal !embed_fupd.
Time Qed.
Time #[global]
Instance elim_modal_embed_fupd_hyp  `{BiEmbedFUpd PROP PROP'} 
 p p' \207\134 E1 E2 (P : PROP) (P' Q Q' : PROP'):
 (ElimModal \207\134 p p' (|={E1,E2}=> \226\142\161 P \226\142\164)%I P' Q Q'
  \226\134\146 ElimModal \207\134 p p' \226\142\161 |={E1,E2}=> P \226\142\164 P' Q Q').
Time Proof.
Time by rewrite /ElimModal embed_fupd.
Time Qed.
Time #[global]
Instance add_modal_later_except_0  P Q: (Timeless P \226\134\146 AddModal (\226\150\183 P) P (\226\151\135 Q))
 |0.
Time Proof.
Time (intros).
Time rewrite /AddModal (except_0_intro (_ -\226\136\151 _)%I) (timeless P).
Time by rewrite -except_0_sep wand_elim_r except_0_idemp.
Time Qed.
Time #[global]
Instance add_modal_later  P Q: (Timeless P \226\134\146 AddModal (\226\150\183 P) P (\226\150\183 Q)) |0.
Time Proof.
Time (intros).
Time rewrite /AddModal (except_0_intro (_ -\226\136\151 _)%I) (timeless P).
Time by rewrite -except_0_sep wand_elim_r except_0_later.
Time Qed.
Time #[global]Instance add_modal_except_0  P Q: (AddModal (\226\151\135 P) P (\226\151\135 Q)) |1.
Time Proof.
Time (intros).
Time rewrite /AddModal (except_0_intro (_ -\226\136\151 _)%I).
Time by rewrite -except_0_sep wand_elim_r except_0_idemp.
Time Qed.
Time #[global]
Instance add_modal_except_0_later  P Q: (AddModal (\226\151\135 P) P (\226\150\183 Q)) |1.
Time Proof.
Time (intros).
Time rewrite /AddModal (except_0_intro (_ -\226\136\151 _)%I).
Time by rewrite -except_0_sep wand_elim_r except_0_later.
Time Qed.
Time #[global]
Instance add_modal_fupd  `{BiFUpd PROP} E1 E2 P Q:
 (AddModal (|={E1}=> P) P (|={E1,E2}=> Q)).
Time Proof.
Time by rewrite /AddModal fupd_frame_r wand_elim_r fupd_trans.
Time Qed.
Time #[global]
Instance add_modal_embed_fupd_goal  `{BiEmbedFUpd PROP PROP'} 
 E1 E2 (P P' : PROP') (Q : PROP):
 (AddModal P P' (|={E1,E2}=> \226\142\161 Q \226\142\164)%I \226\134\146 AddModal P P' \226\142\161 |={E1,E2}=> Q \226\142\164).
Time Proof.
Time by rewrite /AddModal !embed_fupd.
Time Qed.
Time #[global]
Instance elim_acc_fupd  `{BiFUpd PROP} {X} E1 E2 E 
 \206\177 \206\178 m\206\179 Q:
 (ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1) \206\177 \206\178 m\206\179 
    (|={E1,E}=> Q) (\206\187 x, |={E2}=> \206\178 x \226\136\151 (m\206\179 x -\226\136\151? |={E1,E}=> Q))%I).
Time Proof.
Time rewrite /ElimAcc.
Time iIntros "Hinner >Hacc".
Time iDestruct "Hacc" as ( x ) "[H\206\177 Hclose]".
Time iMod ("Hinner" with "H\206\177") as "[H\206\178 Hfin]".
Time iMod ("Hclose" with "H\206\178") as "H\206\179".
Time by iApply "Hfin".
Time Qed.
Time #[global]
Instance into_laterN_0  only_head P: (IntoLaterN only_head 0 P P).
Time Proof.
Time by rewrite /IntoLaterN /MaybeIntoLaterN.
Time Qed.
Time #[global]
Instance into_laterN_later  only_head n n' m' P Q 
 lQ:
 (NatCancel n 1 n' m'
  \226\134\146 TCIf (TCEq 1 m') (IntoLaterN only_head n' P Q)
      (MaybeIntoLaterN only_head n' P Q)
    \226\134\146 MakeLaterN m' Q lQ \226\134\146 IntoLaterN only_head n (\226\150\183 P) lQ) |2.
Time Proof.
Time rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel.
Time
(move  {}=>Hn [_ {+}->|{+}->] {+}<-; by rewrite -later_laterN -laterN_plus
  -Hn Nat.add_comm).
Time Qed.
Time #[global]
Instance into_laterN_laterN  only_head n m n' m' P 
 Q lQ:
 (NatCancel n m n' m'
  \226\134\146 TCIf (TCEq m m') (IntoLaterN only_head n' P Q)
      (MaybeIntoLaterN only_head n' P Q)
    \226\134\146 MakeLaterN m' Q lQ \226\134\146 IntoLaterN only_head n (\226\150\183^m P) lQ) |1.
Time Proof.
Time rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel.
Time
(move  {}=>Hn [_ {+}->|{+}->] {+}<-; by rewrite -!laterN_plus -Hn
  Nat.add_comm).
Time Qed.
Time #[global]
Instance into_laterN_Next  {A : ofeT} only_head n 
 n' (x y : A):
 (NatCancel n 1 n' 0
  \226\134\146 IntoLaterN (PROP:=PROP) only_head n (Next x \226\137\161 Next y) (x \226\137\161 y)) |2.
Time Proof.
Time rewrite /MakeLaterN /IntoLaterN /MaybeIntoLaterN /NatCancel Nat.add_0_r.
Time move  {}=>{+}<-.
Time rewrite later_equivI.
Time by rewrite Nat.add_comm /= -laterN_intro.
Time Qed.
Time #[global]
Instance into_laterN_and_l  n P1 P2 Q1 Q2:
 (IntoLaterN false n P1 Q1
  \226\134\146 MaybeIntoLaterN false n P2 Q2 \226\134\146 IntoLaterN false n (P1 \226\136\167 P2) (Q1 \226\136\167 Q2))
 |10.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}-> {+}->).
Time by rewrite laterN_and.
Time Qed.
Time #[global]
Instance into_laterN_and_r  n P P2 Q2:
 (IntoLaterN false n P2 Q2 \226\134\146 IntoLaterN false n (P \226\136\167 P2) (P \226\136\167 Q2)) |11.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_and -(laterN_intro _ P).
Time Qed.
Time #[global]
Instance into_laterN_forall  {A} n (\206\166 \206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, IntoLaterN false n (\206\166 x) (\206\168 x))
  \226\134\146 IntoLaterN false n (\226\136\128 x, \206\166 x) (\226\136\128 x, \206\168 x)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 laterN_forall =>?).
Time by apply forall_mono.
Time Qed.
Time #[global]
Instance into_laterN_exist  {A} n (\206\166 \206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, IntoLaterN false n (\206\166 x) (\206\168 x))
  \226\134\146 IntoLaterN false n (\226\136\131 x, \206\166 x) (\226\136\131 x, \206\168 x)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 -laterN_exist_2 =>?).
Time by apply exist_mono.
Time Qed.
Time #[global]
Instance into_laterN_or_l  n P1 P2 Q1 Q2:
 (IntoLaterN false n P1 Q1
  \226\134\146 MaybeIntoLaterN false n P2 Q2 \226\134\146 IntoLaterN false n (P1 \226\136\168 P2) (Q1 \226\136\168 Q2))
 |10.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}-> {+}->).
Time by rewrite laterN_or.
Time Qed.
Time #[global]
Instance into_laterN_or_r  n P P2 Q2:
 (IntoLaterN false n P2 Q2 \226\134\146 IntoLaterN false n (P \226\136\168 P2) (P \226\136\168 Q2)) |11.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_or -(laterN_intro _ P).
Time Qed.
Time #[global]
Instance into_later_affinely  n P Q:
 (IntoLaterN false n P Q \226\134\146 IntoLaterN false n (<affine> P) (<affine> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_affinely_2.
Time Qed.
Time #[global]
Instance into_later_intuitionistically  n P Q:
 (IntoLaterN false n P Q \226\134\146 IntoLaterN false n (\226\150\161 P) (\226\150\161 Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_intuitionistically_2.
Time Qed.
Time #[global]
Instance into_later_absorbingly  n P Q:
 (IntoLaterN false n P Q \226\134\146 IntoLaterN false n (<absorb> P) (<absorb> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_absorbingly.
Time Qed.
Time #[global]
Instance into_later_plainly  `{BiPlainly PROP} n P 
 Q: (IntoLaterN false n P Q \226\134\146 IntoLaterN false n (\226\150\160 P) (\226\150\160 Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_plainly.
Time Qed.
Time #[global]
Instance into_later_persistently  n P Q:
 (IntoLaterN false n P Q \226\134\146 IntoLaterN false n (<pers> P) (<pers> Q)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_persistently.
Time Qed.
Time #[global]
Instance into_later_embed  `{SbiEmbed PROP PROP'} 
 n P Q: (IntoLaterN false n P Q \226\134\146 IntoLaterN false n \226\142\161 P \226\142\164 \226\142\161 Q \226\142\164).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite embed_laterN.
Time Qed.
Time #[global]
Instance into_laterN_sep_l  n P1 P2 Q1 Q2:
 (IntoLaterN false n P1 Q1
  \226\134\146 MaybeIntoLaterN false n P2 Q2 \226\134\146 IntoLaterN false n (P1 \226\136\151 P2) (Q1 \226\136\151 Q2))
 |10.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}-> {+}->).
Time by rewrite laterN_sep.
Time Qed.
Time #[global]
Instance into_laterN_sep_r  n P P2 Q2:
 (IntoLaterN false n P2 Q2 \226\134\146 IntoLaterN false n (P \226\136\151 P2) (P \226\136\151 Q2)) |11.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>{+}->).
Time by rewrite laterN_sep -(laterN_intro _ P).
Time Qed.
Time #[global]
Instance into_laterN_big_sepL  n {A} (\206\166 \206\168 : nat \226\134\146 A \226\134\146 PROP) 
 (l : list A):
 ((\226\136\128 x k, IntoLaterN false n (\206\166 k x) (\206\168 k x))
  \226\134\146 IntoLaterN false n ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\166 k x) ([\226\136\151 list] k\226\134\166x \226\136\136 l, \206\168 k x)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN =>?).
Time rewrite big_opL_commute.
Time by apply big_sepL_mono.
Time Qed.
Time #[global]
Instance into_laterN_big_sepL2  n {A} {B} (\206\166 \206\168 : nat \226\134\146 A \226\134\146 B \226\134\146 PROP) 
 l1 l2:
 ((\226\136\128 x1 x2 k, IntoLaterN false n (\206\166 k x1 x2) (\206\168 k x1 x2))
  \226\134\146 IntoLaterN false n ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\166 k y1 y2)
      ([\226\136\151 list] k\226\134\166y1;y2 \226\136\136 l1;l2, \206\168 k y1 y2)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN =>?).
Time rewrite -big_sepL2_laterN_2.
Time by apply big_sepL2_mono.
Time Qed.
Time #[global]
Instance into_laterN_big_sepM  n `{Countable K} {A} 
 (\206\166 \206\168 : K \226\134\146 A \226\134\146 PROP) (m : gmap K A):
 ((\226\136\128 x k, IntoLaterN false n (\206\166 k x) (\206\168 k x))
  \226\134\146 IntoLaterN false n ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN =>?).
Time rewrite big_opM_commute.
Time by apply big_sepM_mono.
Time Qed.
Time #[global]
Instance into_laterN_big_sepM2  n `{Countable K} {A} 
 {B} (\206\166 \206\168 : K \226\134\146 A \226\134\146 B \226\134\146 PROP) (m1 : gmap K A) (m2 : gmap K B):
 ((\226\136\128 x1 x2 k, IntoLaterN false n (\206\166 k x1 x2) (\206\168 k x1 x2))
  \226\134\146 IntoLaterN false n ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\166 k x1 x2)
      ([\226\136\151 map] k\226\134\166x1;x2 \226\136\136 m1;m2, \206\168 k x1 x2)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN
 =>H\206\166\206\168).
Time rewrite -big_sepM2_laterN_2.
Time by apply big_sepM2_mono.
Time Qed.
Time #[global]
Instance into_laterN_big_sepS  n `{Countable A} (\206\166 \206\168 : A \226\134\146 PROP)
 (X : gset A):
 ((\226\136\128 x, IntoLaterN false n (\206\166 x) (\206\168 x))
  \226\134\146 IntoLaterN false n ([\226\136\151 set] x \226\136\136 X, \206\166 x) ([\226\136\151 set] x \226\136\136 X, \206\168 x)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN =>?).
Time rewrite big_opS_commute.
Time by apply big_sepS_mono.
Time Qed.
Time #[global]
Instance into_laterN_big_sepMS  n `{Countable A} (\206\166 \206\168 : A \226\134\146 PROP)
 (X : gmultiset A):
 ((\226\136\128 x, IntoLaterN false n (\206\166 x) (\206\168 x))
  \226\134\146 IntoLaterN false n ([\226\136\151 mset] x \226\136\136 X, \206\166 x) ([\226\136\151 mset] x \226\136\136 X, \206\168 x)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoLaterN /MaybeIntoLaterN =>?).
Time rewrite big_opMS_commute.
Time by apply big_sepMS_mono.
Time Qed.
Time End sbi_instances.
