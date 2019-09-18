Time From iris.bi Require Export bi.
Time From iris.proofmode Require Import classes class_instances_bi.
Time Set Default Proof Using "Type".
Time
Class Fractional {PROP : bi} (\206\166 : Qp \226\134\146 PROP) :=
    fractional : forall p q, \206\166 (p + q)%Qp \226\138\163\226\138\162 \206\166 p \226\136\151 \206\166 q.
Time Arguments Fractional {_} _%I : simpl never.
Time
Class AsFractional {PROP : bi} (P : PROP) (\206\166 : Qp \226\134\146 PROP) (q : Qp) :={
 as_fractional : P \226\138\163\226\138\162 \206\166 q;
 as_fractional_fractional :> Fractional \206\166}.
Time Arguments AsFractional {_} _%I _%I _%Qp.
Time Arguments fractional {_} {_} {_} _ _.
Time Hint Mode AsFractional - + - -: typeclass_instances.
Time Hint Mode AsFractional - - + -: typeclass_instances.
Time Section fractional.
Time Context {PROP : bi}.
Time Implicit Types P Q : PROP.
Time Implicit Type \206\166 : Qp \226\134\146 PROP.
Time Implicit Type q : Qp.
Time
Lemma fractional_split P P1 P2 \206\166 q1 q2 :
  AsFractional P \206\166 (q1 + q2)
  \226\134\146 AsFractional P1 \206\166 q1 \226\134\146 AsFractional P2 \206\166 q2 \226\134\146 P \226\138\163\226\138\162 P1 \226\136\151 P2.
Time Proof.
Time by move  {}=>- [{+}-> {+}->] [{+}-> _] [{+}-> _].
Time Qed.
Time
Lemma fractional_split_1 P P1 P2 \206\166 q1 q2 :
  AsFractional P \206\166 (q1 + q2)
  \226\134\146 AsFractional P1 \206\166 q1 \226\134\146 AsFractional P2 \206\166 q2 \226\134\146 P -\226\136\151 P1 \226\136\151 P2.
Time Proof.
Time (intros).
Time by rewrite -(fractional_split P).
Time Qed.
Time
Lemma fractional_split_2 P P1 P2 \206\166 q1 q2 :
  AsFractional P \206\166 (q1 + q2)
  \226\134\146 AsFractional P1 \206\166 q1 \226\134\146 AsFractional P2 \206\166 q2 \226\134\146 P1 -\226\136\151 P2 -\226\136\151 P.
Time Proof.
Time (intros).
Time (apply bi.wand_intro_r).
Time by rewrite -(fractional_split P).
Time Qed.
Time
Lemma fractional_half P P12 \206\166 q :
  AsFractional P \206\166 q \226\134\146 AsFractional P12 \206\166 (q / 2) \226\134\146 P \226\138\163\226\138\162 P12 \226\136\151 P12.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite -{+1}
 (Qp_div_2 q) =>- [{+}-> {+}->] [{+}-> _].
Time Qed.
Time
Lemma fractional_half_1 P P12 \206\166 q :
  AsFractional P \206\166 q \226\134\146 AsFractional P12 \206\166 (q / 2) \226\134\146 P -\226\136\151 P12 \226\136\151 P12.
Time Proof.
Time (intros).
Time by rewrite -(fractional_half P).
Time Qed.
Time
Lemma fractional_half_2 P P12 \206\166 q :
  AsFractional P \206\166 q \226\134\146 AsFractional P12 \206\166 (q / 2) \226\134\146 P12 -\226\136\151 P12 -\226\136\151 P.
Time Proof.
Time (intros).
Time (apply bi.wand_intro_r).
Time by rewrite -(fractional_half P).
Time Qed.
Time #[global]
Instance persistent_fractional  P:
 (Persistent P \226\134\146 Absorbing P \226\134\146 Fractional (\206\187 _, P)).
Time Proof.
Time (intros ? ? q q').
Time by apply bi.persistent_sep_dup.
Time Qed.
Time #[global]
Instance fractional_sep  \206\166 \206\168:
 (Fractional \206\166 \226\134\146 Fractional \206\168 \226\134\146 Fractional (\206\187 q, \206\166 q \226\136\151 \206\168 q)%I).
Time Proof.
Time (intros ? ? q q').
Time rewrite !fractional -!assoc.
Time f_equiv.
Time rewrite !assoc.
Time f_equiv.
Time by rewrite comm.
Time Qed.
Time #[global]
Instance fractional_big_sepL  {A} l \206\168:
 ((\226\136\128 k (x : A), Fractional (\206\168 k x))
  \226\134\146 Fractional (PROP:=PROP) (\206\187 q, [\226\136\151 list] k\226\134\166x \226\136\136 l, \206\168 k x q)%I).
Time Proof.
Time (intros ? q q').
Time rewrite -big_sepL_sep.
Time by setoid_rewrite fractional.
Time Qed.
Time #[global]
Instance fractional_big_sepM  `{Countable K} {A} (m : gmap K A) 
 \206\168:
 ((\226\136\128 k (x : A), Fractional (\206\168 k x))
  \226\134\146 Fractional (PROP:=PROP) (\206\187 q, [\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x q)%I).
Time Proof.
Time (intros ? q q').
Time rewrite -big_sepM_sep.
Time by setoid_rewrite fractional.
Time Qed.
Time #[global]
Instance fractional_big_sepS  `{Countable A} (X : gset A) 
 \206\168:
 ((\226\136\128 x, Fractional (\206\168 x))
  \226\134\146 Fractional (PROP:=PROP) (\206\187 q, [\226\136\151 set] x \226\136\136 X, \206\168 x q)%I).
Time Proof.
Time (intros ? q q').
Time rewrite -big_sepS_sep.
Time by setoid_rewrite fractional.
Time Qed.
Time #[global]
Instance fractional_big_sepMS  `{Countable A} (X : gmultiset A) 
 \206\168:
 ((\226\136\128 x, Fractional (\206\168 x))
  \226\134\146 Fractional (PROP:=PROP) (\206\187 q, [\226\136\151 mset] x \226\136\136 X, \206\168 x q)%I).
Time Proof.
Time (intros ? q q').
Time rewrite -big_sepMS_sep.
Time by setoid_rewrite fractional.
Time Qed.
Time #[global]
Instance mult_fractional_l  \206\166 \206\168 p:
 ((\226\136\128 q, AsFractional (\206\166 q) \206\168 (q * p)) \226\134\146 Fractional \206\166).
Time Proof.
Time (intros H q q').
Time (rewrite !as_fractional, Qp_mult_plus_distr_l).
Time by apply H.
Time Qed.
Time #[global]
Instance mult_fractional_r  \206\166 \206\168 p:
 ((\226\136\128 q, AsFractional (\206\166 q) \206\168 (p * q)) \226\134\146 Fractional \206\166).
Time Proof.
Time (intros H q q').
Time (rewrite !as_fractional, Qp_mult_plus_distr_r).
Time by apply H.
Time Qed.
Time
Instance mult_as_fractional_l  P \206\166 p q:
 (AsFractional P \206\166 (q * p) \226\134\146 AsFractional P (\206\187 q, \206\166 (q * p)%Qp) q).
Time Proof.
Time (intros H).
Time split.
Time (apply H).
Time (eapply (mult_fractional_l _ \206\166 p)).
Time split.
Time done.
Time (apply H).
Time Qed.
Time
Instance mult_as_fractional_r  P \206\166 p q:
 (AsFractional P \206\166 (p * q) \226\134\146 AsFractional P (\206\187 q, \206\166 (p * q)%Qp) q).
Time Proof.
Time (intros H).
Time split.
Time (apply H).
Time (eapply (mult_fractional_r _ \206\166 p)).
Time split.
Time done.
Time (apply H).
Time Qed.
Time #[global]
Instance from_and_fractional_fwd  P P1 P2 \206\166 q1 q2:
 (AsFractional P \206\166 (q1 + q2)
  \226\134\146 AsFractional P1 \206\166 q1 \226\134\146 AsFractional P2 \206\166 q2 \226\134\146 FromSep P P1 P2).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>- 
 [{+}-> {+}->] [{+}-> _] [{+}-> _].
Time Qed.
Time #[global]
Instance from_sep_fractional_bwd  P P1 P2 \206\166 q1 q2:
 (AsFractional P1 \206\166 q1
  \226\134\146 AsFractional P2 \206\166 q2 \226\134\146 AsFractional P \206\166 (q1 + q2) \226\134\146 FromSep P P1 P2) |10.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>- 
 [{+}-> _] [{+}-> {+}<-] [{+}-> _].
Time Qed.
Time #[global]
Instance from_sep_fractional_half_fwd  P Q \206\166 q:
 (AsFractional P \206\166 q \226\134\146 AsFractional Q \206\166 (q / 2) \226\134\146 FromSep P Q Q) |10.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromSep -{+1}
 (Qp_div_2 q) =>- [{+}-> {+}->] [{+}-> _].
Time Qed.
Time #[global]
Instance from_sep_fractional_half_bwd  P Q \206\166 q:
 (AsFractional P \206\166 (q / 2) \226\134\146 AsFractional Q \206\166 q \226\134\146 FromSep Q P P).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromSep =>- 
 [{+}-> {+}<-] [{+}-> _]).
Time by rewrite Qp_div_2.
Time Qed.
Time #[global]
Instance into_sep_fractional  P P1 P2 \206\166 q1 q2:
 (AsFractional P \206\166 (q1 + q2)
  \226\134\146 AsFractional P1 \206\166 q1 \226\134\146 AsFractional P2 \206\166 q2 \226\134\146 IntoSep P P1 P2).
Time Proof.
Time (intros).
Time rewrite /IntoSep [P]fractional_split //.
Time Qed.
Time #[global]
Instance into_sep_fractional_half  P Q \206\166 q:
 (AsFractional P \206\166 q \226\134\146 AsFractional Q \206\166 (q / 2) \226\134\146 IntoSep P Q Q) |100.
Time Proof.
Time (intros).
Time rewrite /IntoSep [P]fractional_half //.
Time Qed.
Time
Inductive FrameFractionalHyps (p : bool) (R : PROP) 
(\206\166 : Qp \226\134\146 PROP) (RES : PROP) : Qp \226\134\146 Qp \226\134\146 Prop :=
  | frame_fractional_hyps_l :
      forall Q q q' r,
      Frame p R (\206\166 q) Q
      \226\134\146 MakeSep Q (\206\166 q') RES \226\134\146 FrameFractionalHyps p R \206\166 RES r (q + q')
  | frame_fractional_hyps_r :
      forall Q q q' r,
      Frame p R (\206\166 q') Q
      \226\134\146 MakeSep Q (\206\166 q) RES \226\134\146 FrameFractionalHyps p R \206\166 RES r (q + q')
  | frame_fractional_hyps_half :
      forall q,
      AsFractional RES \206\166 (q / 2) \226\134\146 FrameFractionalHyps p R \206\166 RES (q / 2) q.
Time Existing Class FrameFractionalHyps.
Time #[global]
Existing Instances
 frame_fractional_hyps_l, frame_fractional_hyps_r, frame_fractional_hyps_half.
Time #[global]
Instance frame_fractional  p R r \206\166 P q RES:
 (AsFractional R \206\166 r
  \226\134\146 AsFractional P \206\166 q \226\134\146 FrameFractionalHyps p R \206\166 RES r q \226\134\146 Frame p R P RES).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>- [HR _] [{+}-> ?] H).
Time
(<ssreflect_plugin::ssrtclintros@0> revert H HR =>-
 [Q q0 q0' r0|Q q0 q0' r0|q0]).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite fractional /Frame /MakeSep
 =>{+}<- {+}<-).
Time by rewrite assoc.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> <ssreflect_plugin::ssrtclintros@0>
 rewrite fractional /Frame /MakeSep =>{+}<- {+}<- =>_).
Time by rewrite (comm _ Q (\206\166 q0)) !assoc (comm _ (\206\166 _)).
Time -
Time move  {}=>- [{+}-> _] {+}->.
Time by rewrite bi.intuitionistically_if_elim -fractional Qp_div_2.
Time Qed.
Time End fractional.
