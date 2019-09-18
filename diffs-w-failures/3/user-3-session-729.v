Time From stdpp Require Export telescopes.
Time From iris.bi Require Export bi.
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
Time From stdpp Require Import namespaces.
Time Set Default Proof Using "Type".
Time Import bi.
Time
Inductive modality_action (PROP1 : bi) : bi \226\134\146 Type :=
  | MIEnvIsEmpty : forall {PROP2 : bi}, modality_action PROP1 PROP2
  | MIEnvForall : forall C : PROP1 \226\134\146 Prop, modality_action PROP1 PROP1
  | MIEnvTransform :
      forall {PROP2 : bi} (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop),
      modality_action PROP1 PROP2
  | MIEnvClear : forall {PROP2}, modality_action PROP1 PROP2
  | MIEnvId : modality_action PROP1 PROP1.
Time Arguments MIEnvIsEmpty {_} {_}.
Time Arguments MIEnvForall {_} _.
Time Arguments MIEnvTransform {_} {_} _.
Time Arguments MIEnvClear {_} {_}.
Time Arguments MIEnvId {_}.
Time Notation MIEnvFilter C:= (MIEnvTransform (TCDiag C)).
Time +
Time (<ssreflect_plugin::ssrtclseq@0> rewrite -forall_intro ; first  done).
Time
Definition modality_intuitionistic_action_spec {PROP1} 
  {PROP2} (s : modality_action PROP1 PROP2) : (PROP1 \226\134\146 PROP2) \226\134\146 Prop :=
  match s with
  | MIEnvIsEmpty => \206\187 M, True
  | MIEnvForall C =>
      \206\187 M, (\226\136\128 P, C P \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P)) \226\136\167 (\226\136\128 P Q, M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q))
  | MIEnvTransform C =>
      \206\187 M, (\226\136\128 P Q, C P Q \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 Q)) \226\136\167 (\226\136\128 P Q, M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q))
  | MIEnvClear => \206\187 M, True
  | MIEnvId => \206\187 M, \226\136\128 P, \226\150\161 P \226\138\162 M (\226\150\161 P)
  end.
Time
Definition modality_spatial_action_spec {PROP1} {PROP2}
  (s : modality_action PROP1 PROP2) : (PROP1 \226\134\146 PROP2) \226\134\146 Prop :=
  match s with
  | MIEnvIsEmpty => \206\187 M, True
  | MIEnvForall C => \206\187 M, \226\136\128 P, C P \226\134\146 P \226\138\162 M P
  | MIEnvTransform C => \206\187 M, \226\136\128 P Q, C P Q \226\134\146 P \226\138\162 M Q
  | MIEnvClear => \206\187 M, \226\136\128 P, Absorbing (M P)
  | MIEnvId => \206\187 M, \226\136\128 P, P \226\138\162 M P
  end.
Time (intros p).
Time rewrite (tele_arg_O_inv p) /= //.
Time -
Time (simpl).
Time (apply (anti_symm _); apply forall_intro; intros a).
Time
Record modality_mixin {PROP1 PROP2 : bi} (M : PROP1 \226\134\146 PROP2)
(iaction saction : modality_action PROP1 PROP2) :={
 modality_mixin_intuitionistic :
  modality_intuitionistic_action_spec iaction M;
 modality_mixin_spatial : modality_spatial_action_spec saction M;
 modality_mixin_emp : emp \226\138\162 M emp;
 modality_mixin_mono : forall P Q, (P \226\138\162 Q) \226\134\146 M P \226\138\162 M Q;
 modality_mixin_sep : forall P Q, M P \226\136\151 M Q \226\138\162 M (P \226\136\151 Q)}.
Time
Record modality (PROP1 PROP2 : bi) :=
 Modality {modality_car :> PROP1 \226\134\146 PROP2;
           modality_intuitionistic_action : modality_action PROP1 PROP2;
           modality_spatial_action : modality_action PROP1 PROP2;
           modality_mixin_of :
            modality_mixin modality_car modality_intuitionistic_action
              modality_spatial_action}.
Time Arguments Modality {_} {_} _ {_} {_} _.
Time Arguments modality_intuitionistic_action {_} {_} _.
Time Arguments modality_spatial_action {_} {_} _.
Time Section modality.
Time Context {PROP1} {PROP2} (M : modality PROP1 PROP2).
Time +
Time rewrite /= -IH.
Time
Lemma modality_intuitionistic_transform C P Q :
  modality_intuitionistic_action M = MIEnvTransform C \226\134\146 C P Q \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time
Lemma modality_and_transform C P Q :
  modality_intuitionistic_action M = MIEnvTransform C \226\134\146 M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time (apply forall_intro; intros p).
Time by rewrite (forall_elim (TargS a p)).
Time +
Time move /tele_arg_inv: {}a {} =>[x [pf {+}->]] {a} /=.
Time setoid_rewrite  <- IH.
Time Qed.
Time
Lemma modality_spatial_transform C P Q :
  modality_spatial_action M = MIEnvTransform C \226\134\146 C P Q \226\134\146 P \226\138\162 M Q.
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time rewrite 2!forall_elim.
Time Qed.
Time
Lemma modality_spatial_clear P :
  modality_spatial_action M = MIEnvClear \226\134\146 Absorbing (M P).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time Lemma modality_emp : emp \226\138\162 M emp.
Time Proof.
Time (eapply modality_mixin_emp, modality_mixin_of).
Time Qed.
Time Lemma modality_mono P Q : (P \226\138\162 Q) \226\134\146 M P \226\138\162 M Q.
Time done.
Time Qed.
Time Proof.
Time (eapply modality_mixin_mono, modality_mixin_of).
Time Qed.
Time Lemma modality_sep P Q : M P \226\136\151 M Q \226\138\162 M (P \226\136\151 Q).
Time Proof.
Time (eapply modality_mixin_sep, modality_mixin_of).
Time Qed.
Time #[global]Instance modality_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) M).
Time Proof.
Time (intros P Q).
Time (apply modality_mono).
Time Qed.
Time #[global]
Instance modality_flip_mono' : (Proper (flip (\226\138\162) ==> flip (\226\138\162)) M).
Time Proof.
Time (intros P Q).
Time (apply modality_mono).
Time Qed.
Time #[global]Instance modality_proper : (Proper ((\226\137\161) ==> (\226\137\161)) M).
Time Proof.
Time (intros P Q).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !equiv_spec =>- 
  [? ?]; eauto using modality_mono).
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
Time Qed.
Time End modality.
Time Section modality1.
Time Context {PROP} (M : modality PROP PROP).
Time
Lemma modality_intuitionistic_forall C P :
  modality_intuitionistic_action M = MIEnvForall C \226\134\146 C P \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P).
Time -
Time (simpl).
Time (apply (anti_symm _); apply exist_elim).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time +
Time (intros p).
Time move /tele_arg_inv: {}p {} =>[x [pf {+}->]] {p} /=.
Time by rewrite -exist_intro -IH -exist_intro.
Time Qed.
Time
Lemma modality_and_forall C P Q :
  modality_intuitionistic_action M = MIEnvForall C \226\134\146 M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time +
Time (intros x).
Time rewrite /= -IH.
Time Qed.
Time
Lemma modality_intuitionistic_id P :
  modality_intuitionistic_action M = MIEnvId \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time (apply exist_elim; intros p).
Time by rewrite -(exist_intro (TargS x p)).
Time
Lemma modality_spatial_forall C P :
  modality_spatial_action M = MIEnvForall C \226\134\146 C P \226\134\146 P \226\138\162 M P.
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time
Lemma modality_spatial_id P : modality_spatial_action M = MIEnvId \226\134\146 P \226\138\162 M P.
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Qed.
Time #[global]
Instance bi_tforall_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_tforall PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_tforall_forall.
Time Qed.
Time
Lemma modality_intuitionistic_forall_big_and C Ps :
  modality_intuitionistic_action M = MIEnvForall C
  \226\134\146 Forall C Ps \226\134\146 \226\150\161 [\226\136\167] Ps \226\138\162 M (\226\150\161 [\226\136\167] Ps).
Time Proof.
Time (induction 2 as [| P Ps ? _ IH]; simpl).
Time -
Time by rewrite intuitionistically_True_emp -modality_emp.
Time rewrite EQ //.
Time -
Time rewrite intuitionistically_and -modality_and_forall // -IH.
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
Instance bi_texist_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_texist PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_texist_exist.
Time by rewrite {+1}(modality_intuitionistic_forall _ P).
Time rewrite EQ //.
Time Qed.
Time #[global]
Instance bi_texist_proper :
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_texist PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_texist_exist.
Time Qed.
Time
Lemma modality_spatial_forall_big_sep C Ps :
  modality_spatial_action M = MIEnvForall C
  \226\134\146 Forall C Ps \226\134\146 [\226\136\151] Ps \226\138\162 M ([\226\136\151] Ps).
Time Proof.
Time (induction 2 as [| P Ps ? _ IH]; simpl).
Time -
Time by rewrite -modality_emp.
Time rewrite EQ //.
Time -
Time by rewrite -modality_sep -IH {+1}(modality_spatial_forall _ P).
Time Qed.
Time End telescope_quantifiers.
Time Qed.
Time End modality1.
Time
Lemma modality_id_mixin {PROP : bi} :
  modality_mixin (@id PROP) MIEnvId MIEnvId.
Time Proof.
Time (split; simpl; eauto).
Time Qed.
Time
Definition modality_id {PROP : bi} := Modality (@id PROP) modality_id_mixin.
