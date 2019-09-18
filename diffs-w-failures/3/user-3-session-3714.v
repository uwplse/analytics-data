Time From iris.bi Require Export bi.
Time From stdpp Require Export telescopes.
Time From iris.base_logic Require Export bi.
Time From stdpp Require Import gmap.
Time From iris.bi Require Export bi.
Time From iris.bi Require Export bi.
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
Time Set Default Proof Using "Type*".
Time Import bi.
Time
Definition bi_texist {PROP : bi} {TT : tele} (\206\168 : TT \226\134\146 PROP) : PROP :=
  tele_fold (@bi_exist PROP) (\206\187 x, x) (tele_bind \206\168).
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
Time
Record modality_mixin {PROP1 PROP2 : bi} (M : PROP1 \226\134\146 PROP2)
(iaction saction : modality_action PROP1 PROP2) :={
 modality_mixin_intuitionistic :
  modality_intuitionistic_action_spec iaction M;
 modality_mixin_spatial : modality_spatial_action_spec saction M;
 modality_mixin_emp : emp \226\138\162 M emp;
 modality_mixin_mono : forall P Q, (P \226\138\162 Q) \226\134\146 M P \226\138\162 M Q;
 modality_mixin_sep : forall P Q, M P \226\136\151 M Q \226\138\162 M (P \226\136\151 Q)}.
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
Time (induction TT as [| X ft IH]).
Time -
Time (simpl).
Time (apply (anti_symm _)).
Time +
Time by rewrite (forall_elim TargO).
Time
Lemma modality_intuitionistic_transform C P Q :
  modality_intuitionistic_action M = MIEnvTransform C \226\134\146 C P Q \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time +
Time (<ssreflect_plugin::ssrtclseq@0> rewrite -forall_intro ; first  done).
Time Qed.
Time
Lemma modality_and_transform C P Q :
  modality_intuitionistic_action M = MIEnvTransform C \226\134\146 M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q).
Time Proof.
Time (intros p).
Time rewrite (tele_arg_O_inv p) /= //.
Time -
Time (simpl).
Time (apply (anti_symm _); apply forall_intro; intros a).
Time (destruct M as [? ? ? []]; naive_solver).
Time +
Time rewrite /= -IH.
Time Qed.
Time
Lemma modality_spatial_transform C P Q :
  modality_spatial_action M = MIEnvTransform C \226\134\146 C P Q \226\134\146 P \226\138\162 M Q.
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Set Default Proof Using "Type".
Time Import bi.
Time Module bi_reflection.
Time Section bi_reflection.
Time Context {PROP : bi}.
Time
Inductive expr :=
  | EEmp : expr
  | EVar : nat \226\134\146 expr
  | ESep : expr \226\134\146 expr \226\134\146 expr.
Time
Fixpoint eval (\206\163 : list PROP) (e : expr) : PROP :=
  match e with
  | EEmp => emp
  | EVar n => default emp (\206\163 !! n)
  | ESep e1 e2 => eval \206\163 e1 \226\136\151 eval \206\163 e2
  end%I.
Time
Fixpoint flatten (e : expr) : list nat :=
  match e with
  | EEmp => []
  | EVar n => [n]
  | ESep e1 e2 => flatten e1 ++ flatten e2
  end.
Time Notation eval_list \206\163 l:= ([\226\136\151 list] n \226\136\136 l, default emp (\206\163 !! n))%I.
Time Lemma eval_flatten \206\163 e : eval \206\163 e \226\138\163\226\138\162 eval_list \206\163 (flatten e).
Time Proof.
Time
(induction e as [| | e1 IH1 e2 IH2]; rewrite /= ?right_id ?big_opL_app ?IH1
  ?IH2 //).
Time (apply forall_intro; intros p).
Time by rewrite (forall_elim (TargS a p)).
Time Qed.
Time
Lemma modality_spatial_clear P :
  modality_spatial_action M = MIEnvClear \226\134\146 Absorbing (M P).
Time Proof.
Time From iris.bi Require Export bi.
Time (destruct M as [? ? ? []]; naive_solver).
Time +
Time move /tele_arg_inv: {}a {} =>[x [pf {+}->]] {a} /=.
Time setoid_rewrite  <- IH.
Time Qed.
Time Lemma modality_emp : emp \226\138\162 M emp.
Time Proof.
Time (eapply modality_mixin_emp, modality_mixin_of).
Time Qed.
Time Lemma modality_mono P Q : (P \226\138\162 Q) \226\134\146 M P \226\138\162 M Q.
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
Time Qed.
Time #[global]
Instance uPred_valid_mono : (Proper ((\226\138\162) ==> impl) (@uPred_valid M)).
Time Proof.
Time solve_proper.
Time rewrite 2!forall_elim.
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
Time
Lemma persistently_cmra_valid_1 {A : cmraT} (a : A) :
  \226\156\147 a \226\138\162 <pers> (\226\156\147 a : uPred M).
Time Proof.
Time by rewrite {+1}plainly_cmra_valid_1 plainly_elim_persistently.
Time Qed.
Time End modality.
Time done.
Time Qed.
Time Section modality1.
Time Context {PROP} (M : modality PROP PROP).
Time
Lemma modality_intuitionistic_forall C P :
  modality_intuitionistic_action M = MIEnvForall C \226\134\146 C P \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
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
Time
Lemma modality_and_forall C P Q :
  modality_intuitionistic_action M = MIEnvForall C \226\134\146 M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time -
Time (simpl).
Time (apply (anti_symm _); apply exist_elim).
Time +
Time (intros p).
Time move /tele_arg_inv: {}p {} =>[x [pf {+}->]] {p} /=.
Time Qed.
Time
Lemma intuitionistically_ownM (a : M) :
  CoreId a \226\134\146 \226\150\161 uPred_ownM a \226\138\163\226\138\162 uPred_ownM a.
Time by rewrite -exist_intro -IH -exist_intro.
Time Qed.
Time
Lemma modality_intuitionistic_id P :
  modality_intuitionistic_action M = MIEnvId \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 P).
Time Proof.
Time (destruct M as [? ? ? []]; naive_solver).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /bi_intuitionistically
  affine_affinely =>?; apply (anti_symm _);
  [ by rewrite persistently_elim |  ]).
Time Qed.
Time
Lemma flatten_entails `{BiAffine PROP} \206\163 e1 e2 :
  flatten e2 \226\138\134+ flatten e1 \226\134\146 eval \206\163 e1 \226\138\162 eval \206\163 e2.
Time Proof.
Time (intros).
Time rewrite !eval_flatten.
Time Qed.
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
Time by rewrite {+1}persistently_ownM_core core_id_core.
Time +
Time (intros x).
Time rewrite /= -IH.
Time Qed.
Time
Lemma modality_intuitionistic_forall_big_and C Ps :
  modality_intuitionistic_action M = MIEnvForall C
  \226\134\146 Forall C Ps \226\134\146 \226\150\161 [\226\136\167] Ps \226\138\162 M (\226\150\161 [\226\136\167] Ps).
Time by apply big_sepL_submseteq.
Time Qed.
Time Proof.
Time (induction 2 as [| P Ps ? _ IH]; simpl).
Time -
Time by rewrite intuitionistically_True_emp -modality_emp.
Time
Lemma flatten_equiv \206\163 e1 e2 :
  flatten e2 \226\137\161\226\130\154 flatten e1 \226\134\146 eval \206\163 e1 \226\138\163\226\138\162 eval \206\163 e2.
Time Proof.
Time (intros He).
Time by rewrite !eval_flatten He.
Time (apply exist_elim; intros p).
Time by rewrite -(exist_intro (TargS x p)).
Time Qed.
Time #[global]
Instance bi_tforall_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_tforall PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_tforall_forall.
Time Qed.
Time
Fixpoint prune (e : expr) : expr :=
  match e with
  | EEmp => EEmp
  | EVar n => EVar n
  | ESep e1 e2 =>
      match prune e1, prune e2 with
      | EEmp, e2' => e2'
      | e1', EEmp => e1'
      | e1', e2' => ESep e1' e2'
      end
  end.
Time Lemma flatten_prune e : flatten (prune e) = flatten e.
Time Proof.
Time -
Time rewrite intuitionistically_and -modality_and_forall // -IH.
Time (induction e as [| | e1 IH1 e2 IH2]; simplify_eq /=; auto).
Time Qed.
Time rewrite -IH1 -IH2.
Time by repeat case_match; rewrite ?right_id_L.
Time rewrite EQ //.
Time Lemma ownM_invalid (a : M) : \194\172 \226\156\147{0} a \226\134\146 uPred_ownM a \226\138\162 False.
Time Proof.
Time by intros; rewrite ownM_valid cmra_valid_elim.
Time Qed.
Time Lemma prune_correct \206\163 e : eval \206\163 (prune e) \226\138\163\226\138\162 eval \206\163 e.
Time Proof.
Time Qed.
Time #[global]
Instance bi_tforall_proper :
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_tforall PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_tforall_forall.
Time Qed.
Time by rewrite !eval_flatten flatten_prune.
Time #[global]
Instance ownM_mono : (Proper (flip (\226\137\188) ==> (\226\138\162)) (@uPred_ownM M)).
Time Proof.
Time (intros a b [b' ->]).
Time rewrite EQ //.
Time by rewrite {+1}(modality_intuitionistic_forall _ P).
Time by rewrite ownM_op sep_elim_l.
Time Qed.
Time
Fixpoint cancel_go (n : nat) (e : expr) : option expr :=
  match e with
  | EEmp => None
  | EVar n' => if decide (n = n') then Some EEmp else None
  | ESep e1 e2 =>
      match cancel_go n e1 with
      | Some e1' => Some (ESep e1' e2)
      | None => ESep e1 <$> cancel_go n e2
      end
  end.
Time
Definition cancel (ns : list nat) (e : expr) : option expr :=
  prune <$> fold_right (mbind \226\136\152 cancel_go) (Some e) ns.
Time
Lemma flatten_cancel_go e e' n :
  cancel_go n e = Some e' \226\134\146 flatten e \226\137\161\226\130\154 n :: flatten e'.
Time Proof.
Time
(revert e'; induction e as [| | e1 IH1 e2 IH2]; intros;
  repeat simplify_option_eq || case_match; auto).
Time Qed.
Time #[global]
Instance bi_texist_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_texist PROP TT)).
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
Time -
Time by rewrite -modality_sep -IH {+1}(modality_spatial_forall _ P).
Time Qed.
Time Lemma ownM_unit' : uPred_ownM \206\181 \226\138\163\226\138\162 True.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply (anti_symm _) ; first  by
 apply pure_intro).
Time (apply ownM_unit).
Time Qed.
Time Lemma plainly_cmra_valid {A : cmraT} (a : A) : \226\150\160 \226\156\147 a \226\138\163\226\138\162 \226\156\147 a.
Time Proof.
Time (apply (anti_symm _), plainly_cmra_valid_1).
Time rewrite EQ //.
Time (apply plainly_elim, _).
Time Qed.
Time Lemma intuitionistically_cmra_valid {A : cmraT} (a : A) : \226\150\161 \226\156\147 a \226\138\163\226\138\162 \226\156\147 a.
Time Proof.
Time rewrite /bi_intuitionistically affine_affinely.
Time Qed.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; apply (anti_symm _) ; first  by
 rewrite persistently_elim).
Time -
Time #[global]
Instance bi_texist_proper :
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_texist PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_texist_exist.
Time by rewrite IH1 //.
Time rewrite EQ //.
Time apply : {}persistently_cmra_valid_1 {}.
Time Qed.
Time Lemma bupd_ownM_update x y : x ~~> y \226\134\146 uPred_ownM x \226\138\162 |==> uPred_ownM y.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; rewrite (bupd_ownM_updateP _ (y =))
 ; last  by apply cmra_update_updateP).
Time -
Time by rewrite IH2 // Permutation_middle.
Time Qed.
Time End telescope_quantifiers.
Time Qed.
Time End modality1.
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply bupd_mono, exist_elim =>y';
  <ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>{+}->.
Time
Lemma modality_id_mixin {PROP : bi} :
  modality_mixin (@id PROP) MIEnvId MIEnvId.
Time Proof.
Time (split; simpl; eauto).
Time Qed.
Time #[global]
Instance valid_timeless  {A : cmraT} `{!CmraDiscrete A} 
 (a : A): (Timeless (\226\156\147 a : uPred M)%I).
Time Proof.
Time rewrite /Timeless !discrete_valid.
Time Qed.
Time
Definition modality_id {PROP : bi} := Modality (@id PROP) modality_id_mixin.
Time Qed.
Time
Lemma flatten_cancel e e' ns :
  cancel ns e = Some e' \226\134\146 flatten e \226\137\161\226\130\154 ns ++ flatten e'.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /cancel fmap_Some =>-
  [{e'} e' [He {+}->]]; rewrite flatten_prune).
Time
(revert e' He; <ssreflect_plugin::ssrtclintros@0> 
  induction ns as [| n ns IH] =>e' He; simplify_option_eq; auto).
Time (apply (timeless _)).
Time Qed.
Time #[global]
Instance ownM_timeless  (a : M): (Discrete a \226\134\146 Timeless (uPred_ownM a)).
Time Proof.
Time (intros ?).
Time rewrite /Timeless later_ownM.
Time (rewrite Permutation_middle -flatten_cancel_go //; eauto).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>b).
Time
rewrite (timeless (a \226\137\161 b)) (except_0_intro (uPred_ownM b)) -except_0_and.
Time Qed.
Time
Lemma cancel_entails \206\163 e1 e2 e1' e2' ns :
  cancel ns e1 = Some e1'
  \226\134\146 cancel ns e2 = Some e2'
    \226\134\146 (eval \206\163 e1' \226\138\162 eval \206\163 e2') \226\134\146 eval \206\163 e1 \226\138\162 eval \206\163 e2.
Time Proof.
Time (intros ? ?).
Time rewrite !eval_flatten.
Time (apply except_0_mono).
Time rewrite internal_eq_sym.
Time
(rewrite (flatten_cancel e1 e1' ns) // (flatten_cancel e2 e2' ns) //; csimpl).
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
Time rewrite !big_opL_app.
Time (apply persistently_ownM_core).
Time Qed.
Time #[global]
Instance uPred_ownM_sep_homomorphism :
 (MonoidHomomorphism op uPred_sep (\226\137\161) (@uPred_ownM M)).
Time Proof.
Time (split; [ split; try apply _ |  ]).
Time (apply sep_mono_r).
Time Qed.
Time (apply ownM_op).
Time (apply ownM_unit').
Time Qed.
Time
Lemma bupd_plain_soundness P `{!Plain P} :
  bi_emp_valid (|==> P) \226\134\146 bi_emp_valid P.
Time
Fixpoint to_expr (l : list nat) : expr :=
  match l with
  | [] => EEmp
  | [n] => EVar n
  | n :: l => ESep (EVar n) (to_expr l)
  end.
Time Arguments to_expr !_ / : simpl nomatch.
Time Lemma eval_to_expr \206\163 l : eval \206\163 (to_expr l) \226\138\163\226\138\162 eval_list \206\163 l.
Time Proof.
Time (induction l as [| n1 [| n2 l] IH]; csimpl; rewrite ?right_id //).
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
Time by rewrite IH.
Time Qed.
Time
Lemma split_l \206\163 e ns e' :
  cancel ns e = Some e' \226\134\146 eval \206\163 e \226\138\163\226\138\162 eval \206\163 (to_expr ns) \226\136\151 eval \206\163 e'.
Time Proof.
Time (intros He%flatten_cancel).
Time by rewrite eval_flatten He big_opL_app eval_to_expr eval_flatten.
Time Qed.
Time
Lemma split_r \206\163 e ns e' :
  cancel ns e = Some e' \226\134\146 eval \206\163 e \226\138\163\226\138\162 eval \206\163 e' \226\136\151 eval \206\163 (to_expr ns).
Time Proof.
Time (intros).
Time rewrite /= comm.
Time by apply split_l.
Time Qed.
Time Class Quote (\206\1631 \206\1632 : list PROP) (P : PROP) (e : expr) :={}.
Time #[global]Instance quote_True  \206\163: (Quote \206\163 \206\163 emp%I EEmp) := { }.
Time #[global]
Instance quote_var  \206\1631 \206\1632 P i:
 (rlist.QuoteLookup \206\1631 \206\1632 P i \226\134\146 Quote \206\1631 \206\1632 P (EVar i)) |1000 := { }.
Time #[global]
Instance quote_sep  \206\1631 \206\1632 \206\1633 P1 P2 e1 e2:
 (Quote \206\1631 \206\1632 P1 e1
  \226\134\146 Quote \206\1632 \206\1633 P2 e2 \226\134\146 Quote \206\1631 \206\1633 (P1 \226\136\151 P2)%I (ESep e1 e2)) := { }.
Time Class QuoteArgs (\206\163 : list PROP) (Ps : list PROP) (ns : list nat) :={}.
Time #[global]Instance quote_args_nil  \206\163: (QuoteArgs \206\163 nil nil) := { }.
Time #[global]
Instance quote_args_cons  \206\163 Ps P ns n:
 (rlist.QuoteLookup \206\163 \206\163 P n
  \226\134\146 QuoteArgs \206\163 Ps ns \226\134\146 QuoteArgs \206\163 (P :: Ps) (n :: ns)) := { }.
Time End bi_reflection.
Time
Ltac
 quote :=
  match goal with
  | |- ?P1 \226\138\162 ?P2 =>
        lazymatch type of (_ : Quote [] _ P1 _) with
        | Quote _ ?\206\1632 _ ?e1 =>
            lazymatch type of (_ : Quote \206\1632 _ P2 _) with
            | Quote _ ?\206\1633 _ ?e2 =>
                change_no_check (eval \206\1633 e1 \226\138\162 eval \206\1633 e2)
            end
        end
  end.
Time
Ltac
 quote_l :=
  match goal with
  | |- ?P1 \226\138\162 ?P2 =>
        lazymatch type of (_ : Quote [] _ P1 _) with
        | Quote _ ?\206\1632 _ ?e1 => change_no_check (eval \206\1632 e1 \226\138\162 P2)
        end
  end.
Time End bi_reflection.
Time
Tactic Notation "solve_sep_entails" :=
 (bi_reflection.quote; (first
   [ apply bi_reflection.flatten_entails
   | apply equiv_entails, bi_reflection.flatten_equiv ]);
   apply (bool_decide_unpack _); vm_compute; exact Logic.I).
Time
Tactic Notation "solve_sep_equiv" :=
 (bi_reflection.quote; apply bi_reflection.flatten_equiv;
   apply (bool_decide_unpack _); vm_compute; exact Logic.I).
Time
Ltac
 close_uPreds Ps tac :=
  let PROP := match goal with
              | |- @bi_entails ?PROP _ _ => PROP
              end in
  let rec go Ps Qs :=
   lazymatch Ps with
   | [] =>
       let Qs' := eval cbv[reverse rev_append] in (reverse Qs) in
       tac Qs'
   | ?P :: ?Ps => find_pat P ltac:(fun Q => go Ps (Q :: Qs))
   end
  in
  try match Ps with
      | [] => unify Ps @nil PROP
      end; go Ps (@nil PROP).
Time
Tactic Notation "cancel" constr(Ps) :=
 (bi_reflection.quote;
   (let \206\163 := match goal with
             | |- bi_reflection.eval ?\206\163 _ \226\138\162 _ => \206\163
             end in
    let ns' :=
     lazymatch type of (_ : bi_reflection.QuoteArgs \206\163 Ps _)
     with
     | bi_reflection.QuoteArgs _ _ ?ns' => ns'
     end
    in
    eapply bi_reflection.cancel_entails with (ns := ns');
     [ compute; reflexivity | compute; reflexivity | simpl ])).
Time
Tactic Notation "ecancel" open_constr(Ps) :=
 (close_uPreds Ps ltac:(fun Qs => cancel Qs)).
Time
Tactic Notation "to_front" open_constr(Ps) :=
 (close_uPreds Ps
   ltac:(fun Ps =>
           bi_reflection.quote_l;
            (let \206\163 := match goal with
                      | |- bi_reflection.eval ?\206\163 _ \226\138\162 _ => \206\163
                      end
             in
             let ns' :=
              lazymatch type of (_ : bi_reflection.QuoteArgs \206\163 Ps _)
              with
              | bi_reflection.QuoteArgs _ _ ?ns' => ns'
              end
             in
             <ssreflect_plugin::ssrtclseq@0> eapply entails_equiv_l ; first 
              apply bi_reflection.split_l with (ns := ns'); compute;
               reflexivity; simpl))).
Time
Tactic Notation "to_back" open_constr(Ps) :=
 (close_uPreds Ps
   ltac:(fun Ps =>
           bi_reflection.quote_l;
            (let \206\163 := match goal with
                      | |- bi_reflection.eval ?\206\163 _ \226\138\162 _ => \206\163
                      end
             in
             let ns' :=
              lazymatch type of (_ : bi_reflection.QuoteArgs \206\163 Ps _)
              with
              | bi_reflection.QuoteArgs _ _ ?ns' => ns'
              end
             in
             <ssreflect_plugin::ssrtclseq@0> eapply entails_equiv_l ; first 
              apply bi_reflection.split_r with (ns := ns'); compute;
               reflexivity; simpl))).
Time
Tactic Notation "sep_split" "right:" open_constr(Ps) :=
 (to_back Ps; apply sep_mono).
Time
Tactic Notation "sep_split" "left:" open_constr(Ps) :=
 (to_front Ps; apply sep_mono).
