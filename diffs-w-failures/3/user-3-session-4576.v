Time From iris.bi Require Export bi.
Time From iris.algebra Require Export cmra.
Time From stdpp Require Export list gmap.
Time From iris.algebra Require Import updates local_updates.
Time From iris.base_logic Require Import base_logic.
Time From iris.bi Require Import tactics.
Time
From iris.proofmode Require Export base environments classes
  modality_instances.
Time Set Default Proof Using "Type".
Time Import bi.
Time Import env_notations.
Time Section bi_tactics.
Time Context {PROP : bi}.
Time Implicit Type \206\147 : env PROP.
Time Implicit Type \206\148 : envs PROP.
Time Implicit Types P Q : PROP.
Time Lemma tac_adequate P : envs_entails (Envs Enil Enil 1) P \226\134\146 P.
Time Proof.
Time rewrite envs_entails_eq !of_envs_eq /=.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite intuitionistically_True_emp
 left_id =>{+}<-).
Time (<ssreflect_plugin::ssrtclintros@0> apply and_intro =>//).
Time (apply pure_intro; repeat constructor).
Time Qed.
Time
Lemma tac_eval \206\148 Q Q' :
  (\226\136\128 (Q'' := Q'), Q'' \226\138\162 Q) \226\134\146 envs_entails \206\148 Q' \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time by intros <-.
Time Qed.
Time
Lemma tac_eval_in \206\148 i p P P' Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 (\226\136\128 (P'' := P'), P \226\138\162 P')
    \226\134\146 match envs_simple_replace i p (Esnoc Enil i P') \206\148 with
      | None => False
      | Some \206\148' => envs_entails \206\148' Q
      end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:Hrep ; last  done).
Time rewrite envs_entails_eq /=.
Time (intros ? HP ?).
Time (rewrite envs_simple_replace_singleton_sound //; simpl).
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context `{Countable K} {A : ofeT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time
Instance gmap_dist : (Dist (gmap K A)) :=
 (\206\187 n m1 m2, \226\136\128 i, m1 !! i \226\137\161{n}\226\137\161 m2 !! i).
Time by rewrite HP wand_elim_r.
Time Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Time Proof.
Time split.
Time -
Time (intros m1 m2; split).
Time +
Time by intros Hm n k; apply equiv_dist.
Time +
Time (intros Hm k; apply equiv_dist; intros n; apply Hm).
Time -
Time (intros n; split).
Time +
Time by intros m k.
Time +
Time by intros m1 m2 ? k.
Time Qed.
Time Class AffineEnv (\206\147 : env PROP) :=
         affine_env : Forall Affine \206\147.
Time +
Time by intros m1 m2 m3 ? ? k; trans m2 !! k.
Time -
Time #[global]Instance affine_env_nil : (AffineEnv Enil).
Time Proof.
Time constructor.
Time Qed.
Time #[global]
Instance affine_env_snoc  \206\147 i P:
 (Affine P \226\134\146 AffineEnv \206\147 \226\134\146 AffineEnv (Esnoc \206\147 i P)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance affine_env_bi  `(BiAffine PROP) \206\147: (AffineEnv \206\147) |0.
Time Proof.
Time (induction \206\147; apply _).
Time by intros n m1 m2 ? k; apply dist_S.
Time Qed.
Time Qed.
Time
Instance affine_env_spatial  \206\148:
 (AffineEnv (env_spatial \206\148) \226\134\146 Affine ([\226\136\151] env_spatial \206\148)).
Time Proof.
Time (intros H).
Time (induction H; simpl; apply _).
Time Qed.
Time Canonical Structure gmapO : ofeT := OfeT (gmap K A) gmap_ofe_mixin.
Time #[program]
Definition gmap_chain (c : chain gmapO) (k : K) : 
  chain (optionO A) := {| chain_car := fun n => c n !! k |}.
Time Next Obligation.
Time by intros c k n i ?; apply (chain_cauchy c).
Time Lemma tac_emp_intro \206\148 : AffineEnv (env_spatial \206\148) \226\134\146 envs_entails \206\148 emp.
Time Proof.
Time (intros).
Time by rewrite envs_entails_eq (affine (of_envs \206\148)).
Time Qed.
Time
Definition gmap_compl `{Cofe A} : Compl gmapO :=
  \206\187 c, map_imap (\206\187 i _, compl (gmap_chain c i)) (c 0).
Time #[global, program]
Instance gmap_cofe  `{Cofe A}: (Cofe gmapO) := {| compl := gmap_compl |}.
Time Next Obligation.
Time (intros ? n c k).
Time rewrite /compl /gmap_compl map_lookup_imap.
Time
(feed inversion \206\187 H, chain_cauchy c 0 n H k; simplify_option_eq; auto
  with lia).
Time Qed.
Time
Lemma tac_assumption \206\148 i p P Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 FromAssumption p P Q
    \226\134\146 (let \206\148' := envs_delete true i p \206\148 in
       if env_spatial_is_nil \206\148' then TCTrue
       else TCOr (Absorbing Q) (AffineEnv (env_spatial \206\148')))
      \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time (intros ? ? H).
Time rewrite envs_entails_eq envs_lookup_sound //.
Time (simpl in *).
Time (destruct (env_spatial_is_nil _) eqn:?).
Time -
Time by rewrite (env_spatial_is_nil_intuitionistically _) // sep_elim_l.
Time by rewrite conv_compl /=; apply reflexive_eq.
Time -
Time rewrite from_assumption.
Time Qed.
Time #[global]
Instance gmap_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete gmapO).
Time Proof.
Time (intros ? m m' ? i).
Time by apply (discrete _).
Time (destruct H; by rewrite sep_elim_l).
Time Qed.
Time #[global]Instance gmapO_leibniz : (LeibnizEquiv A \226\134\146 LeibnizEquiv gmapO).
Time Proof.
Time (intros; change_no_check (LeibnizEquiv (gmap K A)); apply _).
Time Qed.
Time #[global]
Instance lookup_ne  k: (NonExpansive (lookup k : gmap K A \226\134\146 option A)).
Time Proof.
Time by intros m1 m2.
Time Qed.
Time #[global]
Instance lookup_proper  k:
 (Proper ((\226\137\161) ==> (\226\137\161)) (lookup k : gmap K A \226\134\146 option A)) := _.
Time #[global]
Instance alter_ne  f k n:
 (Proper (dist n ==> dist n) f \226\134\146 Proper (dist n ==> dist n) (alter f k)).
Time Proof.
Time (intros ? m m' Hm k').
Time by destruct (decide (k = k')); simplify_map_eq; rewrite (Hm k').
Time Qed.
Time
Lemma tac_rename \206\148 i j p P Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 match envs_simple_replace i p (Esnoc Enil j P) \206\148 with
    | None => False
    | Some \206\148' => envs_entails \206\148' Q
    end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:Hrep ; last  done).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ?).
Time rewrite envs_simple_replace_singleton_sound //.
Time by rewrite wand_elim_r.
Time Qed.
Time
Lemma tac_clear \206\148 i p P Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 (if p then TCTrue else TCOr (Affine P) (Absorbing Q))
    \226\134\146 envs_entails (envs_delete true i p \206\148) Q \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? HQ).
Time rewrite envs_lookup_sound //.
Time rewrite HQ.
Time by destruct p; rewrite /= sep_elim_r.
Time Qed.
Time Qed.
Time Lemma tac_ex_falso \206\148 Q : envs_entails \206\148 False \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time by rewrite envs_entails_eq -(False_elim Q).
Time Qed.
Time
Lemma tac_false_destruct \206\148 i p P Q :
  envs_lookup i \206\148 = Some (p, P) \226\134\146 P = False%I \226\134\146 envs_entails \206\148 Q.
Time #[global]
Instance insert_ne  i: (NonExpansive2 (insert (M:=gmap K A) i)).
Time Proof.
Time
(intros n x y ? m m' ? j; destruct (decide (i = j)); simplify_map_eq;
  [ by constructor | by apply lookup_ne ]).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ?).
Time subst.
Time (rewrite envs_lookup_sound //; simpl).
Time by rewrite intuitionistically_if_elim sep_elim_l False_elim.
Time Qed.
Time
Lemma tac_pure_intro \206\148 Q \207\134 a :
  FromPure a Q \207\134
  \226\134\146 (if a then AffineEnv (env_spatial \206\148) else TCTrue) \226\134\146 \207\134 \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time (intros ? ? ?).
Time rewrite envs_entails_eq -(from_pure a Q).
Time (destruct a; simpl).
Time -
Time
by rewrite (affine (of_envs \206\148)) pure_True // affinely_True_emp affinely_emp.
Time Qed.
Time #[global]
Instance singleton_ne  i: (NonExpansive (singletonM i : A \226\134\146 gmap K A)).
Time Proof.
Time by intros ? ? ? ?; apply insert_ne.
Time Qed.
Time #[global]Instance delete_ne  i: (NonExpansive (delete (M:=gmap K A) i)).
Time Proof.
Time
(intros n m m' ? j; destruct (decide (i = j)); simplify_map_eq;
  [ by constructor | by apply lookup_ne ]).
Time Qed.
Time -
Time by apply pure_intro.
Time Qed.
Time #[global]Instance gmap_empty_discrete : (Discrete (\226\136\133 : gmap K A)).
Time Proof.
Time (intros m Hm i; specialize (Hm i); rewrite lookup_empty in  {} Hm |- *).
Time
Lemma tac_pure \206\148 i p P \207\134 Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 IntoPure P \207\134
    \226\134\146 (if p then TCTrue else TCOr (Affine P) (Absorbing Q))
      \226\134\146 (\207\134 \226\134\146 envs_entails (envs_delete true i p \206\148) Q) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? HPQ HQ).
Time (inversion_clear Hm; constructor).
Time Qed.
Time (rewrite envs_lookup_sound //; simpl).
Time #[global]
Instance gmap_lookup_discrete  m i: (Discrete m \226\134\146 Discrete (m !! i)).
Time Proof.
Time (intros ? [x| ] Hx; [  | by symmetry; apply : {}discrete {} ]).
Time
(assert (m \226\137\161{0}\226\137\161 <[i:=x]> m) by by
  symmetry in Hx; inversion Hx; ofe_subst; rewrite insert_id).
Time (destruct p; simpl).
Time -
Time
rewrite (into_pure P) -persistently_and_intuitionistically_sep_l
 persistently_pure.
Time by rewrite (discrete m (<[i:=x]> m)) // lookup_insert.
Time by apply pure_elim_l.
Time -
Time (destruct HPQ).
Time +
Time
rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_l.
Time Qed.
Time #[global]
Instance gmap_insert_discrete  m i x:
 (Discrete x \226\134\146 Discrete m \226\134\146 Discrete (<[i:=x]> m)).
Time Proof.
Time (intros ? ? m' Hm j; destruct (decide (i = j)); simplify_map_eq).
Time by apply pure_elim_l.
Time +
Time
rewrite (into_pure P) -(persistent_absorbingly_affinely \226\140\156_\226\140\157%I)
 absorbingly_sep_lr.
Time {
Time by apply : {}discrete {}; rewrite -Hm lookup_insert.
Time rewrite -persistent_and_affinely_sep_l.
Time }
Time by apply : {}discrete {}; rewrite -Hm lookup_insert_ne.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>?).
Time by rewrite HQ.
Time Qed.
Time Qed.
Time
Lemma tac_pure_revert \206\148 \207\134 Q : envs_entails \206\148 (\226\140\156\207\134\226\140\157 \226\134\146 Q) \226\134\146 \207\134 \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time rewrite envs_entails_eq.
Time (intros H\206\148 ?).
Time by rewrite H\206\148 pure_True // left_id.
Time #[global]
Instance gmap_singleton_discrete  i x:
 (Discrete x \226\134\146 Discrete ({[i := x]} : gmap K A)) := _.
Time Lemma insert_idN n m i x : m !! i \226\137\161{n}\226\137\161 Some x \226\134\146 <[i:=x]> m \226\137\161{n}\226\137\161 m.
Time Proof.
Time (intros (y', (?, ->))%dist_Some_inv_r').
Time by rewrite insert_id.
Time Qed.
Time End cofe.
Time Arguments gmapO _ {_} {_} _.
Time Section cmra.
Time Context `{Countable K} {A : cmraT}.
Time Implicit Type m : gmap K A.
Time Instance gmap_unit : (Unit (gmap K A)) := (\226\136\133 : gmap K A).
Time Instance gmap_op : (Op (gmap K A)) := (merge op).
Time Instance gmap_pcore : (PCore (gmap K A)) := (\206\187 m, Some (omap pcore m)).
Time Instance gmap_valid : (Valid (gmap K A)) := (\206\187 m, \226\136\128 i, \226\156\147 (m !! i)).
Time
Instance gmap_validN : (ValidN (gmap K A)) := (\206\187 n m, \226\136\128 i, \226\156\147{n} (m !! i)).
Time Lemma lookup_op m1 m2 i : (m1 \226\139\133 m2) !! i = m1 !! i \226\139\133 m2 !! i.
Time Proof.
Time by apply lookup_merge.
Time Qed.
Time Qed.
Time Lemma lookup_core m i : core m !! i = core (m !! i).
Time Proof.
Time by apply lookup_omap.
Time Qed.
Time
Lemma lookup_included (m1 m2 : gmap K A) : m1 \226\137\188 m2 \226\134\148 (\226\136\128 i, m1 !! i \226\137\188 m2 !! i).
Time
Lemma tac_intuitionistic \206\148 i p P P' Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 IntoPersistent p P P'
    \226\134\146 (if p then TCTrue else TCOr (Affine P) (Absorbing Q))
      \226\134\146 match envs_replace i p true (Esnoc Enil i P') \206\148 with
        | None => False
        | Some \206\148' => envs_entails \206\148' Q
        end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_replace _ _ _ _ _) as [\206\148'| ] eqn:Hrep ; last  done).
Time Proof.
Time
(split; [ by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm |  ]).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? HPQ HQ).
Time rewrite envs_replace_singleton_sound //=.
Time revert m2.
Time
(<ssreflect_plugin::ssrtclintros@0>
 induction m1 as [| i x m Hi IH] using map_ind =>m2 Hm).
Time (destruct p; simpl; rewrite /bi_intuitionistically).
Time -
Time by rewrite -(into_persistent true P) /= wand_elim_r.
Time {
Time exists m2.
Time by rewrite left_id.
Time }
Time (destruct (IH (delete i m2)) as [m2' Hm2']).
Time {
Time (intros j).
Time (move : {}(Hm j) {}; destruct (decide (i = j)) as [->| ]).
Time -
Time (intros _).
Time rewrite Hi.
Time apply : {}ucmra_unit_least {}.
Time -
Time rewrite lookup_insert_ne // lookup_delete_ne //.
Time -
Time (destruct HPQ).
Time +
Time
rewrite -(affine_affinely P) (_ : P = <pers>?false P)%I //
 (into_persistent _ P) wand_elim_r //.
Time }
Time (destruct (Hm i) as [my Hi']; simplify_map_eq).
Time
(<ssreflect_plugin::ssrtclintros@0> exists (partial_alter (\206\187 _, my) i m2')
  =>j; destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
Time +
Time rewrite (_ : P = <pers>?false P)%I // (into_persistent _ P).
Time
by rewrite -{+1}absorbingly_intuitionistically_into_persistently
 absorbingly_sep_l wand_elim_r HQ.
Time -
Time move : {}(Hm2' j) {}.
Time
by rewrite !lookup_op lookup_delete_ne // lookup_insert_ne //
 lookup_partial_alter_ne.
Time Qed.
Time
Lemma tac_impl_intro \206\148 i P P' Q R :
  FromImpl R P Q
  \226\134\146 (if env_spatial_is_nil \206\148 then TCTrue else Persistent P)
    \226\134\146 FromAffinely P' P
      \226\134\146 match envs_app false (Esnoc Enil i P') \206\148 with
        | None => False
        | Some \206\148' => envs_entails \206\148' Q
        end \226\134\146 envs_entails \206\148 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) eqn:? ; last 
 done).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromImpl envs_entails_eq =>{+}<-
 ? ? ?).
Time (destruct (env_spatial_is_nil \206\148) eqn:?).
Time -
Time (rewrite (env_spatial_is_nil_intuitionistically \206\148) //; simpl).
Time (apply impl_intro_l).
Time (rewrite envs_app_singleton_sound //; simpl).
Time Qed.
Time Lemma gmap_cmra_mixin : CmraMixin (gmap K A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time (intros n m1 m2 m3 Hm i; by rewrite !lookup_op (Hm i)).
Time rewrite -(from_affinely P' P) -affinely_and_lr.
Time -
Time (intros n m1 m2 Hm i; by rewrite !lookup_core (Hm i)).
Time -
Time (intros n m1 m2 Hm ? i; by rewrite -(Hm i)).
Time
by rewrite persistently_and_intuitionistically_sep_r intuitionistically_elim
 wand_elim_r.
Time -
Time (intros m; split).
Time +
Time by intros ? n i; apply cmra_valid_validN.
Time +
Time
(intros Hm i; <ssreflect_plugin::ssrtclintros@0> apply cmra_valid_validN =>n;
  apply Hm).
Time -
Time (intros n m Hm i; apply cmra_validN_S, Hm).
Time -
Time by intros m1 m2 m3 i; rewrite !lookup_op assoc.
Time -
Time by intros m1 m2 i; rewrite !lookup_op comm.
Time -
Time (apply impl_intro_l).
Time (rewrite envs_app_singleton_sound //; simpl).
Time -
Time (intros m i).
Time by rewrite lookup_op lookup_core cmra_core_l.
Time -
Time (intros m i).
Time by rewrite !lookup_core cmra_core_idemp.
Time
by rewrite -(from_affinely P' P) persistent_and_affinely_sep_l_1 wand_elim_r.
Time -
Time
(intros m1 m2; <ssreflect_plugin::ssrtclintros@0> rewrite !lookup_included
  =>Hm i).
Time rewrite !lookup_core.
Time by apply cmra_core_mono.
Time -
Time (intros n m1 m2 Hm i; apply cmra_validN_op_l with (m2 !! i)).
Time Qed.
Time by rewrite -lookup_op.
Time -
Time (intros n m y1 y2 Hm Heq).
Time
(<ssreflect_plugin::ssrtclseq@0> refine
 ((\206\187 FUN, _) (\206\187 i, cmra_extend n (m !! i) (y1 !! i) (y2 !! i) (Hm i) _)) ;
 last  by rewrite -lookup_op).
Time
Lemma tac_impl_intro_intuitionistic \206\148 i P P' Q R :
  FromImpl R P Q
  \226\134\146 IntoPersistent false P P'
    \226\134\146 match envs_app true (Esnoc Enil i P') \206\148 with
      | None => False
      | Some \206\148' => envs_entails \206\148' Q
      end \226\134\146 envs_entails \206\148 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) eqn:? ; last 
 done).
Time exists (map_imap (\206\187 i _, projT1 (FUN i)) y1).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromImpl envs_entails_eq =>{+}<-
 ? ?).
Time exists (map_imap (\206\187 i _, proj1_sig (projT2 (FUN i))) y2).
Time
(<ssreflect_plugin::ssrtclintros@0> split; [  | split ] =>i; rewrite
  ?lookup_op !map_lookup_imap; <ssreflect_plugin::ssrtclintros@0>
  destruct (FUN i) as (z1i, (z2i, (Hmi, (Hz1i, Hz2i)))) =>/=).
Time rewrite envs_app_singleton_sound //=.
Time (apply impl_intro_l).
Time rewrite (_ : P = <pers>?false P)%I // (into_persistent false P).
Time by rewrite persistently_and_intuitionistically_sep_l wand_elim_r.
Time Qed.
Time
Lemma tac_impl_intro_drop \206\148 P Q R :
  FromImpl R P Q \226\134\146 envs_entails \206\148 Q \226\134\146 envs_entails \206\148 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromImpl envs_entails_eq =>{+}<-
 ?).
Time (apply impl_intro_l).
Time by rewrite and_elim_r.
Time Qed.
Time
Lemma tac_wand_intro \206\148 i P Q R :
  FromWand R P Q
  \226\134\146 match envs_app false (Esnoc Enil i P) \206\148 with
    | None => False
    | Some \206\148' => envs_entails \206\148' Q
    end \226\134\146 envs_entails \206\148 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) as [\206\148'| ] eqn:Hrep
 ; last  done).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromWand envs_entails_eq =>{+}<-
 HQ).
Time (rewrite envs_app_sound //; simpl).
Time by rewrite right_id HQ.
Time +
Time
(destruct (y1 !! i), (y2 !! i); inversion Hz1i; inversion Hz2i;
  <ssreflect_plugin::ssrtclintros@0> subst =>//).
Time Qed.
Time
Lemma tac_wand_intro_intuitionistic \206\148 i P P' Q R :
  FromWand R P Q
  \226\134\146 IntoPersistent false P P'
    \226\134\146 TCOr (Affine P) (Absorbing Q)
      \226\134\146 match envs_app true (Esnoc Enil i P') \206\148 with
        | None => False
        | Some \206\148' => envs_entails \206\148' Q
        end \226\134\146 envs_entails \206\148 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) as [\206\148'| ] eqn:Hrep
 ; last  done).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromWand envs_entails_eq =>{+}<-
 ? HPQ HQ).
Time +
Time revert Hz1i.
Time case : {}(y1 !! i) {} =>[?|] //.
Time rewrite envs_app_singleton_sound //=.
Time +
Time revert Hz2i.
Time case : {}(y2 !! i) {} =>[?|] //.
Time Qed.
Time (apply wand_intro_l).
Time (destruct HPQ).
Time -
Time
rewrite -(affine_affinely P) (_ : P = <pers>?false P)%I //
 (into_persistent _ P) wand_elim_r //.
Time -
Time rewrite (_ : P = <pers>?false P)%I // (into_persistent _ P).
Time
by rewrite -{+1}absorbingly_intuitionistically_into_persistently
 absorbingly_sep_l wand_elim_r HQ.
Time Canonical Structure gmapR := CmraT (gmap K A) gmap_cmra_mixin.
Time #[global]
Instance gmap_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete gmapR).
Time Proof.
Time (split; [ apply _ |  ]).
Time (intros m ? i).
Time by apply : {}cmra_discrete_valid {}.
Time Qed.
Time Lemma gmap_ucmra_mixin : UcmraMixin (gmap K A).
Time Proof.
Time split.
Time -
Time by intros i; rewrite lookup_empty.
Time -
Time by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>i).
Time by rewrite lookup_omap lookup_empty.
Time Qed.
Time Canonical Structure gmapUR := UcmraT (gmap K A) gmap_ucmra_mixin.
Time
Lemma gmap_equivI {M} m1 m2 : m1 \226\137\161 m2 \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, m1 !! i \226\137\161 m2 !! i).
Time Proof.
Time by uPred.unseal.
Time Qed.
Time Qed.
Time
Lemma tac_wand_intro_drop \206\148 P Q R :
  FromWand R P Q
  \226\134\146 TCOr (Affine P) (Absorbing Q) \226\134\146 envs_entails \206\148 Q \226\134\146 envs_entails \206\148 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq /FromWand =>{+}<-
 HPQ {+}->).
Time Lemma gmap_validI {M} m : \226\156\147 m \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, \226\156\147 (m !! i)).
Time Proof.
Time by uPred.unseal.
Time (apply wand_intro_l).
Time by rewrite sep_elim_r.
Time Qed.
Time End cmra.
Time Qed.
Time
Lemma tac_specialize remove_intuitionistic \206\148 i p j 
  q P1 P2 R Q :
  envs_lookup i \206\148 = Some (p, P1)
  \226\134\146 let \206\148' := envs_delete remove_intuitionistic i p \206\148 in
    envs_lookup j \206\148' = Some (q, R)
    \226\134\146 IntoWand q p R P1 P2
      \226\134\146 match envs_replace j q (p && q) (Esnoc Enil j P2) \206\148' with
        | Some \206\148'' => envs_entails \206\148'' Q
        | None => False
        end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time rewrite envs_entails_eq /IntoWand.
Time (intros ? ? HR ?).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_replace _ _ _ _ _) as [\206\148''| ] eqn:? ; last  done).
Time rewrite (envs_lookup_sound' _ remove_intuitionistic) //.
Time rewrite envs_replace_singleton_sound //.
Time Arguments gmapR _ {_} {_} _.
Time Arguments gmapUR _ {_} {_} _.
Time Section properties.
Time Context `{Countable K} {A : cmraT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time Implicit Types x y : A.
Time #[global]
Instance lookup_op_homomorphism :
 (MonoidHomomorphism op op (\226\137\161) (lookup i : gmap K A \226\134\146 option A)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (destruct p; simpl in *).
Time -
Time rewrite -{+1}intuitionistically_idemp -{+1}intuitionistically_if_idemp.
Time (intros m1 m2; by rewrite lookup_op).
Time done.
Time Qed.
Time Lemma lookup_opM m1 mm2 i : (m1 \226\139\133? mm2) !! i = m1 !! i \226\139\133 (mm2 \226\137\171= (!!i)).
Time Proof.
Time (destruct mm2; by rewrite /= ?lookup_op ?right_id_L).
Time rewrite {+1}(intuitionistically_intuitionistically_if q).
Time Qed.
Time
Lemma lookup_validN_Some n m i x : \226\156\147{n} m \226\134\146 m !! i \226\137\161{n}\226\137\161 Some x \226\134\146 \226\156\147{n} x.
Time by rewrite HR assoc intuitionistically_if_sep_2 !wand_elim_r.
Time Proof.
Time by move  {}=>/(_ i) Hm Hi; move : {}Hm {}; rewrite Hi.
Time Qed.
Time Lemma lookup_valid_Some m i x : \226\156\147 m \226\134\146 m !! i \226\137\161 Some x \226\134\146 \226\156\147 x.
Time Proof.
Time move  {}=>Hm Hi.
Time move : {}(Hm i) {}.
Time by rewrite Hi.
Time Qed.
Time Lemma insert_validN n m i x : \226\156\147{n} x \226\134\146 \226\156\147{n} m \226\134\146 \226\156\147{n} <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time Qed.
Time Lemma insert_valid m i x : \226\156\147 x \226\134\146 \226\156\147 m \226\134\146 \226\156\147 <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time -
Time by rewrite HR assoc !wand_elim_r.
Time Qed.
Time Lemma singleton_validN n i x : \226\156\147{n} ({[i := x]} : gmap K A) \226\134\148 \226\156\147{n} x.
Time Proof.
Time split.
Time -
Time (move  {}=>/(_ i); by simplify_map_eq).
Time -
Time (intros).
Time (apply insert_validN).
Time done.
Time apply : {}ucmra_unit_validN {}.
Time Qed.
Time Lemma singleton_valid i x : \226\156\147 ({[i := x]} : gmap K A) \226\134\148 \226\156\147 x.
Time Proof.
Time rewrite !cmra_valid_validN.
Time by setoid_rewrite singleton_validN.
Time Qed.
Time Lemma delete_validN n m i : \226\156\147{n} m \226\134\146 \226\156\147{n} delete i m.
Time Proof.
Time (intros Hm j; destruct (decide (i = j)); by simplify_map_eq).
Time Qed.
Time
Lemma tac_specialize_assert \206\148 j q neg js R P1 P2 P1' 
  Q :
  envs_lookup j \206\148 = Some (q, R)
  \226\134\146 IntoWand q false R P1 P2
    \226\134\146 AddModal P1' P1 Q
      \226\134\146 match
          ' '(\206\1481, \206\1482)
          \226\134\144 envs_split match neg with
                       | true => Right
                       | _ => Left
                       end js (envs_delete true j q \206\148);
          \206\1482' \226\134\144 envs_app false (Esnoc Enil j P2) \206\1482; Some (\206\1481, \206\1482')
        with
        | Some (\206\1481, \206\1482') => envs_entails \206\1481 P1' \226\136\167 envs_entails \206\1482' Q
        | None => False
        end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time rewrite envs_entails_eq.
Time Qed.
Time (intros ? ? ? HQ).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (_ \226\137\171= _) as [[\206\1481 \206\1482']| ] eqn:? ;
 last  done).
Time Lemma delete_valid m i : \226\156\147 m \226\134\146 \226\156\147 delete i m.
Time Proof.
Time (intros Hm j; destruct (decide (i = j)); by simplify_map_eq).
Time (destruct HQ as [HP1 HQ]).
Time
(destruct (envs_split _ _ _) as [[? \206\1482]| ] eqn:?; simplify_eq /=;
  destruct (envs_app _ _ _) eqn:?; simplify_eq /=).
Time Qed.
Time
Lemma insert_singleton_op m i x : m !! i = None \226\134\146 <[i:=x]> m = {[i := x]} \226\139\133 m.
Time Proof.
Time
(intros Hi; <ssreflect_plugin::ssrtclintros@0> apply map_eq =>j;
  destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
Time rewrite envs_lookup_sound // envs_split_sound //.
Time -
Time
by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
Time Qed.
Time
Lemma core_singleton (i : K) (x : A) cx :
  pcore x = Some cx \226\134\146 core ({[i := x]} : gmap K A) = {[i := cx]}.
Time Proof.
Time (apply omap_singleton).
Time Qed.
Time
Lemma core_singleton' (i : K) (x : A) cx :
  pcore x \226\137\161 Some cx \226\134\146 core ({[i := x]} : gmap K A) \226\137\161 {[i := cx]}.
Time Proof.
Time (intros (cx', (?, ->))%equiv_Some_inv_r').
Time (rewrite (envs_app_singleton_sound \206\1482) //; simpl).
Time rewrite HP1 (into_wand q false) /= -(add_modal P1' P1 Q).
Time cancel [P1'].
Time (apply wand_intro_l).
Time by rewrite assoc !wand_elim_r.
Time by rewrite (core_singleton _ _ cx').
Time Qed.
Time
Lemma op_singleton (i : K) (x y : A) :
  {[i := x]} \226\139\133 {[i := y]} = ({[i := x \226\139\133 y]} : gmap K A).
Time Proof.
Time by apply (merge_singleton _ _ _ x y).
Time Qed.
Time #[global]
Instance is_op_singleton  i a a1 a2:
 (IsOp a a1 a2 \226\134\146 IsOp' ({[i := a]} : gmap K A) {[i := a1]} {[i := a2]}).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp =>{+}->).
Time Qed.
Time
Lemma tac_unlock_emp \206\148 Q : envs_entails \206\148 Q \226\134\146 envs_entails \206\148 (emp \226\136\151 locked Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>{+}->).
Time by rewrite -lock left_id.
Time Qed.
Time
Lemma tac_unlock_True \206\148 Q :
  envs_entails \206\148 Q \226\134\146 envs_entails \206\148 (True \226\136\151 locked Q).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>{+}->).
Time by rewrite -lock -True_sep_2.
Time Qed.
Time Lemma tac_unlock \206\148 Q : envs_entails \206\148 Q \226\134\146 envs_entails \206\148 (locked Q).
Time Proof.
Time by unlock.
Time Qed.
Time
Lemma tac_specialize_frame \206\148 j q R P1 P2 P1' Q Q' :
  envs_lookup j \206\148 = Some (q, R)
  \226\134\146 IntoWand q false R P1 P2
    \226\134\146 AddModal P1' P1 Q
      \226\134\146 envs_entails (envs_delete true j q \206\148) (P1' \226\136\151 locked Q')
        \226\134\146 Q' = (P2 -\226\136\151 Q)%I \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time rewrite envs_entails_eq.
Time (intros ? ? ? HPQ ->).
Time rewrite envs_lookup_sound //.
Time rewrite HPQ -lock.
Time rewrite (into_wand q false) -{+2}(add_modal P1' P1 Q).
Time by rewrite -op_singleton.
Time Qed.
Time cancel [P1'].
Time #[global]Instance gmap_core_id  m: ((\226\136\128 x : A, CoreId x) \226\134\146 CoreId m).
Time Proof.
Time (intros; <ssreflect_plugin::ssrtclintros@0> apply core_id_total =>i).
Time rewrite lookup_core.
Time (apply (core_id_core _)).
Time Qed.
Time (apply wand_intro_l).
Time by rewrite assoc !wand_elim_r.
Time #[global]
Instance gmap_singleton_core_id  i (x : A): (CoreId x \226\134\146 CoreId {[i := x]}).
Time Proof.
Time (intros).
Time by apply core_id_total, core_singleton'.
Time Qed.
Time
Lemma singleton_includedN n m i x :
  {[i := x]} \226\137\188{n} m \226\134\148 (\226\136\131 y, m !! i \226\137\161{n}\226\137\161 Some y \226\136\167 Some x \226\137\188{n} Some y).
Time Proof.
Time split.
Time -
Time
(move  {}=>[m' /(_ i)]; <ssreflect_plugin::ssrtclintros@0> rewrite lookup_op
  lookup_singleton =>Hi).
Time exists (x \226\139\133? m' !! i).
Time rewrite -Some_op_opM.
Time split.
Time done.
Time (apply cmra_includedN_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time exists (partial_alter (\206\187 _, mz) i m).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time Qed.
Time
Lemma tac_specialize_assert_pure \206\148 j q a R P1 P2 \207\134 
  Q :
  envs_lookup j \206\148 = Some (q, R)
  \226\134\146 IntoWand q true R P1 P2
    \226\134\146 FromPure a P1 \207\134
      \226\134\146 \207\134
        \226\134\146 match envs_simple_replace j q (Esnoc Enil j P2) \206\148 with
          | None => False
          | Some \206\148' => envs_entails \206\148' Q
          end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:? ; last  done).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? ? ? ?).
Time rewrite envs_simple_replace_singleton_sound //=.
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time rewrite -intuitionistically_if_idemp (into_wand q true) /=.
Time Qed.
Time rewrite -(from_pure a P1) pure_True //.
Time
Lemma singleton_included m i x :
  {[i := x]} \226\137\188 m \226\134\148 (\226\136\131 y, m !! i \226\137\161 Some y \226\136\167 Some x \226\137\188 Some y).
Time Proof.
Time split.
Time -
Time (move  {}=>[m' /(_ i)]; rewrite lookup_op lookup_singleton).
Time exists (x \226\139\133? m' !! i).
Time rewrite -Some_op_opM.
Time split.
Time done.
Time (apply cmra_included_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time exists (partial_alter (\206\187 _, mz) i m).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time rewrite -affinely_affinely_if affinely_True_emp affinely_emp.
Time Qed.
Time
Lemma singleton_included_exclusive m i x :
  Exclusive x \226\134\146 \226\156\147 m \226\134\146 {[i := x]} \226\137\188 m \226\134\148 m !! i \226\137\161 Some x.
Time Proof.
Time (intros ? Hm).
Time rewrite singleton_included.
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  by eauto).
Time
(intros (y, (?, ->%(Some_included_exclusive _))); eauto
  using lookup_valid_Some).
Time by rewrite intuitionistically_emp left_id wand_elim_r.
Time Qed.
Time #[global]
Instance singleton_cancelable  i x:
 (Cancelable (Some x) \226\134\146 Cancelable {[i := x]}).
Time Proof.
Time (intros ? n m1 m2 Hv EQ j).
Time move : {}(Hv j) {}(EQ j) {}.
Time rewrite !lookup_op.
Time (destruct (decide (i = j)) as [->| ]).
Time -
Time rewrite lookup_singleton.
Time by apply cancelableN.
Time -
Time by rewrite lookup_singleton_ne // !(left_id None _).
Time Qed.
Time
Lemma tac_specialize_assert_intuitionistic \206\148 j q P1 
  P1' P2 R Q :
  envs_lookup j \206\148 = Some (q, R)
  \226\134\146 IntoWand q true R P1 P2
    \226\134\146 Persistent P1
      \226\134\146 IntoAbsorbingly P1' P1
        \226\134\146 envs_entails (envs_delete true j q \206\148) P1'
          \226\134\146 match envs_simple_replace j q (Esnoc Enil j P2) \206\148 with
            | Some \206\148'' => envs_entails \206\148'' Q
            | None => False
            end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? ? ? HP1 HQ).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148''| ] eqn:? ; last  done).
Time rewrite -HQ envs_lookup_sound //.
Time rewrite -(idemp bi_and (of_envs (envs_delete _ _ _ _))).
Time Qed.
Time #[global]
Instance gmap_cancelable  (m : gmap K A):
 ((\226\136\128 x : A, IdFree x) \226\134\146 (\226\136\128 x : A, Cancelable x) \226\134\146 Cancelable m).
Time Proof.
Time (intros ? ? n m1 m2 ? ? i).
Time (apply (cancelableN (m !! i)); by rewrite -!lookup_op).
Time (rewrite {+2}envs_simple_replace_singleton_sound' //; simpl).
Time Qed.
Time
Lemma insert_op m1 m2 i x y :
  <[i:=x \226\139\133 y]> (m1 \226\139\133 m2) = <[i:=x]> m1 \226\139\133 <[i:=y]> m2.
Time Proof.
Time by rewrite (insert_merge (\226\139\133) m1 m2 i (x \226\139\133 y) x y).
Time Qed.
Time
Lemma insert_updateP (P : A \226\134\146 Prop) (Q : gmap K A \226\134\146 Prop) 
  m i x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q (<[i:=y]> m)) \226\134\146 <[i:=x]> m ~~>: Q.
Time Proof.
Time
(intros Hx%option_updateP' HP; <ssreflect_plugin::ssrtclintros@0>
  apply cmra_total_updateP =>n mf Hm).
Time (destruct (Hx n (Some (mf !! i))) as ([y| ], (?, ?)); try done).
Time {
Time by generalize (Hm i); rewrite lookup_op; simplify_map_eq.
Time
rewrite {+1}HP1 (into_absorbingly P1' P1) (persistent_persistently_2 P1).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (<[i:=y]> m); split ; first  by auto).
Time
(intros j; move : {}(Hm j) {} =>{Hm}; <ssreflect_plugin::ssrtclintros@0>
  rewrite !lookup_op =>Hm).
Time (destruct (decide (i = j)); simplify_map_eq /=; auto).
Time
rewrite absorbingly_elim_persistently
 persistently_and_intuitionistically_sep_l assoc.
Time Qed.
Time
Lemma insert_updateP' (P : A \226\134\146 Prop) m i x :
  x ~~>: P \226\134\146 <[i:=x]> m ~~>: (\206\187 m', \226\136\131 y, m' = <[i:=y]> m \226\136\167 P y).
Time Proof.
Time eauto using insert_updateP.
Time Qed.
Time Lemma insert_update m i x y : x ~~> y \226\134\146 <[i:=x]> m ~~> <[i:=y]> m.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using insert_updateP with subst).
Time rewrite -intuitionistically_if_idemp -intuitionistically_idemp.
Time Qed.
Time
Lemma singleton_updateP (P : A \226\134\146 Prop) (Q : gmap K A \226\134\146 Prop) 
  i x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q {[i := y]}) \226\134\146 {[i := x]} ~~>: Q.
Time Proof.
Time (apply insert_updateP).
Time Qed.
Time
Lemma singleton_updateP' (P : A \226\134\146 Prop) i x :
  x ~~>: P \226\134\146 {[i := x]} ~~>: (\206\187 m, \226\136\131 y, m = {[i := y]} \226\136\167 P y).
Time Proof.
Time (apply insert_updateP').
Time Qed.
Time
Lemma singleton_update i (x y : A) : x ~~> y \226\134\146 {[i := x]} ~~> {[i := y]}.
Time Proof.
Time (apply insert_update).
Time Qed.
Time Lemma delete_update m i : m ~~> delete i m.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_total_update =>n mf Hm j;
  destruct (decide (i = j)); subst).
Time -
Time move : {}(Hm j) {}.
Time rewrite !lookup_op lookup_delete left_id.
Time (apply cmra_validN_op_r).
Time -
Time move : {}(Hm j) {}.
Time by rewrite !lookup_op lookup_delete_ne.
Time rewrite (intuitionistically_intuitionistically_if q).
Time Qed.
Time Lemma dom_op m1 m2 : dom (gset K) (m1 \226\139\133 m2) = dom _ m1 \226\136\170 dom _ m2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply elem_of_equiv_L =>i; rewrite
  elem_of_union !elem_of_dom).
Time
by rewrite intuitionistically_if_sep_2 (into_wand q true) wand_elim_l
 wand_elim_r.
Time (unfold is_Some; setoid_rewrite lookup_op).
Time Qed.
Time
Lemma tac_specialize_intuitionistic_helper \206\148 j q P 
  R R' Q :
  envs_lookup j \206\148 = Some (q, P)
  \226\134\146 (if q then TCTrue else BiAffine PROP)
    \226\134\146 envs_entails \206\148 (<absorb> R)
      \226\134\146 IntoPersistent false R R'
        \226\134\146 match envs_replace j q true (Esnoc Enil j R') \206\148 with
          | Some \206\148'' => envs_entails \206\148'' Q
          | None => False
          end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? HR ? ?).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_replace _ _ _ _ _) as [\206\148'| ] eqn:? ; last  done).
Time rewrite -(idemp bi_and (of_envs \206\148)) {+1}HR.
Time (destruct (m1 !! i), (m2 !! i); naive_solver).
Time (rewrite envs_replace_singleton_sound //; destruct q; simpl).
Time -
Time
by rewrite (_ : R = <pers>?false R)%I // (into_persistent _ R)
 absorbingly_elim_persistently sep_elim_r
 persistently_and_intuitionistically_sep_l wand_elim_r.
Time Qed.
Time Lemma dom_included m1 m2 : m1 \226\137\188 m2 \226\134\146 dom (gset K) m1 \226\138\134 dom _ m2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_included =>? i; rewrite
  !elem_of_dom).
Time by apply is_Some_included.
Time Qed.
Time Section freshness.
Time #[local]Set Default Proof Using "Type*".
Time Context `{!Infinite K}.
Time
Lemma alloc_updateP_strong (Q : gmap K A \226\134\146 Prop) (I : K \226\134\146 Prop) 
  m x :
  pred_infinite I
  \226\134\146 \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 I i \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time move  {}=>/(pred_infinite_set I (C:=gset K)) HP ? HQ.
Time (apply cmra_total_updateP).
Time (intros n mf Hm).
Time (destruct (HP (dom (gset K) (m \226\139\133 mf))) as [i [Hi1 Hi2]]).
Time (assert (m !! i = None)).
Time {
Time (eapply (not_elem_of_dom (D:=gset K))).
Time revert Hi2.
Time rewrite dom_op not_elem_of_union.
Time -
Time
by rewrite (absorbing_absorbingly R) (_ : R = <pers>?false R)%I //
 (into_persistent _ R) sep_elim_r persistently_and_intuitionistically_sep_l
 wand_elim_r.
Time naive_solver.
Time }
Time (exists (<[i:=x]> m); split).
Time -
Time by apply HQ.
Time -
Time rewrite insert_singleton_op //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -assoc -insert_singleton_op ; last 
 by eapply (not_elem_of_dom (D:=gset K))).
Time by apply insert_validN; [ apply cmra_valid_validN |  ].
Time Qed.
Time Qed.
Time
Lemma alloc_updateP (Q : gmap K A \226\134\146 Prop) m x :
  \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time
Lemma tac_specialize_intuitionistic_helper_done \206\148 
  i q P : envs_lookup i \206\148 = Some (q, P) \226\134\146 envs_entails \206\148 (<absorb> P).
Time Proof.
Time move  {}=>? ?.
Time
(eapply alloc_updateP_strong with (I := \206\187 _, True); eauto
  using pred_infinite_True).
Time Qed.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> <ssreflect_plugin::ssrtclintros@0>
 rewrite envs_entails_eq /bi_absorbingly =>/envs_lookup_sound =>{+}->).
Time
Lemma alloc_updateP_strong' m x (I : K \226\134\146 Prop) :
  pred_infinite I
  \226\134\146 \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, I i \226\136\167 m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP_strong.
Time Qed.
Time rewrite intuitionistically_if_elim comm.
Time
Lemma alloc_updateP' m x :
  \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP.
Time Qed.
Time
Lemma alloc_updateP_cofinite (Q : gmap K A \226\134\146 Prop) 
  (J : gset K) m x :
  \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 i \226\136\137 J \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time (eapply alloc_updateP_strong).
Time (apply (pred_infinite_set (C:=gset K))).
Time (intros E).
Time exists (fresh (J \226\136\170 E)).
Time (apply not_elem_of_union, is_fresh).
Time Qed.
Time
Lemma alloc_updateP_cofinite' m x (J : gset K) :
  \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, (i \226\136\137 J) \226\136\167 m' = <[i:=x]> m \226\136\167 m !! i = None).
Time (f_equiv; auto using pure_intro).
Time Proof.
Time eauto using alloc_updateP_cofinite.
Time Qed.
Time
Lemma tac_revert \206\148 i Q :
  match envs_lookup_delete true i \206\148 with
  | Some (p, P, \206\148') => envs_entails \206\148' ((if p then \226\150\161 P else P)%I -\226\136\151 Q)
  | None => False
  end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>HQ).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_lookup_delete _ _ _) as [[[p P] \206\148']| ] eqn:? ; last  done).
Time Qed.
Time End freshness.
Time
Lemma alloc_unit_singleton_updateP (P : A \226\134\146 Prop) 
  (Q : gmap K A \226\134\146 Prop) u i :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q {[i := y]}) \226\134\146 \226\136\133 ~~>: Q.
Time Proof.
Time (intros ? ? Hx HQ).
Time (<ssreflect_plugin::ssrtclintros@0> apply cmra_total_updateP =>n gf Hg).
Time (destruct (Hx n (gf !! i)) as (y, (?, Hy))).
Time {
Time move : {}(Hg i) {}.
Time rewrite !left_id.
Time rewrite envs_lookup_delete_sound //=.
Time rewrite HQ.
Time (destruct p; simpl; auto using wand_elim_r).
Time (case : {}(gf !! i) {} =>[x|]; rewrite /= ?left_id //).
Time Qed.
Time
Class IntoIH (\207\134 : Prop) (\206\148 : envs PROP) (Q : PROP) :=
    into_ih : \207\134 \226\134\146 of_envs \206\148 \226\138\162 Q.
Time #[global]Instance into_ih_entails  \206\148 Q: (IntoIH (envs_entails \206\148 Q) \206\148 Q).
Time Proof.
Time by rewrite envs_entails_eq /IntoIH.
Time Qed.
Time #[global]
Instance into_ih_forall  {A} (\207\134 : A \226\134\146 Prop) \206\148 \206\166:
 ((\226\136\128 x, IntoIH (\207\134 x) \206\148 (\206\166 x)) \226\134\146 IntoIH (\226\136\128 x, \207\134 x) \206\148 (\226\136\128 x, \206\166 x)%I) |2.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoIH =>H\206\148 ?).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (H\206\148 x).
Time Qed.
Time #[global]
Instance into_ih_impl  (\207\134 \207\136 : Prop) \206\148 Q:
 (IntoIH \207\134 \206\148 Q \226\134\146 IntoIH (\207\136 \226\134\146 \207\134) \206\148 (\226\140\156\207\136\226\140\157 \226\134\146 Q)%I) |1.
Time (intros; by apply cmra_valid_validN).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists {[i := y]}; split ; first  by auto).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IntoIH =>H\206\148 ?).
Time (apply impl_intro_l, pure_elim_l).
Time auto.
Time Qed.
Time
Lemma tac_revert_ih \206\148 P Q {\207\134 : Prop} (H\207\134 : \207\134) :
  IntoIH \207\134 \206\148 P
  \226\134\146 env_spatial_is_nil \206\148 = true
    \226\134\146 envs_entails \206\148 (<pers> P \226\134\146 Q) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time rewrite /IntoIH envs_entails_eq.
Time (intros HP ? HPQ).
Time rewrite (env_spatial_is_nil_intuitionistically \206\148) //.
Time (intros i'; destruct (decide (i' = i)) as [->| ]).
Time -
Time rewrite lookup_op lookup_singleton.
Time (move : {}Hy {}; case : {}(gf !! i) {} =>[x|]; rewrite /= ?right_id //).
Time rewrite -(idemp bi_and (\226\150\161 of_envs \206\148)%I) {+1}HP // HPQ.
Time -
Time move : {}(Hg i') {}.
Time by rewrite !lookup_op lookup_singleton_ne // !left_id.
Time Qed.
Time
Lemma alloc_unit_singleton_updateP' (P : A \226\134\146 Prop) 
  u i :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~>: P \226\134\146 \226\136\133 ~~>: (\206\187 m, \226\136\131 y, m = {[i := y]} \226\136\167 P y).
Time Proof.
Time eauto using alloc_unit_singleton_updateP.
Time Qed.
Time
Lemma alloc_unit_singleton_update (u : A) i (y : A) :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~> y \226\134\146 (\226\136\133 : gmap K A) ~~> {[i := y]}.
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto using alloc_unit_singleton_updateP
  with subst).
Time
rewrite {+1}intuitionistically_into_persistently_1 intuitionistically_elim
 impl_elim_r //.
Time Qed.
Time
Lemma tac_assert \206\148 j P Q :
  match envs_app true (Esnoc Enil j (P -\226\136\151 P)%I) \206\148 with
  | None => False
  | Some \206\148' => envs_entails \206\148' Q
  end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) as [\206\148'| ] eqn:? ;
 last  done).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>?).
Time (rewrite (envs_app_singleton_sound \206\148) //; simpl).
Time by rewrite -(entails_wand P) // intuitionistically_emp emp_wand.
Time Qed.
Time
Lemma alloc_local_update m1 m2 i x :
  m1 !! i = None \226\134\146 \226\156\147 x \226\134\146 (m1, m2) ~l~> (<[i:=x]> m1, <[i:=x]> m2).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite cmra_valid_validN =>Hi ?).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time Qed.
Time
Lemma tac_pose_proof \206\148 j P Q :
  P
  \226\134\146 match envs_app true (Esnoc Enil j P) \206\148 with
    | None => False
    | Some \206\148' => envs_entails \206\148' Q
    end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) as [\206\148'| ] eqn:? ;
 last  done).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>HP ?).
Time rewrite envs_app_singleton_sound //=.
Time (split; auto using insert_validN).
Time by rewrite -HP /= intuitionistically_emp emp_wand.
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time -
Time
(move : {}(Hm j) {}; <ssreflect_plugin::ssrtclintros@0> rewrite Hi
  symmetry_iff dist_None lookup_op op_None =>- [_ Hj]).
Time Qed.
Time
Lemma tac_pose_proof_hyp \206\148 i j Q :
  match envs_lookup_delete false i \206\148 with
  | None => False
  | Some (p, P, \206\148') =>
      match envs_app p (Esnoc Enil j P) \206\148' with
      | None => False
      | Some \206\148'' => envs_entails \206\148'' Q
      end
  end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_lookup_delete _ _ _) as [((p, P), \206\148')| ] eqn:Hlookup ; last 
 done).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) as [\206\148''| ] eqn:? ;
 last  done).
Time rewrite envs_entails_eq.
Time rewrite envs_lookup_delete_Some in  {} Hlookup *.
Time by rewrite lookup_op !lookup_insert Hj.
Time (intros [? ->] <-).
Time rewrite envs_lookup_sound' // envs_app_singleton_sound //=.
Time -
Time rewrite Hm lookup_insert_ne // !lookup_op lookup_insert_ne //.
Time by rewrite wand_elim_r.
Time Qed.
Time Qed.
Time
Lemma tac_apply \206\148 i p R P1 P2 :
  envs_lookup i \206\148 = Some (p, R)
  \226\134\146 IntoWand p false R P1 P2
    \226\134\146 envs_entails (envs_delete true i p \206\148) P1 \226\134\146 envs_entails \206\148 P2.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? HP1).
Time rewrite envs_lookup_sound //.
Time by rewrite (into_wand p false) /= HP1 wand_elim_l.
Time
Lemma alloc_singleton_local_update m i x :
  m !! i = None \226\134\146 \226\156\147 x \226\134\146 (m, \226\136\133) ~l~> (<[i:=x]> m, {[i := x]}).
Time Proof.
Time (apply alloc_local_update).
Time Qed.
Time
Lemma insert_local_update m1 m2 i x y x' y' :
  m1 !! i = Some x
  \226\134\146 m2 !! i = Some y
    \226\134\146 (x, y) ~l~> (x', y') \226\134\146 (m1, m2) ~l~> (<[i:=x']> m1, <[i:=y']> m2).
Time Proof.
Time
(intros Hi1 Hi2 Hup; <ssreflect_plugin::ssrtclintros@0>
  apply local_update_unital =>n mf Hmv Hm; simpl in *).
Time Qed.
Time
Lemma tac_and_split \206\148 P Q1 Q2 :
  FromAnd P Q1 Q2 \226\134\146 envs_entails \206\148 Q1 \226\134\146 envs_entails \206\148 Q2 \226\134\146 envs_entails \206\148 P.
Time Proof.
Time rewrite envs_entails_eq.
Time (intros).
Time rewrite -(from_and P).
Time by apply and_intro.
Time Qed.
Time
Lemma tac_sep_split \206\148 d js P Q1 Q2 :
  FromSep P Q1 Q2
  \226\134\146 match envs_split d js \206\148 with
    | None => False
    | Some (\206\1481, \206\1482) => envs_entails \206\1481 Q1 \226\136\167 envs_entails \206\1482 Q2
    end \226\134\146 envs_entails \206\148 P.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_split _ _ _) as [(\206\1481, \206\1482)| ] eqn:? ; last  done).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? [HQ1 HQ2]).
Time rewrite envs_split_sound //.
Time (destruct (Hup n (mf !! i)) as [? Hx']; simpl in *).
Time {
Time move : {}(Hmv i) {}.
Time by rewrite Hi1.
Time }
Time {
Time move : {}(Hm i) {}.
Time by rewrite lookup_op Hi1 Hi2 Some_op_opM (inj_iff Some).
Time by rewrite HQ1 HQ2.
Time }
Time (split; auto using insert_validN).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite Hm Hx' =>j;
  destruct (decide (i = j)) as [->| ]).
Time Qed.
Time
Class FromSeps {PROP : bi} (P : PROP) (Qs : list PROP) :=
    from_seps : [\226\136\151] Qs \226\138\162 P.
Time Arguments FromSeps {_} _%I _%I.
Time Arguments from_seps {_} _%I _%I {_}.
Time #[global]Instance from_seps_nil : (@FromSeps PROP emp []).
Time Proof.
Time by rewrite /FromSeps.
Time Qed.
Time #[global]Instance from_seps_singleton  P: (FromSeps P [P]) |1.
Time Proof.
Time by rewrite /FromSeps /= right_id.
Time Qed.
Time #[global]
Instance from_seps_cons  P P' Q Qs:
 (FromSeps P' Qs \226\134\146 FromSep P Q P' \226\134\146 FromSeps P (Q :: Qs)) |2.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /FromSeps /FromSep /= =>{+}->.
Time -
Time by rewrite lookup_insert lookup_op lookup_insert Some_op_opM.
Time Qed.
Time
Lemma tac_combine \206\1481 \206\1482 \206\1483 js p Ps j P Q :
  envs_lookup_delete_list false js \206\1481 = Some (p, Ps, \206\1482)
  \226\134\146 FromSeps P Ps
    \226\134\146 envs_app p (Esnoc Enil j P) \206\1482 = Some \206\1483
      \226\134\146 envs_entails \206\1483 Q \226\134\146 envs_entails \206\1481 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? ? {+}<-).
Time -
Time by rewrite lookup_insert_ne // !lookup_op lookup_insert_ne.
Time rewrite envs_lookup_delete_list_sound //.
Time rewrite from_seps.
Time Qed.
Time rewrite envs_app_singleton_sound //=.
Time
Lemma singleton_local_update m i x y x' y' :
  m !! i = Some x
  \226\134\146 (x, y) ~l~> (x', y') \226\134\146 (m, {[i := y]}) ~l~> (<[i:=x']> m, {[i := y']}).
Time by rewrite wand_elim_r.
Time Proof.
Time (intros).
Time rewrite /singletonM /map_singleton -(insert_insert \226\136\133 i y' y).
Time by eapply insert_local_update; [  | eapply lookup_insert |  ].
Time Qed.
Time
Lemma delete_local_update m1 m2 i x `{!Exclusive x} :
  m2 !! i = Some x \226\134\146 (m1, m2) ~l~> (delete i m1, delete i m2).
Time Proof.
Time (intros Hi).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time Qed.
Time
Lemma tac_and_destruct \206\148 i p j1 j2 P P1 P2 Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 (if p then IntoAnd true P P1 P2 else IntoSep P P1 P2)
    \226\134\146 match envs_simple_replace i p (Esnoc (Esnoc Enil j1 P1) j2 P2) \206\148 with
      | None => False
      | Some \206\148' => envs_entails \206\148' Q
      end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:Hrep ; last  done).
Time rewrite envs_entails_eq.
Time (intros).
Time rewrite envs_simple_replace_sound //=.
Time (destruct p).
Time -
Time by rewrite (into_and _ P) /= right_id -(comm _ P1) wand_elim_r.
Time (split; auto using delete_validN).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite Hm =>j;
  destruct (decide (i = j)) as [<-| ]).
Time -
Time -
Time rewrite lookup_op !lookup_delete left_id symmetry_iff dist_None.
Time (<ssreflect_plugin::ssrtclintros@0> apply eq_None_not_Some =>- [y Hi']).
Time move : {}(Hmv i) {}.
Time rewrite Hm lookup_op Hi Hi' -Some_op.
Time by apply exclusiveN_l.
Time -
Time by rewrite lookup_op !lookup_delete_ne // lookup_op.
Time Qed.
Time by rewrite /= (into_sep P) right_id -(comm _ P1) wand_elim_r.
Time
Lemma delete_singleton_local_update m i x `{!Exclusive x} :
  (m, {[i := x]}) ~l~> (delete i m, \226\136\133).
Time Proof.
Time rewrite -(delete_singleton i x).
Time by eapply delete_local_update, lookup_singleton.
Time Qed.
Time
Lemma delete_local_update_cancelable m1 m2 i mx `{!Cancelable mx} :
  m1 !! i \226\137\161 mx \226\134\146 m2 !! i \226\137\161 mx \226\134\146 (m1, m2) ~l~> (delete i m1, delete i m2).
Time Proof.
Time (intros Hm1i Hm2i).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time (split; [ eauto using delete_validN |  ]).
Time (intros j).
Time (destruct (decide (i = j)) as [->| ]).
Time -
Time move : {}(Hm j) {}.
Time rewrite !lookup_op Hm1i Hm2i !lookup_delete.
Time (intros Hmx).
Time rewrite (cancelableN mx n (mf !! j) None) ?right_id // -Hmx -Hm1i.
Time Qed.
Time
Lemma tac_and_destruct_choice \206\148 i p d j P P1 P2 Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 (if p then IntoAnd p P P1 P2 : Type
     else TCOr (IntoAnd p P P1 P2)
            (TCAnd (IntoSep P P1 P2)
               match d with
               | Left => TCOr (Affine P2) (Absorbing Q)
               | _ => TCOr (Affine P1) (Absorbing Q)
               end))
    \226\134\146 match
        envs_simple_replace i p
          (Esnoc Enil j match d with
                        | Left => P1
                        | _ => P2
                        end) \206\148
      with
      | None => False
      | Some \206\148' => envs_entails \206\148' Q
      end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:Hrep ; last  done).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? HP HQ).
Time rewrite envs_simple_replace_singleton_sound //=.
Time (destruct p).
Time {
Time rewrite (into_and _ P) HQ.
Time (destruct d; simpl).
Time -
Time by rewrite and_elim_l wand_elim_r.
Time -
Time by rewrite and_elim_r wand_elim_r.
Time }
Time (destruct HP as [?| [? ?]]).
Time {
Time rewrite (into_and _ P) HQ.
Time (apply Hmv).
Time -
Time by rewrite lookup_op !lookup_delete_ne // Hm lookup_op.
Time (destruct d; simpl).
Time -
Time by rewrite and_elim_l wand_elim_r.
Time Qed.
Time -
Time by rewrite and_elim_r wand_elim_r.
Time
Lemma delete_singleton_local_update_cancelable m i 
  x `{!Cancelable (Some x)} :
  m !! i \226\137\161 Some x \226\134\146 (m, {[i := x]}) ~l~> (delete i m, \226\136\133).
Time Proof.
Time (intros).
Time rewrite -(delete_singleton i x).
Time }
Time rewrite (into_sep P) HQ.
Time
(apply (delete_local_update_cancelable m _ i (Some x));
  [ done | by rewrite lookup_singleton ]).
Time Qed.
Time
Lemma gmap_fmap_mono {B : cmraT} (f : A \226\134\146 B) m1 m2 :
  Proper ((\226\137\161) ==> (\226\137\161)) f
  \226\134\146 (\226\136\128 x y, x \226\137\188 y \226\134\146 f x \226\137\188 f y) \226\134\146 m1 \226\137\188 m2 \226\134\146 fmap f m1 \226\137\188 fmap f m2.
Time Proof.
Time (intros ? ?).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !lookup_included =>Hm i).
Time rewrite !lookup_fmap.
Time by apply option_fmap_mono.
Time Qed.
Time End properties.
Time (destruct d; simpl).
Time -
Time by rewrite (comm _ P1) -assoc wand_elim_r sep_elim_r.
Time Section unital_properties.
Time Context `{Countable K} {A : ucmraT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time Implicit Types x y : A.
Time
Lemma insert_alloc_local_update m1 m2 i x x' y' :
  m1 !! i = Some x
  \226\134\146 m2 !! i = None
    \226\134\146 (x, \206\181) ~l~> (x', y') \226\134\146 (m1, m2) ~l~> (<[i:=x']> m1, <[i:=y']> m2).
Time -
Time by rewrite -assoc wand_elim_r sep_elim_r.
Time Proof.
Time (intros Hi1 Hi2 Hup).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hm1v Hm).
Time (assert (Hif : mf !! i \226\137\161{n}\226\137\161 Some x)).
Time {
Time move : {}(Hm i) {}.
Time Qed.
Time by rewrite lookup_op Hi1 Hi2 left_id.
Time
Lemma tac_frame_pure \206\148 (\207\134 : Prop) P Q :
  \207\134 \226\134\146 Frame true \226\140\156\207\134\226\140\157 P Q \226\134\146 envs_entails \206\148 Q \226\134\146 envs_entails \206\148 P.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? Hframe {+}->).
Time rewrite -Hframe /=.
Time }
Time (destruct (Hup n (mf !! i)) as [Hx'v Hx'eq]).
Time rewrite -persistently_and_intuitionistically_sep_l persistently_pure.
Time {
Time move : {}(Hm1v i) {}.
Time by rewrite Hi1.
Time }
Time {
Time by rewrite Hif -(inj_iff Some) -Some_op_opM -Some_op left_id.
Time auto using and_intro, pure_intro.
Time Qed.
Time
Lemma tac_frame \206\148 i p R P Q :
  envs_lookup i \206\148 = Some (p, R)
  \226\134\146 Frame p R P Q
    \226\134\146 envs_entails (envs_delete false i p \206\148) Q \226\134\146 envs_entails \206\148 P.
Time Proof.
Time rewrite envs_entails_eq.
Time (intros ? Hframe HQ).
Time rewrite (envs_lookup_sound' _ false) //.
Time by rewrite -Hframe HQ.
Time }
Time split.
Time -
Time by apply insert_validN.
Time -
Time (simpl in Hx'eq).
Time by rewrite -(insert_idN n mf i x) // -insert_op -Hm Hx'eq Hif.
Time Qed.
Time
Lemma tac_or_l \206\148 P Q1 Q2 :
  FromOr P Q1 Q2 \226\134\146 envs_entails \206\148 Q1 \226\134\146 envs_entails \206\148 P.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? {+}->).
Time rewrite -(from_or P).
Time by apply or_intro_l'.
Time Qed.
Time
Lemma tac_or_r \206\148 P Q1 Q2 :
  FromOr P Q1 Q2 \226\134\146 envs_entails \206\148 Q2 \226\134\146 envs_entails \206\148 P.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? {+}->).
Time rewrite -(from_or P).
Time by apply or_intro_r'.
Time Qed.
Time
Lemma tac_or_destruct \206\148 i p j1 j2 P P1 P2 Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 IntoOr P P1 P2
    \226\134\146 match
        envs_simple_replace i p (Esnoc Enil j1 P1) \206\148,
        envs_simple_replace i p (Esnoc Enil j2 P2) \206\148
      with
      | Some \206\1481, Some \206\1482 => envs_entails \206\1481 Q \226\136\167 envs_entails \206\1482 Q
      | _, _ => False
      end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace i p (Esnoc Enil j1 P1)) as [\206\1481| ] eqn:? ;
 last  done).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace i p (Esnoc Enil j2 P2)) as [\206\1482| ] eqn:? ;
 last  done).
Time rewrite envs_entails_eq.
Time (intros ? ? (HP1, HP2)).
Time rewrite envs_lookup_sound //.
Time (rewrite (into_or P) intuitionistically_if_or sep_or_r; apply or_elim).
Time -
Time rewrite (envs_simple_replace_singleton_sound' _ \206\1481) //.
Time by rewrite wand_elim_r.
Time -
Time rewrite (envs_simple_replace_singleton_sound' _ \206\1482) //.
Time Qed.
Time End unital_properties.
Time by rewrite wand_elim_r.
Time
Instance gmap_fmap_ne  `{Countable K} {A B : ofeT} 
 (f : A \226\134\146 B) n:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (fmap (M:=gmap K) f)).
Time Proof.
Time by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne.
Time Qed.
Time Qed.
Time
Lemma tac_forall_intro {A} \206\148 (\206\166 : A \226\134\146 PROP) Q :
  FromForall Q \206\166 \226\134\146 (\226\136\128 a, envs_entails \206\148 (\206\166 a)) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq /FromForall
 =>{+}<-).
Time
Instance gmap_fmap_cmra_morphism  `{Countable K} {A B : cmraT} 
 (f : A \226\134\146 B) `{!CmraMorphism f}:
 (CmraMorphism (fmap f : gmap K A \226\134\146 gmap K B)).
Time Proof.
Time (split; try apply _).
Time (apply forall_intro).
Time Qed.
Time
Lemma tac_forall_specialize {A} \206\148 i p P (\206\166 : A \226\134\146 PROP) 
  Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 IntoForall P \206\166
    \226\134\146 (\226\136\131 x : A,
         match envs_simple_replace i p (Esnoc Enil i (\206\166 x)) \206\148 with
         | None => False
         | Some \206\148' => envs_entails \206\148' Q
         end) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time rewrite envs_entails_eq.
Time (intros ? ? (x, ?)).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace) as [\206\148'| ] eqn:? ; last  done).
Time (rewrite envs_simple_replace_singleton_sound //; simpl).
Time by rewrite (into_forall P) (forall_elim x) wand_elim_r.
Time Qed.
Time
Lemma tac_forall_revert {A} \206\148 (\206\166 : A \226\134\146 PROP) :
  envs_entails \206\148 (\226\136\128 a, \206\166 a) \226\134\146 \226\136\128 a, envs_entails \206\148 (\206\166 a).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>H\206\148 a).
Time by rewrite H\206\148 (forall_elim a).
Time Qed.
Time
Lemma tac_exist {A} \206\148 P (\206\166 : A \226\134\146 PROP) :
  FromExist P \206\166 \226\134\146 (\226\136\131 a, envs_entails \206\148 (\206\166 a)) \226\134\146 envs_entails \206\148 P.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? [a ?]).
Time rewrite -(from_exist P).
Time -
Time by intros n m ? i; rewrite lookup_fmap; apply (cmra_morphism_validN _).
Time eauto using exist_intro'.
Time -
Time (intros m).
Time (<ssreflect_plugin::ssrtclintros@0> apply Some_proper =>i).
Time rewrite lookup_fmap !lookup_omap lookup_fmap.
Time Qed.
Time
Lemma tac_exist_destruct {A} \206\148 i p j P (\206\166 : A \226\134\146 PROP) 
  Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 IntoExist P \206\166
    \226\134\146 (\226\136\128 a,
         match envs_simple_replace i p (Esnoc Enil j (\206\166 a)) \206\148 with
         | Some \206\148' => envs_entails \206\148' Q
         | None => False
         end) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? H\206\166).
Time rewrite envs_lookup_sound //.
Time case : {}(m !! i) {} =>//= ?.
Time rewrite (into_exist P) intuitionistically_if_exist sep_exist_r.
Time (apply cmra_morphism_pcore, _).
Time -
Time (intros m1 m2 i).
Time by rewrite lookup_op !lookup_fmap lookup_op cmra_morphism_op.
Time
(<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a; specialize 
  (H\206\166 a) as Hmatch).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:Hrep ; last  done).
Time Qed.
Time (rewrite envs_simple_replace_singleton_sound' //; simpl).
Time
Definition gmapO_map `{Countable K} {A} {B} (f : A -n> B) :
  gmapO K A -n> gmapO K B := OfeMor (fmap f : gmapO K A \226\134\146 gmapO K B).
Time by rewrite wand_elim_r.
Time Qed.
Time
Lemma tac_modal_elim \206\148 i p p' \207\134 P' P Q Q' :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 ElimModal \207\134 p p' P P' Q Q'
    \226\134\146 \207\134
      \226\134\146 match envs_replace i p p' (Esnoc Enil i P') \206\148 with
        | None => False
        | Some \206\148' => envs_entails \206\148' Q'
        end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_replace _ _ _ _ _) as [\206\148'| ] eqn:? ; last  done).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? ? H\206\148).
Time rewrite envs_replace_singleton_sound //=.
Time rewrite H\206\148.
Time
Instance gmapO_map_ne  `{Countable K} {A} {B}:
 (NonExpansive (@gmapO_map K _ _ A B)).
Time Proof.
Time (intros n f g Hf m k; rewrite /= !lookup_fmap).
Time (destruct (_ !! k) eqn:?; simpl; constructor; apply Hf).
Time Qed.
Time by eapply elim_modal.
Time Qed.
Time Lemma tac_accu \206\148 P : env_to_prop (env_spatial \206\148) = P \226\134\146 envs_entails \206\148 P.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>{+}<-).
Time rewrite env_to_prop_sound !of_envs_eq and_elim_r sep_elim_r //.
Time #[program]
Definition gmapOF K `{Countable K} (F : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => gmapO K (oFunctor_car F A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg => gmapO_map (oFunctor_map F fg) |}.
Time Qed.
Time
Lemma tac_inv_elim {X : Type} \206\148 i j \207\134 p Pinv Pin Pout
  (Pclose : option (X \226\134\146 PROP)) Q (Q' : X \226\134\146 PROP) :
  envs_lookup i \206\148 = Some (p, Pinv)
  \226\134\146 ElimInv \207\134 Pinv Pin Pout Pclose Q Q'
    \226\134\146 \207\134
      \226\134\146 (\226\136\128 R,
           match
             envs_app false
               (Esnoc Enil j
                  (Pin
                   -\226\136\151 (\226\136\128 x, Pout x -\226\136\151 pm_option_fun Pclose x -\226\136\151? Q' x) -\226\136\151 R)%I)
               (envs_delete false i p \206\148)
           with
           | Some \206\148'' => envs_entails \206\148'' R
           | None => False
           end) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? Hinv ? /
 (_ Q) Hmatch).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) eqn:? ; last 
 done).
Time
(rewrite -Hmatch (envs_lookup_sound' _ false) // envs_app_singleton_sound //;
  simpl).
Time
(<ssreflect_plugin::ssrtclseq@0> apply wand_elim_r', wand_mono ; last  done).
Time (apply wand_intro_r, wand_intro_r).
Time rewrite intuitionistically_if_elim -assoc.
Time (destruct Pclose; simpl in *).
Time -
Time setoid_rewrite wand_curry.
Time Next Obligation.
Time
by
 intros K ? ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A ? B ? x).
Time rewrite /= -{+2}(map_fmap_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply oFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -map_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply oFunctor_compose).
Time Qed.
Time
Instance gmapOF_contractive  K `{Countable K} F:
 (oFunctorContractive F \226\134\146 oFunctorContractive (gmapOF K F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, oFunctor_contractive.
Time Qed.
Time #[program]
Definition gmapURF K `{Countable K} (F : rFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => gmapUR K (rFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   gmapO_map (rFunctor_map F fg) |}.
Time auto.
Time -
Time setoid_rewrite  <- (right_id emp%I _ (Pout _)).
Time auto.
Time Qed.
Time End bi_tactics.
Time
Class TransformIntuitionisticEnv {PROP1} {PROP2} (M : modality PROP1 PROP2)
(C : PROP2 \226\134\146 PROP1 \226\134\146 Prop) (\206\147in : env PROP2) (\206\147out : env PROP1) :={
 transform_intuitionistic_env :
  (\226\136\128 P Q, C P Q \226\134\146 \226\150\161 P \226\138\162 M (\226\150\161 Q))
  \226\134\146 (\226\136\128 P Q, M P \226\136\167 M Q \226\138\162 M (P \226\136\167 Q)) \226\134\146 \226\150\161 [\226\136\167] \206\147in \226\138\162 M (\226\150\161 [\226\136\167] \206\147out);
 transform_intuitionistic_env_wf : env_wf \206\147in \226\134\146 env_wf \206\147out;
 transform_intuitionistic_env_dom :
  forall i, \206\147in !! i = None \226\134\146 \206\147out !! i = None}.
Time
Class TransformSpatialEnv {PROP1} {PROP2} (M : modality PROP1 PROP2)
(C : PROP2 \226\134\146 PROP1 \226\134\146 Prop) (\206\147in : env PROP2) (\206\147out : env PROP1)
(filtered : bool) :={transform_spatial_env :
                      (\226\136\128 P Q, C P Q \226\134\146 P \226\138\162 M Q)
                      \226\134\146 [\226\136\151] \206\147in
                        \226\138\162 M ([\226\136\151] \206\147out) \226\136\151 (if filtered then True else emp);
                     transform_spatial_env_wf : env_wf \206\147in \226\134\146 env_wf \206\147out;
                     transform_spatial_env_dom :
                      forall i, \206\147in !! i = None \226\134\146 \206\147out !! i = None}.
Time
Inductive IntoModalIntuitionisticEnv {PROP2} :
\226\136\128 {PROP1} (M : modality PROP1 PROP2) (\206\147in : env PROP2) (\206\147out : env PROP1),
  modality_action PROP1 PROP2 \226\134\146 Prop :=
  | MIEnvIsEmpty_intuitionistic :
      forall {PROP1} (M : modality PROP1 PROP2),
      IntoModalIntuitionisticEnv M Enil Enil MIEnvIsEmpty
  | MIEnvForall_intuitionistic :
      forall (M : modality PROP2 PROP2) (C : PROP2 \226\134\146 Prop) \206\147,
      TCForall C (env_to_list \206\147)
      \226\134\146 IntoModalIntuitionisticEnv M \206\147 \206\147 (MIEnvForall C)
  | MIEnvTransform_intuitionistic :
      forall {PROP1} (M : modality PROP1 PROP2) (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop)
        \206\147in \206\147out,
      TransformIntuitionisticEnv M C \206\147in \206\147out
      \226\134\146 IntoModalIntuitionisticEnv M \206\147in \206\147out (MIEnvTransform C)
  | MIEnvClear_intuitionistic :
      forall {PROP1 : bi} (M : modality PROP1 PROP2) \206\147,
      IntoModalIntuitionisticEnv M \206\147 Enil MIEnvClear
  | MIEnvId_intuitionistic :
      forall (M : modality PROP2 PROP2) \206\147,
      IntoModalIntuitionisticEnv M \206\147 \206\147 MIEnvId.
Time Existing Class IntoModalIntuitionisticEnv.
Time
Existing Instances
 MIEnvIsEmpty_intuitionistic, MIEnvForall_intuitionistic, MIEnvTransform_intuitionistic, MIEnvClear_intuitionistic, MIEnvId_intuitionistic.
Time
Inductive IntoModalSpatialEnv {PROP2} :
\226\136\128 {PROP1} (M : modality PROP1 PROP2) (\206\147in : env PROP2) (\206\147out : env PROP1),
  modality_action PROP1 PROP2 \226\134\146 bool \226\134\146 Prop :=
  | MIEnvIsEmpty_spatial :
      forall {PROP1} (M : modality PROP1 PROP2),
      IntoModalSpatialEnv M Enil Enil MIEnvIsEmpty false
  | MIEnvForall_spatial :
      forall (M : modality PROP2 PROP2) (C : PROP2 \226\134\146 Prop) \206\147,
      TCForall C (env_to_list \206\147)
      \226\134\146 IntoModalSpatialEnv M \206\147 \206\147 (MIEnvForall C) false
  | MIEnvTransform_spatial :
      forall {PROP1} (M : modality PROP1 PROP2) (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop)
        \206\147in \206\147out fi,
      TransformSpatialEnv M C \206\147in \206\147out fi
      \226\134\146 IntoModalSpatialEnv M \206\147in \206\147out (MIEnvTransform C) fi
  | MIEnvClear_spatial :
      forall {PROP1 : bi} (M : modality PROP1 PROP2) \206\147,
      IntoModalSpatialEnv M \206\147 Enil MIEnvClear false
  | MIEnvId_spatial :
      forall (M : modality PROP2 PROP2) \206\147,
      IntoModalSpatialEnv M \206\147 \206\147 MIEnvId false.
Time Existing Class IntoModalSpatialEnv.
Time
Existing Instances
 MIEnvIsEmpty_spatial, MIEnvForall_spatial, MIEnvTransform_spatial, MIEnvClear_spatial, MIEnvId_spatial.
Time Section tac_modal_intro.
Time Context {PROP1 PROP2 : bi} (M : modality PROP1 PROP2).
Time #[global]
Instance transform_intuitionistic_env_nil  C:
 (TransformIntuitionisticEnv M C Enil Enil).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> split; [  | eauto using Enil_wf | done ]
 =>/= ? ?).
Time rewrite !intuitionistically_True_emp -modality_emp //.
Time Qed.
Time #[global]
Instance transform_intuitionistic_env_snoc  (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop) 
 \206\147 \206\147' i P Q:
 (C P Q
  \226\134\146 TransformIntuitionisticEnv M C \206\147 \206\147'
    \226\134\146 TransformIntuitionisticEnv M C (Esnoc \206\147 i P) (Esnoc \206\147' i Q)).
Time Proof.
Time (intros ? [H\206\147 Hwf Hdom]; split; simpl).
Time -
Time (intros HC Hand).
Time rewrite intuitionistically_and HC // H\206\147 //.
Time by rewrite Hand -intuitionistically_and.
Time -
Time (inversion 1; constructor; auto).
Time -
Time (intros j).
Time (destruct (ident_beq _ _); naive_solver).
Time Qed.
Time #[global]
Instance transform_intuitionistic_env_snoc_not  (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop) 
 \206\147 \206\147' i P:
 (TransformIntuitionisticEnv M C \206\147 \206\147'
  \226\134\146 TransformIntuitionisticEnv M C (Esnoc \206\147 i P) \206\147') |100.
Time Proof.
Time (intros [H\206\147 Hwf Hdom]; split; simpl).
Time -
Time (intros HC Hand).
Time by rewrite and_elim_r H\206\147.
Time -
Time (inversion 1; auto).
Time -
Time (intros j).
Time (destruct (ident_beq _ _); naive_solver).
Time Next Obligation.
Time
by
 intros K ? ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, rFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A ? B ? x).
Time rewrite /= -{+2}(map_fmap_id x).
Time Qed.
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply rFunctor_id).
Time #[global]
Instance transform_spatial_env_nil  C:
 (TransformSpatialEnv M C Enil Enil false).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> split; [  | eauto using Enil_wf | done ]
 =>/= ?).
Time Qed.
Time by rewrite right_id -modality_emp.
Time Next Obligation.
Time (intros K ? ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -map_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply rFunctor_compose).
Time Qed.
Time
Instance gmapRF_contractive  K `{Countable K} F:
 (rFunctorContractive F \226\134\146 urFunctorContractive (gmapURF K F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, rFunctor_contractive.
Time Qed.
Time Qed.
Time #[global]
Instance transform_spatial_env_snoc  (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop) 
 \206\147 \206\147' i P Q fi:
 (C P Q
  \226\134\146 TransformSpatialEnv M C \206\147 \206\147' fi
    \226\134\146 TransformSpatialEnv M C (Esnoc \206\147 i P) (Esnoc \206\147' i Q) fi).
Time Proof.
Time (intros ? [H\206\147 Hwf Hdom]; split; simpl).
Time -
Time (intros HC).
Time by rewrite {+1}(HC P) // H\206\147 // assoc modality_sep.
Time -
Time (inversion 1; constructor; auto).
Time -
Time (intros j).
Time (destruct (ident_beq _ _); naive_solver).
Time Qed.
Time #[global]
Instance transform_spatial_env_snoc_not  (C : PROP2 \226\134\146 PROP1 \226\134\146 Prop) 
 \206\147 \206\147' i P fi fi':
 (TransformSpatialEnv M C \206\147 \206\147' fi
  \226\134\146 TCIf (TCEq fi false) (TCIf (Affine P) (TCEq fi' false) (TCEq fi' true))
      (TCEq fi' true) \226\134\146 TransformSpatialEnv M C (Esnoc \206\147 i P) \206\147' fi') |100.
Time Proof.
Time (intros [H\206\147 Hwf Hdom] Hif; split; simpl).
Time -
Time (intros ?).
Time rewrite H\206\147 //.
Time (destruct Hif as [-> [? ->| ->]| ->]).
Time +
Time by rewrite (affine P) left_id.
Time +
Time by rewrite right_id comm (True_intro P).
Time +
Time by rewrite comm -assoc (True_intro (_ \226\136\151 P)%I).
Time -
Time (inversion 1; auto).
Time -
Time (intros j).
Time (destruct (ident_beq _ _); naive_solver).
Time Qed.
Time
Lemma tac_modal_intro {A} (sel : A) \206\147p \206\147s n \206\147p' \206\147s' 
  Q Q' fi :
  FromModal M sel Q' Q
  \226\134\146 IntoModalIntuitionisticEnv M \206\147p \206\147p' (modality_intuitionistic_action M)
    \226\134\146 IntoModalSpatialEnv M \206\147s \206\147s' (modality_spatial_action M) fi
      \226\134\146 (if fi then Absorbing Q' else TCTrue)
        \226\134\146 envs_entails (Envs \206\147p' \206\147s' n) Q \226\134\146 envs_entails (Envs \206\147p \206\147s n) Q'.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq /FromModal
 !of_envs_eq =>HQ' H\206\147p H\206\147s ? HQ).
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>- [? ? ?]).
Time (assert (Hwf : envs_wf (Envs \206\147p' \206\147s' n))).
Time {
Time (split; simpl in *).
Time -
Time (destruct H\206\147p as [| | ? ? ? ? ? []| | ]; eauto using Enil_wf).
Time -
Time (destruct H\206\147s as [| | ? ? ? ? ? ? []| | ]; eauto using Enil_wf).
Time -
Time (assert (\226\136\128 i, \206\147p !! i = None \226\134\146 \206\147p' !! i = None)).
Time {
Time (destruct H\206\147p as [| | ? ? ? ? ? []| | ]; eauto).
Time }
Time (assert (\226\136\128 i, \206\147s !! i = None \226\134\146 \206\147s' !! i = None)).
Time {
Time (destruct H\206\147s as [| | ? ? ? ? ? ? []| | ]; eauto).
Time }
Time naive_solver.
Time }
Time (assert (HMp : (\226\150\161 [\226\136\167] \206\147p \226\138\162 M (\226\150\161 [\226\136\167] \206\147p'))%I)).
Time {
Time (remember (modality_intuitionistic_action M)).
Time
(destruct H\206\147p as [?| M C \206\147p ?%TCForall_Forall| ? M C \206\147p \206\147p' []| ? M \206\147p| M \206\147p];
  simpl).
Time -
Time
rewrite {+1}intuitionistically_elim_emp (modality_emp M)
 intuitionistically_True_emp //.
Time -
Time eauto using modality_intuitionistic_forall_big_and.
Time -
Time eauto using modality_intuitionistic_transform, modality_and_transform.
Time -
Time
by rewrite {+1}intuitionistically_elim_emp (modality_emp M)
 intuitionistically_True_emp.
Time -
Time eauto using modality_intuitionistic_id.
Time }
Time
(move : {}HQ' {}; <ssreflect_plugin::ssrtclintros@0> rewrite -HQ pure_True //
  left_id HMp =>HQ' {HQ Hwf HMp}).
Time (remember (modality_spatial_action M)).
Time
(destruct H\206\147s
  as [?| M C \206\147s ?%TCForall_Forall| ? M C \206\147s \206\147s' fi []| ? M \206\147s| M \206\147s]; 
  simpl).
Time -
Time by rewrite -HQ' /= !right_id.
Time -
Time rewrite -HQ' {+1}(modality_spatial_forall_big_sep _ _ \206\147s) //.
Time by rewrite modality_sep.
Time -
Time (destruct fi).
Time +
Time rewrite -(absorbing Q') /bi_absorbingly -HQ' (comm _ True%I).
Time rewrite -modality_sep -assoc.
Time (apply sep_mono_r).
Time eauto using modality_spatial_transform.
Time +
Time rewrite -HQ' -modality_sep.
Time (apply sep_mono_r).
Time rewrite -(right_id emp%I bi_sep (M _)).
Time eauto using modality_spatial_transform.
Time -
Time rewrite -HQ' /= right_id comm -{+2}(modality_spatial_clear M) //.
Time by rewrite (True_intro ([\226\136\151] \206\147s)%I).
Time -
Time rewrite -HQ' {+1}(modality_spatial_id M ([\226\136\151] \206\147s)%I) //.
Time by rewrite -modality_sep.
Time Qed.
Time End tac_modal_intro.
Time Section sbi_tactics.
Time Context {PROP : sbi}.
Time Implicit Type \206\147 : env PROP.
Time Implicit Type \206\148 : envs PROP.
Time Implicit Types P Q : PROP.
Time
Lemma tac_rewrite \206\148 i p Pxy d Q :
  envs_lookup i \206\148 = Some (p, Pxy)
  \226\134\146 \226\136\128 {A : ofeT} (x y : A) (\206\166 : A \226\134\146 PROP),
      IntoInternalEq Pxy x y
      \226\134\146 Q \226\138\163\226\138\162 \206\166 match d with
               | Left => y
               | _ => x
               end
        \226\134\146 NonExpansive \206\166
          \226\134\146 envs_entails \206\148 (\206\166 match d with
                              | Left => x
                              | _ => y
                              end) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time (intros ? A x y ? HPxy -> ?).
Time rewrite envs_entails_eq.
Time (apply internal_eq_rewrite'; auto).
Time rewrite {+1}envs_lookup_sound //.
Time
rewrite (into_internal_eq Pxy x y) intuitionistically_if_elim sep_elim_l.
Time (destruct d; auto using internal_eq_sym).
Time Qed.
Time
Lemma tac_rewrite_in \206\148 i p Pxy j q P d Q :
  envs_lookup i \206\148 = Some (p, Pxy)
  \226\134\146 envs_lookup j \206\148 = Some (q, P)
    \226\134\146 \226\136\128 {A : ofeT} (x y : A) (\206\166 : A \226\134\146 PROP),
        IntoInternalEq Pxy x y
        \226\134\146 P \226\138\163\226\138\162 \206\166 match d with
                 | Left => y
                 | _ => x
                 end
          \226\134\146 NonExpansive \206\166
            \226\134\146 match
                envs_simple_replace j q
                  (Esnoc Enil j (\206\166 match d with
                                   | Left => x
                                   | _ => y
                                   end)) \206\148
              with
              | None => False
              | Some \206\148' => envs_entails \206\148' Q
              end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq /IntoInternalEq
 =>? ? A x y \206\166 HPxy HP ? Hentails).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:? ; last  done).
Time rewrite -Hentails.
Time rewrite -(idemp bi_and (of_envs \206\148)) {+2}(envs_lookup_sound _ i) //.
Time rewrite (envs_simple_replace_singleton_sound _ _ j) //=.
Time rewrite HP HPxy (intuitionistically_if_elim _ (_ \226\137\161 _)%I) sep_elim_l.
Time rewrite persistent_and_affinely_sep_r -assoc.
Time (apply wand_elim_r').
Time rewrite -persistent_and_affinely_sep_r.
Time (apply impl_elim_r').
Time (destruct d).
Time -
Time (apply (internal_eq_rewrite x y (\206\187 y, \226\150\161?q \206\166 y -\226\136\151 of_envs \206\148')%I)).
Time solve_proper.
Time -
Time rewrite internal_eq_sym.
Time (eapply (internal_eq_rewrite y x (\206\187 y, \226\150\161?q \206\166 y -\226\136\151 of_envs \206\148')%I)).
Time solve_proper.
Time Qed.
Time
Class MaybeIntoLaterNEnvs (n : nat) (\206\1481 \206\1482 : envs PROP) :={
 into_later_intuitionistic :
  TransformIntuitionisticEnv (modality_laterN n) (MaybeIntoLaterN false n)
    (env_intuitionistic \206\1481) (env_intuitionistic \206\1482);
 into_later_spatial :
  TransformSpatialEnv (modality_laterN n) (MaybeIntoLaterN false n)
    (env_spatial \206\1481) (env_spatial \206\1482) false}.
Time #[global]
Instance into_laterN_envs  n \206\147p1 \206\147p2 \206\147s1 \206\147s2 m:
 (TransformIntuitionisticEnv (modality_laterN n) (MaybeIntoLaterN false n)
    \206\147p1 \206\147p2
  \226\134\146 TransformSpatialEnv (modality_laterN n) (MaybeIntoLaterN false n) \206\147s1 \206\147s2
      false \226\134\146 MaybeIntoLaterNEnvs n (Envs \206\147p1 \206\147s1 m) (Envs \206\147p2 \206\147s2 m)).
Time Proof.
Time by split.
Time Qed.
Time
Lemma into_laterN_env_sound n \206\1481 \206\1482 :
  MaybeIntoLaterNEnvs n \206\1481 \206\1482 \226\134\146 of_envs \206\1481 \226\138\162 \226\150\183^n of_envs \206\1482.
Time Proof.
Time
(intros [[Hp ? ?] [Hs ? ?]]; rewrite !of_envs_eq /= !laterN_and !laterN_sep).
Time rewrite -{+1}laterN_intro.
Time (apply and_mono, sep_mono).
Time -
Time (apply pure_mono; destruct 1; constructor; naive_solver).
Time -
Time (apply Hp; rewrite /= /MaybeIntoLaterN).
Time +
Time (intros P Q ->).
Time by rewrite laterN_intuitionistically_2.
Time +
Time (intros P Q).
Time by rewrite laterN_and.
Time -
Time by rewrite Hs //= right_id.
Time Qed.
Time
Lemma tac_l\195\182b \206\148 i Q :
  env_spatial_is_nil \206\148 = true
  \226\134\146 match envs_app true (Esnoc Enil i (\226\150\183 Q)%I) \206\148 with
    | None => False
    | Some \206\148' => envs_entails \206\148' Q
    end \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (envs_app _ _ _) eqn:? ; last 
 done).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? HQ).
Time rewrite (env_spatial_is_nil_intuitionistically \206\148) //.
Time rewrite -(persistently_and_emp_elim Q).
Time
(<ssreflect_plugin::ssrtclseq@0> apply and_intro ; first  apply : {}affine
 {}).
Time rewrite -(l\195\182b (<pers> Q)%I) later_persistently.
Time (apply impl_intro_l).
Time (rewrite envs_app_singleton_sound //; simpl; rewrite HQ).
Time
rewrite persistently_and_intuitionistically_sep_l
 -{+1}intuitionistically_idemp.
Time
rewrite intuitionistically_sep_2 wand_elim_r
 intuitionistically_into_persistently_1 //.
Time Qed.
Time End sbi_tactics.
