Time From iris.bi Require Export bi.
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
Time by rewrite HP wand_elim_r.
Time Qed.
Time Class AffineEnv (\206\147 : env PROP) :=
         affine_env : Forall Affine \206\147.
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
Time Qed.
Time
Instance affine_env_spatial  \206\148:
 (AffineEnv (env_spatial \206\148) \226\134\146 Affine ([\226\136\151] env_spatial \206\148)).
Time Proof.
Time (intros H).
Time (induction H; simpl; apply _).
Time Qed.
Time Lemma tac_emp_intro \206\148 : AffineEnv (env_spatial \206\148) \226\134\146 envs_entails \206\148 emp.
Time Proof.
Time (intros).
Time by rewrite envs_entails_eq (affine (of_envs \206\148)).
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
Time -
Time rewrite from_assumption.
Time (destruct H; by rewrite sep_elim_l).
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
Time Lemma tac_ex_falso \206\148 Q : envs_entails \206\148 False \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time by rewrite envs_entails_eq -(False_elim Q).
Time Qed.
Time
Lemma tac_false_destruct \206\148 i p P Q :
  envs_lookup i \206\148 = Some (p, P) \226\134\146 P = False%I \226\134\146 envs_entails \206\148 Q.
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
Time -
Time by apply pure_intro.
Time Qed.
Time
Lemma tac_pure \206\148 i p P \207\134 Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 IntoPure P \207\134
    \226\134\146 (if p then TCTrue else TCOr (Affine P) (Absorbing Q))
      \226\134\146 (\207\134 \226\134\146 envs_entails (envs_delete true i p \206\148) Q) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? HPQ HQ).
Time (rewrite envs_lookup_sound //; simpl).
Time (destruct p; simpl).
Time -
Time
rewrite (into_pure P) -persistently_and_intuitionistically_sep_l
 persistently_pure.
Time by apply pure_elim_l.
Time -
Time (destruct HPQ).
Time +
Time
rewrite -(affine_affinely P) (into_pure P) -persistent_and_affinely_sep_l.
Time by apply pure_elim_l.
Time +
Time
rewrite (into_pure P) -(persistent_absorbingly_affinely \226\140\156_\226\140\157%I)
 absorbingly_sep_lr.
Time rewrite -persistent_and_affinely_sep_l.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>?).
Time by rewrite HQ.
Time Qed.
Time
Lemma tac_pure_revert \206\148 \207\134 Q : envs_entails \206\148 (\226\140\156\207\134\226\140\157 \226\134\146 Q) \226\134\146 \207\134 \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time rewrite envs_entails_eq.
Time (intros H\206\148 ?).
Time by rewrite H\206\148 pure_True // left_id.
Time Qed.
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
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? ? HPQ HQ).
Time rewrite envs_replace_singleton_sound //=.
Time (destruct p; simpl; rewrite /bi_intuitionistically).
Time -
Time by rewrite -(into_persistent true P) /= wand_elim_r.
Time -
Time (destruct HPQ).
Time +
Time
rewrite -(affine_affinely P) (_ : P = <pers>?false P)%I //
 (into_persistent _ P) wand_elim_r //.
Time +
Time rewrite (_ : P = <pers>?false P)%I // (into_persistent _ P).
Time
by rewrite -{+1}absorbingly_intuitionistically_into_persistently
 absorbingly_sep_l wand_elim_r HQ.
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
Time rewrite -(from_affinely P' P) -affinely_and_lr.
Time
by rewrite persistently_and_intuitionistically_sep_r intuitionistically_elim
 wand_elim_r.
Time -
Time (apply impl_intro_l).
Time (rewrite envs_app_singleton_sound //; simpl).
Time
by rewrite -(from_affinely P' P) persistent_and_affinely_sep_l_1 wand_elim_r.
Time Qed.
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
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /FromImpl envs_entails_eq =>{+}<-
 ? ?).
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
Time rewrite envs_app_singleton_sound //=.
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
Time Qed.
Time
Lemma tac_wand_intro_drop \206\148 P Q R :
  FromWand R P Q
  \226\134\146 TCOr (Affine P) (Absorbing Q) \226\134\146 envs_entails \206\148 Q \226\134\146 envs_entails \206\148 R.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq /FromWand =>{+}<-
 HPQ {+}->).
Time (apply wand_intro_l).
Time by rewrite sep_elim_r.
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
Time (destruct p; simpl in *).
Time -
Time rewrite -{+1}intuitionistically_idemp -{+1}intuitionistically_if_idemp.
Time rewrite {+1}(intuitionistically_intuitionistically_if q).
Time by rewrite HR assoc intuitionistically_if_sep_2 !wand_elim_r.
Time -
Time by rewrite HR assoc !wand_elim_r.
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
Time (intros ? ? ? HQ).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (_ \226\137\171= _) as [[\206\1481 \206\1482']| ] eqn:? ;
 last  done).
Time (destruct HQ as [HP1 HQ]).
Time
(destruct (envs_split _ _ _) as [[? \206\1482]| ] eqn:?; simplify_eq /=;
  destruct (envs_app _ _ _) eqn:?; simplify_eq /=).
Time rewrite envs_lookup_sound // envs_split_sound //.
Time (rewrite (envs_app_singleton_sound \206\1482) //; simpl).
Time rewrite HP1 (into_wand q false) /= -(add_modal P1' P1 Q).
Time cancel [P1'].
Time (apply wand_intro_l).
Time by rewrite assoc !wand_elim_r.
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
Time cancel [P1'].
Time (apply wand_intro_l).
Time by rewrite assoc !wand_elim_r.
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
Time rewrite -intuitionistically_if_idemp (into_wand q true) /=.
Time rewrite -(from_pure a P1) pure_True //.
Time rewrite -affinely_affinely_if affinely_True_emp affinely_emp.
Time by rewrite intuitionistically_emp left_id wand_elim_r.
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
Time (rewrite {+2}envs_simple_replace_singleton_sound' //; simpl).
Time
rewrite {+1}HP1 (into_absorbingly P1' P1) (persistent_persistently_2 P1).
Time
rewrite absorbingly_elim_persistently
 persistently_and_intuitionistically_sep_l assoc.
Time rewrite -intuitionistically_if_idemp -intuitionistically_idemp.
Time rewrite (intuitionistically_intuitionistically_if q).
Time
by rewrite intuitionistically_if_sep_2 (into_wand q true) wand_elim_l
 wand_elim_r.
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
Time (rewrite envs_replace_singleton_sound //; destruct q; simpl).
Time -
Time
by rewrite (_ : R = <pers>?false R)%I // (into_persistent _ R)
 absorbingly_elim_persistently sep_elim_r
 persistently_and_intuitionistically_sep_l wand_elim_r.
Time -
Time
by rewrite (absorbing_absorbingly R) (_ : R = <pers>?false R)%I //
 (into_persistent _ R) sep_elim_r persistently_and_intuitionistically_sep_l
 wand_elim_r.
Time Qed.
Time
Lemma tac_specialize_intuitionistic_helper_done \206\148 
  i q P : envs_lookup i \206\148 = Some (q, P) \226\134\146 envs_entails \206\148 (<absorb> P).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> <ssreflect_plugin::ssrtclintros@0>
 rewrite envs_entails_eq /bi_absorbingly =>/envs_lookup_sound =>{+}->).
Time rewrite intuitionistically_if_elim comm.
Time (f_equiv; auto using pure_intro).
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
Time rewrite envs_lookup_delete_sound //=.
Time rewrite HQ.
Time (destruct p; simpl; auto using wand_elim_r).
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
Time rewrite -(idemp bi_and (\226\150\161 of_envs \206\148)%I) {+1}HP // HPQ.
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
Time by rewrite -HP /= intuitionistically_emp emp_wand.
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
Time (intros [? ->] <-).
Time rewrite envs_lookup_sound' // envs_app_singleton_sound //=.
Time by rewrite wand_elim_r.
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
Time by rewrite HQ1 HQ2.
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
Time rewrite envs_lookup_delete_list_sound //.
Time rewrite from_seps.
Time rewrite envs_app_singleton_sound //=.
Time by rewrite wand_elim_r.
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
Time -
Time by rewrite /= (into_sep P) right_id -(comm _ P1) wand_elim_r.
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
Time (destruct d; simpl).
Time -
Time by rewrite and_elim_l wand_elim_r.
Time -
Time by rewrite and_elim_r wand_elim_r.
Time }
Time rewrite (into_sep P) HQ.
Time (destruct d; simpl).
Time -
Time by rewrite (comm _ P1) -assoc wand_elim_r sep_elim_r.
Time -
Time by rewrite -assoc wand_elim_r sep_elim_r.
Time Qed.
Time
Lemma tac_frame_pure \206\148 (\207\134 : Prop) P Q :
  \207\134 \226\134\146 Frame true \226\140\156\207\134\226\140\157 P Q \226\134\146 envs_entails \206\148 Q \226\134\146 envs_entails \206\148 P.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>? Hframe {+}->).
Time rewrite -Hframe /=.
Time rewrite -persistently_and_intuitionistically_sep_l persistently_pure.
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
Time by rewrite wand_elim_r.
Time Qed.
Time
Lemma tac_forall_intro {A} \206\148 (\206\166 : A \226\134\146 PROP) Q :
  FromForall Q \206\166 \226\134\146 (\226\136\128 a, envs_entails \206\148 (\206\166 a)) \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq /FromForall
 =>{+}<-).
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
Time eauto using exist_intro'.
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
Time rewrite (into_exist P) intuitionistically_if_exist sep_exist_r.
Time
(<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a; specialize 
  (H\206\166 a) as Hmatch).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (envs_simple_replace _ _ _ _) as [\206\148'| ] eqn:Hrep ; last  done).
Time (rewrite envs_simple_replace_singleton_sound' //; simpl).
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
Time by eapply elim_modal.
Time Qed.
Time Lemma tac_accu \206\148 P : env_to_prop (env_spatial \206\148) = P \226\134\146 envs_entails \206\148 P.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>{+}<-).
Time rewrite env_to_prop_sound !of_envs_eq and_elim_r sep_elim_r //.
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
Time Qed.
Time #[global]
Instance transform_spatial_env_nil  C:
 (TransformSpatialEnv M C Enil Enil false).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> split; [  | eauto using Enil_wf | done ]
 =>/= ?).
Time by rewrite right_id -modality_emp.
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
