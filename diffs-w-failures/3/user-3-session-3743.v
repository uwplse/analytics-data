Time From iris.algebra Require Export ofe.
Time From iris.algebra Require Import proofmode_classes.
Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Export gmap coPset local_updates.
Time Set Default Proof Using "Type".
Time Section language_mixin.
Time Context {expr val state observation : Type}.
Time Context (of_val : val \226\134\146 expr).
Time Context (to_val : expr \226\134\146 option val).
Time
Context
 (prim_step : expr
              \226\134\146 state \226\134\146 list observation \226\134\146 expr \226\134\146 state \226\134\146 list expr \226\134\146 Prop).
Time
Record LanguageMixin :={mixin_to_of_val :
                         forall v, to_val (of_val v) = Some v;
                        mixin_of_to_val :
                         forall e v, to_val e = Some v \226\134\146 of_val v = e;
                        mixin_val_stuck :
                         forall e \207\131 \206\186 e' \207\131' efs,
                         prim_step e \207\131 \206\186 e' \207\131' efs \226\134\146 to_val e = None}.
Time End language_mixin.
Time
Structure language :=
 Language {expr : Type;
           val : Type;
           state : Type;
           observation : Type;
           of_val : val \226\134\146 expr;
           to_val : expr \226\134\146 option val;
           prim_step :
            expr \226\134\146 state \226\134\146 list observation \226\134\146 expr \226\134\146 state \226\134\146 list expr \226\134\146 Prop;
           language_mixin : LanguageMixin of_val to_val prim_step}.
Time Delimit Scope expr_scope with E.
Time Delimit Scope val_scope with V.
Time Bind Scope expr_scope with expr.
Time Bind Scope val_scope with val.
Time Arguments Language {_} {_} {_} {_} {_} {_} {_} _.
Time Arguments of_val {_} _.
Time Arguments to_val {_} _.
Time Arguments prim_step {_} _ _ _ _ _ _.
Time Canonical Structure stateC \206\155 := leibnizC (state \206\155).
Time Canonical Structure valC \206\155 := leibnizC (val \206\155).
Time Canonical Structure exprC \206\155 := leibnizC (expr \206\155).
Time Definition cfg (\206\155 : language) := (list (expr \206\155) * state \206\155)%type.
Time
Class LanguageCtx {\206\155 : language} (K : expr \206\155 \226\134\146 expr \206\155) :={
 fill_not_val : forall e, to_val e = None \226\134\146 to_val (K e) = None;
 fill_step :
  forall e1 \207\1311 \206\186 e2 \207\1312 efs,
  prim_step e1 \207\1311 \206\186 e2 \207\1312 efs \226\134\146 prim_step (K e1) \207\1311 \206\186 (K e2) \207\1312 efs;
 fill_step_inv :
  forall e1' \207\1311 \206\186 e2 \207\1312 efs,
  to_val e1' = None
  \226\134\146 prim_step (K e1') \207\1311 \206\186 e2 \207\1312 efs
    \226\134\146 \226\136\131 e2', e2 = K e2' \226\136\167 prim_step e1' \207\1311 \206\186 e2' \207\1312 efs}.
Time Instance language_ctx_id  \206\155: (LanguageCtx (@id (expr \206\155))).
Time Proof.
Time (constructor; naive_solver).
Time Qed.
Time Inductive atomicity :=
       | StronglyAtomic : _
       | WeaklyAtomic : _.
Time Section language.
Time Context {\206\155 : language}.
Time Implicit Type v : val \206\155.
Time Implicit Type e : expr \206\155.
Time Lemma to_of_val v : to_val (of_val v) = Some v.
Time Proof.
Time (apply language_mixin).
Time Qed.
Time Lemma of_to_val e v : to_val e = Some v \226\134\146 of_val v = e.
Time Proof.
Time (apply language_mixin).
Time Qed.
Time
Lemma val_stuck e \207\131 \206\186 e' \207\131' efs : prim_step e \207\131 \206\186 e' \207\131' efs \226\134\146 to_val e = None.
Time Proof.
Time (apply language_mixin).
Time Qed.
Time
Definition reducible (e : expr \206\155) (\207\131 : state \206\155) :=
  \226\136\131 \206\186 e' \207\131' efs, prim_step e \207\131 \206\186 e' \207\131' efs.
Time
Definition reducible_no_obs (e : expr \206\155) (\207\131 : state \206\155) :=
  \226\136\131 e' \207\131' efs, prim_step e \207\131 [] e' \207\131' efs.
Time
Definition irreducible (e : expr \206\155) (\207\131 : state \206\155) :=
  \226\136\128 \206\186 e' \207\131' efs, \194\172 prim_step e \207\131 \206\186 e' \207\131' efs.
Time
Definition stuck (e : expr \206\155) (\207\131 : state \206\155) :=
  to_val e = None \226\136\167 irreducible e \207\131.
Time
Class Atomic (a : atomicity) (e : expr \206\155) : Prop :=
    atomic :
      forall \207\131 e' \206\186 \207\131' efs,
      prim_step e \207\131 \206\186 e' \207\131' efs
      \226\134\146 match a with
        | WeaklyAtomic => irreducible e' \207\131'
        | _ => is_Some (to_val e')
        end.
Time
Inductive step (\207\1291 : cfg \206\155) (\206\186 : list (observation \206\155)) (\207\1292 : cfg \206\155) : Prop :=
    step_atomic :
      forall e1 \207\1311 e2 \207\1312 efs t1 t2,
      \207\1291 = (t1 ++ e1 :: t2, \207\1311)
      \226\134\146 \207\1292 = (t1 ++ e2 :: t2 ++ efs, \207\1312)
        \226\134\146 prim_step e1 \207\1311 \206\186 e2 \207\1312 efs \226\134\146 step \207\1291 \206\186 \207\1292.
Time Hint Constructors step: core.
Time
Inductive nsteps : nat \226\134\146 cfg \206\155 \226\134\146 list (observation \206\155) \226\134\146 cfg \206\155 \226\134\146 Prop :=
  | nsteps_refl : forall \207\129, nsteps 0 \207\129 [] \207\129
  | nsteps_l :
      forall n \207\1291 \207\1292 \207\1293 \206\186 \206\186s,
      step \207\1291 \206\186 \207\1292 \226\134\146 nsteps n \207\1292 \206\186s \207\1293 \226\134\146 nsteps (S n) \207\1291 (\206\186 ++ \206\186s) \207\1293.
Time Hint Constructors nsteps: core.
Time Definition erased_step (\207\1291 \207\1292 : cfg \206\155) := \226\136\131 \206\186, step \207\1291 \206\186 \207\1292.
Time
Lemma erased_steps_nsteps \207\1291 \207\1292 :
  rtc erased_step \207\1291 \207\1292 \226\134\148 (\226\136\131 n \206\186s, nsteps n \207\1291 \206\186s \207\1292).
Time Proof.
Time split.
Time -
Time (induction 1; firstorder  eauto).
Time -
Time (intros (n, (\206\186s, Hsteps))).
Time (unfold erased_step).
Time (induction Hsteps; eauto using rtc_refl, rtc_l).
Time Qed.
Time Lemma of_to_val_flip v e : of_val v = e \226\134\146 to_val e = Some v.
Time From iris.base_logic Require Import base_logic.
Time Proof.
Time (intros <-).
Time by rewrite to_of_val.
Time Qed.
Time Lemma not_reducible e \207\131 : \194\172 reducible e \207\131 \226\134\148 irreducible e \207\131.
Time Proof.
Time (unfold reducible, irreducible).
Time naive_solver.
Time Qed.
Time Lemma reducible_not_val e \207\131 : reducible e \207\131 \226\134\146 to_val e = None.
Time Proof.
Time (intros (?, (?, (?, (?, ?)))); eauto using val_stuck).
Time Qed.
Time
Lemma reducible_no_obs_reducible e \207\131 : reducible_no_obs e \207\131 \226\134\146 reducible e \207\131.
Time Proof.
Time (intros (?, (?, (?, ?))); eexists; eauto).
Time Qed.
Time Lemma val_irreducible e \207\131 : is_Some (to_val e) \226\134\146 irreducible e \207\131.
Time Proof.
Time (intros [? ?] ? ? ? ? ?%val_stuck).
Time by destruct (to_val e).
Time Qed.
Time #[global]Instance of_val_inj : (Inj (=) (=) (@of_val \206\155)).
Time Proof.
Time by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv.
Time Qed.
Time Lemma strongly_atomic_atomic e a : Atomic StronglyAtomic e \226\134\146 Atomic a e.
Time Proof.
Time (unfold Atomic).
Time (destruct a; eauto using val_irreducible).
Time Qed.
Time
Lemma reducible_fill `{!@LanguageCtx \206\155 K} e \207\131 :
  to_val e = None \226\134\146 reducible (K e) \207\131 \226\134\146 reducible e \207\131.
Time Proof.
Time (intros ? (e', (\207\131', (k, (efs, Hstep)))); unfold reducible).
Time (apply fill_step_inv in Hstep as (e2', (_, Hstep)); eauto).
Time Qed.
Time
Lemma reducible_no_obs_fill `{!@LanguageCtx \206\155 K} e 
  \207\131 : to_val e = None \226\134\146 reducible_no_obs (K e) \207\131 \226\134\146 reducible_no_obs e \207\131.
Time Proof.
Time (intros ? (e', (\207\131', (efs, Hstep))); unfold reducible_no_obs).
Time (apply fill_step_inv in Hstep as (e2', (_, Hstep)); eauto).
Time Qed.
Time
Lemma irreducible_fill `{!@LanguageCtx \206\155 K} e \207\131 :
  to_val e = None \226\134\146 irreducible e \207\131 \226\134\146 irreducible (K e) \207\131.
Time Proof.
Time rewrite -!not_reducible.
Time naive_solver eauto using reducible_fill.
Time Qed.
Time
Lemma step_Permutation (t1 t1' t2 : list (expr \206\155)) 
  \206\186 \207\1311 \207\1312 :
  t1 \226\137\161\226\130\154 t1'
  \226\134\146 step (t1, \207\1311) \206\186 (t2, \207\1312) \226\134\146 \226\136\131 t2', t2 \226\137\161\226\130\154 t2' \226\136\167 step (t1', \207\1311) \206\186 (t2', \207\1312).
Time Proof.
Time (intros Ht [e1 \207\1311' e2 \207\1312' efs tl tr ? ? Hstep]; simplify_eq /=).
Time (move : {}Ht {}; rewrite -Permutation_middle (symmetry_iff (\226\137\161\226\130\154))).
Time (intros (tl', (tr', (->, Ht)))%Permutation_cons_inv).
Time (exists (tl' ++ e2 :: tr' ++ efs); split; [  | by econstructor ]).
Time by rewrite -!Permutation_middle !assoc_L Ht.
Time Qed.
Time
Lemma erased_step_Permutation (t1 t1' t2 : list (expr \206\155)) 
  \207\1311 \207\1312 :
  t1 \226\137\161\226\130\154 t1'
  \226\134\146 erased_step (t1, \207\1311) (t2, \207\1312)
    \226\134\146 \226\136\131 t2', t2 \226\137\161\226\130\154 t2' \226\136\167 erased_step (t1', \207\1311) (t2', \207\1312).
Time Proof.
Time (intros Heq [? Hs]).
Time (pose proof (step_Permutation _ _ _ _ _ _ Heq Hs)).
Time firstorder.
Time Qed.
Time
Record pure_step (e1 e2 : expr \206\155) :={pure_step_safe :
                                      forall \207\1311, reducible_no_obs e1 \207\1311;
                                     pure_step_det :
                                      forall \207\1311 \206\186 e2' \207\1312 efs,
                                      prim_step e1 \207\1311 \206\186 e2' \207\1312 efs
                                      \226\134\146 \206\186 = []
                                        \226\136\167 \207\1312 = \207\1311 \226\136\167 e2' = e2 \226\136\167 efs = []}.
Time
Class PureExec (\207\134 : Prop) (n : nat) (e1 e2 : expr \206\155) :=
    pure_exec : \207\134 \226\134\146 relations.nsteps pure_step n e1 e2.
Time
Lemma pure_step_ctx K `{!@LanguageCtx \206\155 K} e1 e2 :
  pure_step e1 e2 \226\134\146 pure_step (K e1) (K e2).
Time Proof.
Time (intros [Hred Hstep]).
Time split.
Time -
Time (unfold reducible_no_obs in *).
Time naive_solver eauto using fill_step.
Time -
Time (intros \207\1311 \206\186 e2' \207\1312 efs Hpstep).
Time
(destruct (fill_step_inv e1 \207\1311 \206\186 e2' \207\1312 efs) as (e2'', (->, ?));
  [  | exact Hpstep |  ]).
Time +
Time (destruct (Hred \207\1311) as (?, (?, (?, ?))); eauto using val_stuck).
Time +
Time (edestruct (Hstep \207\1311 \206\186 e2'' \207\1312 efs) as (?, (->, (->, ->))); auto).
Time Qed.
Time From iris.base_logic Require Import base_logic.
Time Set Default Proof Using "Type".
Time Inductive counting :=
       | Count : forall z : Z, _
       | CountBot : _.
Time #[local]Open Scope Z.
Time
Instance counting_valid : (Valid counting) :=
 (\206\187 x, match x with
       | Count _ => True
       | CountBot => False
       end).
Time
Instance counting_validN : (ValidN counting) :=
 (\206\187 n x, match x with
         | Count _ => True
         | CountBot => False
         end).
Time Instance counting_pcore : (PCore counting) := (\206\187 x, None).
Time
Lemma pure_step_nsteps_ctx K `{!@LanguageCtx \206\155 K} 
  n e1 e2 :
  relations.nsteps pure_step n e1 e2
  \226\134\146 relations.nsteps pure_step n (K e1) (K e2).
Time Proof.
Time (induction 1; econstructor; eauto using pure_step_ctx).
Time
Instance counting_op : (Op counting) :=
 (\206\187 x y,
    match x, y with
    | Count z1, Count z2 =>
        if decide (z1 >= 0 \226\136\167 z2 >= 0) then CountBot
        else if decide ((z1 >= 0 \226\136\168 z2 >= 0) \226\136\167 z1 + z2 < 0) then CountBot
             else Count (z1 + z2)
    | _, _ => CountBot
    end).
Time Qed.
Time
Lemma pure_exec_ctx K `{!@LanguageCtx \206\155 K} \207\134 n e1 
  e2 : PureExec \207\134 n e1 e2 \226\134\146 PureExec \207\134 n (K e1) (K e2).
Time Proof.
Time Canonical Structure countingC := leibnizC counting.
Time #[local]
Ltac
 by_cases :=
  repeat <ssreflect_plugin::ssrtclintros@0>
   match goal with
   | H:counting |- _ => destruct H
   end =>//=; repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=;
   try lia.
Time (rewrite /PureExec; eauto using pure_step_nsteps_ctx).
Time Qed.
Time Class IntoVal (e : expr \206\155) (v : val \206\155) :=
         into_val : of_val v = e.
Time Lemma counting_ra_mixin : RAMixin counting.
Time Proof.
Time (split; try apply _; try done).
Time Class AsVal (e : expr \206\155) :=
         as_val : \226\136\131 v, of_val v = e.
Time #[global]Instance as_vals_of_val  vs: (TCForall AsVal (of_val <$> vs)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply TCForall_Forall, Forall_fmap, Forall_true =>v).
Time (rewrite /AsVal /=; eauto).
Time Qed.
Time Lemma as_val_is_Some e : (\226\136\131 v, of_val v = e) \226\134\146 is_Some (to_val e).
Time Proof.
Time (intros [v <-]).
Time rewrite to_of_val.
Time eauto.
Time Qed.
Time End language.
Time From iris.algebra Require Import local_updates.
Time -
Time (intros x y z).
Time rewrite /op /counting_op.
Time by_cases.
Time Set Default Proof Using "Type".
Time #[local]Arguments pcore _ _ !_ /.
Time #[local]Arguments cmra_pcore _ !_ /.
Time #[local]Arguments validN _ _ _ !_ /.
Time #[local]Arguments valid _ _ !_ /.
Time #[local]Arguments cmra_validN _ _ !_ /.
Time #[local]Arguments cmra_valid _ !_ /.
Time
Inductive csum (A B : Type) :=
  | Cinl : A \226\134\146 csum A B
  | Cinr : B \226\134\146 csum A B
  | CsumBot : csum A B.
Time Arguments Cinl {_} {_} _.
Time Arguments Cinr {_} {_} _.
Time Arguments CsumBot {_} {_}.
Time Instance: (Params (@Cinl) 2) := { }.
Time Instance: (Params (@Cinr) 2) := { }.
Time Instance: (Params (@CsumBot) 2) := { }.
Time
Instance maybe_Cinl  {A} {B}: (Maybe (@Cinl A B)) :=
 (\206\187 x, match x with
       | Cinl a => Some a
       | _ => None
       end).
Time
Instance maybe_Cinr  {A} {B}: (Maybe (@Cinr A B)) :=
 (\206\187 x, match x with
       | Cinr b => Some b
       | _ => None
       end).
Time Section cofe.
Time Context {A B : ofeT}.
Time Implicit Type a : A.
Time Implicit Type b : B.
Time
Inductive csum_equiv : Equiv (csum A B) :=
  | Cinl_equiv : forall a a', a \226\137\161 a' \226\134\146 Cinl a \226\137\161 Cinl a'
  | Cinr_equiv : forall b b', b \226\137\161 b' \226\134\146 Cinr b \226\137\161 Cinr b'
  | CsumBot_equiv : CsumBot \226\137\161 CsumBot.
Time Existing Instance csum_equiv.
Time
Inductive csum_dist : Dist (csum A B) :=
  | Cinl_dist : forall n a a', a \226\137\161{n}\226\137\161 a' \226\134\146 Cinl a \226\137\161{n}\226\137\161 Cinl a'
  | Cinr_dist : forall n b b', b \226\137\161{n}\226\137\161 b' \226\134\146 Cinr b \226\137\161{n}\226\137\161 Cinr b'
  | CsumBot_dist : forall n, CsumBot \226\137\161{n}\226\137\161 CsumBot.
Time Existing Instance csum_dist.
Time #[global]Instance Cinl_ne : (NonExpansive (@Cinl A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinl_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@Cinl A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinl_inj : (Inj (\226\137\161) (\226\137\161) (@Cinl A B)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time #[global]Instance Cinl_inj_dist  n: (Inj (dist n) (dist n) (@Cinl A B)).
Time Proof.
Time by inversion_clear 1.
Time From stdpp Require Import namespaces.
Time From iris.algebra Require Import updates.
Time From iris.algebra Require Import proofmode_classes.
Time Qed.
Time #[global]Instance Cinr_ne : (NonExpansive (@Cinr A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinr_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@Cinr A B)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Cinr_inj : (Inj (\226\137\161) (\226\137\161) (@Cinr A B)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time Set Default Proof Using "Type".
Time
Record namespace_map (A : Type) :=
 NamespaceMap {namespace_map_data_proj : gmap positive A;
               namespace_map_token_proj : coPset_disj}.
Time #[global]Instance Cinr_inj_dist  n: (Inj (dist n) (dist n) (@Cinr A B)).
Time Proof.
Time by inversion_clear 1.
Time Add Printing Constructor namespace_map.
Time Arguments NamespaceMap {_} _ _.
Time Arguments namespace_map_data_proj {_} _.
Time Arguments namespace_map_token_proj {_} _.
Time Instance: (Params (@NamespaceMap) 1) := { }.
Time Instance: (Params (@namespace_map_data_proj) 1) := { }.
Time Instance: (Params (@namespace_map_token_proj) 1) := { }.
Time
Definition namespace_map_data {A : cmraT} (N : namespace) 
  (a : A) : namespace_map A := NamespaceMap {[positives_flatten N := a]} \206\181.
Time
Definition namespace_map_token {A : cmraT} (E : coPset) : 
  namespace_map A := NamespaceMap \226\136\133 (CoPset E).
Time Qed.
Time Definition csum_ofe_mixin : OfeMixin (csum A B).
Time Proof.
Time split.
Time -
Time (intros mx my; split).
Time +
Time by destruct 1; constructor; try apply equiv_dist.
Time Instance: (Params (@namespace_map_data) 2) := { }.
Time Section ofe.
Time Context {A : ofeT}.
Time Implicit Types x y : namespace_map A.
Time
Instance namespace_map_equiv : (Equiv (namespace_map A)) :=
 (\206\187 x y,
    namespace_map_data_proj x \226\137\161 namespace_map_data_proj y
    \226\136\167 namespace_map_token_proj x = namespace_map_token_proj y).
Time
Instance namespace_map_dist : (Dist (namespace_map A)) :=
 (\206\187 n x y,
    namespace_map_data_proj x \226\137\161{n}\226\137\161 namespace_map_data_proj y
    \226\136\167 namespace_map_token_proj x = namespace_map_token_proj y).
Time #[global]Instance Awesome_ne : (NonExpansive2 (@NamespaceMap A)).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance Awesome_proper : (Proper ((\226\137\161) ==> (=) ==> (\226\137\161)) (@NamespaceMap A)).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance namespace_map_data_proj_ne :
 (NonExpansive (@namespace_map_data_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time #[global]
Instance namespace_map_data_proj_proper :
 (Proper ((\226\137\161) ==> (\226\137\161)) (@namespace_map_data_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time Definition namespace_map_ofe_mixin : OfeMixin (namespace_map A).
Time Proof.
Time
by
 apply
  (iso_ofe_mixin
     (\206\187 x, (namespace_map_data_proj x, namespace_map_token_proj x))).
Time +
Time
(intros Hxy; feed inversion Hxy 0; subst; constructor; try done;
  <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n; by feed inversion
  Hxy n).
Time Qed.
Time
Canonical Structure namespace_mapC :=
  OfeT (namespace_map A) namespace_map_ofe_mixin.
Time #[global]
Instance NamespaceMap_discrete  a b:
 (Discrete a \226\134\146 Discrete b \226\134\146 Discrete (NamespaceMap a b)).
Time Proof.
Time (intros ? ? [? ?] [? ?]; split; unfold_leibniz; by eapply discrete).
Time Qed.
Time #[global]
Instance namespace_map_ofe_discrete :
 (OfeDiscrete A \226\134\146 OfeDiscrete namespace_mapC).
Time Proof.
Time (intros ? [? ?]; apply _).
Time Qed.
Time End ofe.
Time -
Time (intros n; split).
Time +
Time by intros [| a| ]; constructor.
Time +
Time by destruct 1; constructor.
Time Arguments namespace_mapC : clear implicits.
Time Section cmra.
Time Context {A : cmraT}.
Time Implicit Types a b : A.
Time Implicit Types x y : namespace_map A.
Time #[global]
Instance namespace_map_data_ne  i: (NonExpansive (@namespace_map_data A i)).
Time +
Time (destruct 1; inversion_clear 1; constructor; etrans; eauto).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance namespace_map_data_proper  N:
 (Proper ((\226\137\161) ==> (\226\137\161)) (@namespace_map_data A N)).
Time Proof.
Time solve_proper.
Time Qed.
Time -
Time by inversion_clear 1; constructor; apply dist_S.
Time #[global]
Instance namespace_map_data_discrete  N a:
 (Discrete a \226\134\146 Discrete (namespace_map_data N a)).
Time Proof.
Time (intros).
Time (apply NamespaceMap_discrete; apply _).
Time Qed.
Time #[global]
Instance namespace_map_token_discrete  E:
 (Discrete (@namespace_map_token A E)).
Time Proof.
Time (intros).
Time (apply NamespaceMap_discrete; apply _).
Time Qed.
Time
Instance namespace_map_valid : (Valid (namespace_map A)) :=
 (\206\187 x,
    match namespace_map_token_proj x with
    | CoPset E =>
        \226\156\147 namespace_map_data_proj x
        \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
    | CoPsetBot => False
    end).
Time #[global]Arguments namespace_map_valid !_ /.
Time
Instance namespace_map_validN : (ValidN (namespace_map A)) :=
 (\206\187 n x,
    match namespace_map_token_proj x with
    | CoPset E =>
        \226\156\147{n} namespace_map_data_proj x
        \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
    | CoPsetBot => False
    end).
Time #[global]Arguments namespace_map_validN !_ /.
Time
Instance namespace_map_pcore : (PCore (namespace_map A)) :=
 (\206\187 x, Some (NamespaceMap (core (namespace_map_data_proj x)) \206\181)).
Time
Instance namespace_map_op : (Op (namespace_map A)) :=
 (\206\187 x y,
    NamespaceMap (namespace_map_data_proj x \226\139\133 namespace_map_data_proj y)
      (namespace_map_token_proj x \226\139\133 namespace_map_token_proj y)).
Time
Definition namespace_map_valid_eq :
  valid =
  (\206\187 x,
     match namespace_map_token_proj x with
     | CoPset E =>
         \226\156\147 namespace_map_data_proj x
         \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
     | CoPsetBot => False
     end) := eq_refl _.
Time Qed.
Time
Definition namespace_map_validN_eq :
  validN =
  (\206\187 n x,
     match namespace_map_token_proj x with
     | CoPset E =>
         \226\156\147{n} namespace_map_data_proj x
         \226\136\167 (\226\136\128 i, namespace_map_data_proj x !! i = None \226\136\168 i \226\136\137 E)
     | CoPsetBot => False
     end) := eq_refl _.
Time
Lemma namespace_map_included x y :
  x \226\137\188 y
  \226\134\148 namespace_map_data_proj x \226\137\188 namespace_map_data_proj y
    \226\136\167 namespace_map_token_proj x \226\137\188 namespace_map_token_proj y.
Time Proof.
Time
(split;
  [ intros [[z1 z2] Hz]; split; [ exists z1 | exists z2 ]; apply Hz |  ]).
Time (intros [[z1 Hz1] [z2 Hz2]]; exists (NamespaceMap z1 z2); split; auto).
Time Canonical Structure csumC : ofeT := OfeT (csum A B) csum_ofe_mixin.
Time #[program]
Definition csum_chain_l (c : chain csumC) (a : A) : 
  chain A :=
  {| chain_car := fun n => match c n with
                           | Cinl a' => a'
                           | _ => a
                           end |}.
Time Next Obligation.
Time (intros c a n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time Qed.
Time
Lemma namespace_map_data_proj_validN n x :
  \226\156\147{n} x \226\134\146 \226\156\147{n} namespace_map_data_proj x.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> destruct x as [? [?| ]] =>// - [? ?].
Time Qed.
Time #[program]
Definition csum_chain_r (c : chain csumC) (b : B) : 
  chain B :=
  {| chain_car := fun n => match c n with
                           | Cinr b' => b'
                           | _ => b
                           end |}.
Time Next Obligation.
Time (intros c b n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time Qed.
Time
Definition csum_compl `{Cofe A} `{Cofe B} : Compl csumC :=
  \206\187 c,
    match c 0 with
    | Cinl a => Cinl (compl (csum_chain_l c a))
    | Cinr b => Cinr (compl (csum_chain_r c b))
    | CsumBot => CsumBot
    end.
Time Qed.
Time
Lemma namespace_map_token_proj_validN n x :
  \226\156\147{n} x \226\134\146 \226\156\147{n} namespace_map_token_proj x.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> destruct x as [? [?| ]] =>// - [? ?].
Time Qed.
Time #[global, program]
Instance csum_cofe  `{Cofe A} `{Cofe B}: (Cofe csumC) :=
 {| compl := csum_compl |}.
Time Next Obligation.
Time (intros ? ? n c; rewrite /compl /csum_compl).
Time
(<ssreflect_plugin::ssrtclseq@0> feed inversion chain_cauchy c 0 n ; first 
  auto with lia; constructor).
Time Lemma namespace_map_cmra_mixin : CmraMixin (namespace_map A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
Time +
Time rewrite (conv_compl n (csum_chain_l c a')) /=.
Time (destruct (c n); naive_solver).
Time +
Time rewrite (conv_compl n (csum_chain_r c b')) /=.
Time (destruct (c n); naive_solver).
Time -
Time solve_proper.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> intros n [m1 [E1| ]] [m2 [E2| ]] [Hm ?]
  =>// - [? ?]; split; simplify_eq /=).
Time Qed.
Time #[global]
Instance csum_ofe_discrete :
 (OfeDiscrete A \226\134\146 OfeDiscrete B \226\134\146 OfeDiscrete csumC).
Time Proof.
Time by inversion_clear 3; constructor; apply (discrete _).
Time Qed.
Time #[global]
Instance csum_leibniz :
 (LeibnizEquiv A \226\134\146 LeibnizEquiv B \226\134\146 LeibnizEquiv csumC).
Time Proof.
Time by destruct 3; f_equal; apply leibniz_equiv.
Time Qed.
Time #[global]Instance Cinl_discrete  a: (Discrete a \226\134\146 Discrete (Cinl a)).
Time Proof.
Time by inversion_clear 2; constructor; apply (discrete _).
Time +
Time by rewrite -Hm.
Time Qed.
Time #[global]Instance Cinr_discrete  b: (Discrete b \226\134\146 Discrete (Cinr b)).
Time Proof.
Time by inversion_clear 2; constructor; apply (discrete _).
Time Qed.
Time End cofe.
Time Arguments csumC : clear implicits.
Time
Definition csum_map {A} {A'} {B} {B'} (fA : A \226\134\146 A') 
  (fB : B \226\134\146 B') (x : csum A B) : csum A' B' :=
  match x with
  | Cinl a => Cinl (fA a)
  | Cinr b => Cinr (fB b)
  | CsumBot => CsumBot
  end.
Time Instance: (Params (@csum_map) 4) := { }.
Time Lemma csum_map_id {A} {B} (x : csum A B) : csum_map id id x = x.
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma csum_map_compose {A} {A'} {A''} {B} {B'} {B''} 
  (f : A \226\134\146 A') (f' : A' \226\134\146 A'') (g : B \226\134\146 B') (g' : B' \226\134\146 B'') 
  (x : csum A B) :
  csum_map (f' \226\136\152 f) (g' \226\136\152 g) x = csum_map f' g' (csum_map f g x).
Time Proof.
Time by destruct x.
Time Qed.
Time +
Time (intros i).
Time by rewrite -(dist_None n) -Hm dist_None.
Time
Lemma csum_map_ext {A A' B B' : ofeT} (f f' : A \226\134\146 A') 
  (g g' : B \226\134\146 B') x :
  (\226\136\128 x, f x \226\137\161 f' x) \226\134\146 (\226\136\128 x, g x \226\137\161 g' x) \226\134\146 csum_map f g x \226\137\161 csum_map f' g' x.
Time Proof.
Time by destruct x; constructor.
Time Qed.
Time
Instance csum_map_cmra_ne  {A A' B B' : ofeT} n:
 (Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n)
    (@csum_map A A' B B')).
Time Proof.
Time
(intros f f' Hf g g' Hg []; destruct 1; constructor; by apply Hf || apply Hg).
Time Qed.
Time
Definition csumC_map {A} {A'} {B} {B'} (f : A -n> A') 
  (g : B -n> B') : csumC A B -n> csumC A' B' := CofeMor (csum_map f g).
Time -
Time
(intros [m [E| ]]; rewrite namespace_map_valid_eq namespace_map_validN_eq /=
  ?cmra_valid_validN; naive_solver eauto using 0).
Time -
Time
(intros n [m [E| ]]; rewrite namespace_map_validN_eq /=; naive_solver eauto
  using cmra_validN_S).
Time -
Time (split; simpl; [ by rewrite assoc | by rewrite assoc_L ]).
Time -
Time (split; simpl; [ by rewrite comm | by rewrite comm_L ]).
Time -
Time (split; simpl; [ by rewrite cmra_core_l | by rewrite left_id_L ]).
Time
Instance csumC_map_ne  A A' B B': (NonExpansive2 (@csumC_map A A' B B')).
Time Proof.
Time by intros n f f' Hf g g' Hg []; constructor.
Time -
Time (split; simpl; [ by rewrite cmra_core_idemp | done ]).
Time Qed.
Time Section cmra.
Time Context {A B : cmraT}.
Time Implicit Type a : A.
Time Implicit Type b : B.
Time
Instance csum_valid : (Valid (csum A B)) :=
 (\206\187 x, match x with
       | Cinl a => \226\156\147 a
       | Cinr b => \226\156\147 b
       | CsumBot => False
       end).
Time
Instance csum_validN : (ValidN (csum A B)) :=
 (\206\187 n x,
    match x with
    | Cinl a => \226\156\147{n} a
    | Cinr b => \226\156\147{n} b
    | CsumBot => False
    end).
Time
Instance csum_pcore : (PCore (csum A B)) :=
 (\206\187 x,
    match x with
    | Cinl a => Cinl <$> pcore a
    | Cinr b => Cinr <$> pcore b
    | CsumBot => Some CsumBot
    end).
Time
Instance csum_op : (Op (csum A B)) :=
 (\206\187 x y,
    match x, y with
    | Cinl a, Cinl a' => Cinl (a \226\139\133 a')
    | Cinr b, Cinr b' => Cinr (b \226\139\133 b')
    | _, _ => CsumBot
    end).
Time Lemma Cinl_op a a' : Cinl a \226\139\133 Cinl a' = Cinl (a \226\139\133 a').
Time Proof.
Time done.
Time Qed.
Time Lemma Cinr_op b b' : Cinr b \226\139\133 Cinr b' = Cinr (b \226\139\133 b').
Time Proof.
Time done.
Time -
Time (intros ? ?; rewrite !namespace_map_included; intros [? ?]).
Time Qed.
Time
Lemma csum_included x y :
  x \226\137\188 y
  \226\134\148 y = CsumBot
    \226\136\168 (\226\136\131 a a', x = Cinl a \226\136\167 y = Cinl a' \226\136\167 a \226\137\188 a')
      \226\136\168 (\226\136\131 b b', x = Cinr b \226\136\167 y = Cinr b' \226\136\167 b \226\137\188 b').
Time Proof.
Time split.
Time -
Time (unfold included).
Time
(intros [[a'| b'| ] Hy]; destruct x as [a| b| ]; inversion_clear Hy; eauto 
  10).
Time by split; simpl; apply : {}cmra_core_mono {}.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> intros n [m1 [E1| ]] [m2 [E2| ]] =>//=;
  rewrite namespace_map_validN_eq /=).
Time rewrite {+1}/op /cmra_op /=.
Time (<ssreflect_plugin::ssrtclseq@0> case_decide ; last  done).
Time
(<ssreflect_plugin::ssrtclseq@0> intros [Hm Hdisj]; split ; first  by eauto
 using cmra_validN_op_l).
Time (intros i).
Time move : {}(Hdisj i) {}.
Time rewrite lookup_op.
Time
(<ssreflect_plugin::ssrtclseq@0> case : {}(m1 !! i) {} =>[a|] ; last  auto).
Time move  {}=>[].
Time by case : {}(m2 !! i) {}.
Time set_solver.
Time -
Time (intros n x y1 y2 ? [? ?]; simpl in *).
Time
(destruct
  (cmra_extend n (namespace_map_data_proj x) (namespace_map_data_proj y1)
     (namespace_map_data_proj y2)) as (m1, (m2, (?, (?, ?)))); auto
  using namespace_map_data_proj_validN).
Time
(destruct
  (cmra_extend n (namespace_map_token_proj x) (namespace_map_token_proj y1)
     (namespace_map_token_proj y2)) as (E1, (E2, (?, (?, ?)))); auto
  using namespace_map_token_proj_validN).
Time by exists (NamespaceMap m1 E1),(NamespaceMap m2 E2).
Time -
Time
(intros [->| [(a, (a', (->, (->, (c, ?)))))| (b, (b', (->, (->, (c, ?)))))]]).
Time +
Time (destruct x; exists CsumBot; constructor).
Time +
Time (exists (Cinl c); by constructor).
Time +
Time (exists (Cinr c); by constructor).
Time Qed.
Time Qed.
Time
Lemma csum_includedN n x y :
  x \226\137\188{n} y
  \226\134\148 y = CsumBot
    \226\136\168 (\226\136\131 a a', x = Cinl a \226\136\167 y = Cinl a' \226\136\167 a \226\137\188{n} a')
      \226\136\168 (\226\136\131 b b', x = Cinr b \226\136\167 y = Cinr b' \226\136\167 b \226\137\188{n} b').
Time Proof.
Time split.
Time -
Time (unfold includedN).
Time
(intros [[a'| b'| ] Hy]; destruct x as [a| b| ]; inversion_clear Hy; eauto 
  10).
Time
Canonical Structure namespace_mapR :=
  CmraT (namespace_map A) namespace_map_cmra_mixin.
Time #[global]
Instance namespace_map_cmra_discrete :
 (CmraDiscrete A \226\134\146 CmraDiscrete namespace_mapR).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time
(intros [m [E| ]]; rewrite namespace_map_validN_eq namespace_map_valid_eq //=).
Time naive_solver eauto using (cmra_discrete_valid m).
Time Qed.
Time
Instance namespace_map_empty : (Unit (namespace_map A)) := (NamespaceMap \206\181 \206\181).
Time Lemma namespace_map_ucmra_mixin : UcmraMixin (namespace_map A).
Time Proof.
Time (split; simpl).
Time -
Time rewrite namespace_map_valid_eq /=.
Time split.
Time (apply ucmra_unit_valid).
Time set_solver.
Time -
Time (split; simpl; [ by rewrite left_id | by rewrite left_id_L ]).
Time f_equal.
Time lia.
Time -
Time (do 2 constructor; [ apply (core_id_core _) | done ]).
Time Qed.
Time
Canonical Structure namespace_mapUR :=
  UcmraT (namespace_map A) namespace_map_ucmra_mixin.
Time #[global]
Instance namespace_map_data_core_id  N a:
 (CoreId a \226\134\146 CoreId (namespace_map_data N a)).
Time Proof.
Time (do 2 constructor; simpl; auto).
Time -
Time (intros x y).
Time rewrite /op /counting_op.
Time (apply core_id_core, _).
Time by_cases.
Time Qed.
Time Lemma namespace_map_data_valid N a : \226\156\147 namespace_map_data N a \226\134\148 \226\156\147 a.
Time Proof.
Time rewrite namespace_map_valid_eq /= singleton_valid.
Time set_solver.
Time Qed.
Time Lemma namespace_map_token_valid E : \226\156\147 namespace_map_token E.
Time Proof.
Time rewrite namespace_map_valid_eq /=.
Time split.
Time done.
Time by left.
Time Qed.
Time
Lemma namespace_map_data_op N a b :
  namespace_map_data N (a \226\139\133 b) =
  namespace_map_data N a \226\139\133 namespace_map_data N b.
Time Proof.
Time
by rewrite {+2}/op /namespace_map_op /namespace_map_data /= -op_singleton
 left_id_L.
Time Qed.
Time
Lemma namespace_map_data_mono N a b :
  a \226\137\188 b \226\134\146 namespace_map_data N a \226\137\188 namespace_map_data N b.
Time Proof.
Time (intros [c ->]).
Time rewrite namespace_map_data_op.
Time (apply cmra_included_l).
Time Qed.
Time #[global]
Instance is_op_namespace_map_data  N a b1 b2:
 (IsOp a b1 b2
  \226\134\146 IsOp' (namespace_map_data N a) (namespace_map_data N b1)
      (namespace_map_data N b2)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp =>{+}->).
Time by rewrite namespace_map_data_op.
Time Qed.
Time
Lemma namespace_map_token_union E1 E2 :
  E1 ## E2
  \226\134\146 namespace_map_token (E1 \226\136\170 E2) =
    namespace_map_token E1 \226\139\133 namespace_map_token E2.
Time Proof.
Time (intros).
Time
by rewrite /op /namespace_map_op /namespace_map_token /= coPset_disj_union //
 left_id_L.
Time -
Time
(intros [->| [(a, (a', (->, (->, (c, ?)))))| (b, (b', (->, (->, (c, ?)))))]]).
Time +
Time (destruct x; exists CsumBot; constructor).
Time Qed.
Time
Lemma namespace_map_token_difference E1 E2 :
  E1 \226\138\134 E2
  \226\134\146 namespace_map_token E2 =
    namespace_map_token E1 \226\139\133 namespace_map_token (E2 \226\136\150 E1).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -namespace_map_token_union ; last 
 set_solver).
Time +
Time (exists (Cinl c); by constructor).
Time +
Time (exists (Cinr c); by constructor).
Time Qed.
Time by rewrite -union_difference_L.
Time Qed.
Time
Lemma namespace_map_token_valid_op E1 E2 :
  \226\156\147 (namespace_map_token E1 \226\139\133 namespace_map_token E2) \226\134\148 E1 ## E2.
Time Proof.
Time rewrite namespace_map_valid_eq /= {+1}/op /cmra_op /=.
Time (<ssreflect_plugin::ssrtclseq@0> case_decide ; last  done).
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op /valid.
Time by_cases.
Time Lemma csum_cmra_mixin : CmraMixin (csum A B).
Time Proof.
Time split.
Time -
Time (intros [] n; destruct 1; constructor; by ofe_subst).
Time Qed.
Time (split; [ done |  ]; intros _).
Time split.
Time -
Time by rewrite left_id.
Time -
Time (intros i).
Time rewrite lookup_op lookup_empty.
Time auto.
Time Qed.
Time -
Time (intros ? ? ? ? [n a a' Ha| n b b' Hb| n] [=]; subst; eauto).
Time
Lemma namespace_map_alloc_update E N a :
  \226\134\145N \226\138\134 E \226\134\146 \226\156\147 a \226\134\146 namespace_map_token E ~~> namespace_map_data N a.
Time Proof.
Time (assert (positives_flatten N \226\136\136 (\226\134\145N : coPset))).
Time {
Time rewrite nclose_eq.
Time (apply elem_coPset_suffixes).
Time exists 1%positive.
Time by rewrite left_id_L.
Time }
Time (intros ? ?).
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_total_update =>n 
 [mf [Ef|]] //).
Time rewrite namespace_map_validN_eq /= {+1}/op /cmra_op /=.
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time (<ssreflect_plugin::ssrtclseq@0> case_decide ; last  done).
Time rewrite left_id_L {+1}left_id.
Time Canonical Structure countingR := discreteR counting counting_ra_mixin.
Time #[global]Instance counting_cmra_discrete : (CmraDiscrete countingR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma counting_op' (x y : countingR) : x \226\139\133 y = counting_op x y.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_valid' (x : countingR) : \226\156\147 x \226\134\148 counting_valid x.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_validN' n (x : countingR) : \226\156\147{n} x \226\134\148 counting_validN n x.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance is_op_counting  z:
 (z >= 0 \226\134\146 IsOp' (Count z) (Count (z + 1)) (Count (- 1))).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp counting_op' =>?).
Time rewrite //=.
Time by_cases.
Time (intros [Hmf Hdisj]; split).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (Hdisj (positives_flatten N)) as [Hmfi| ] ; last  set_solver).
Time (destruct (cmra_pcore_ne n a a' ca) as (ca', (->, ?)); auto).
Time (exists (Cinl ca'); by repeat constructor).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time f_equal.
Time lia.
Time Qed.
Time #[global]
Instance is_op_counting'  (n : nat):
 (IsOp' (Count n) (Count (S n)) (Count (- 1))).
Time Proof.
Time rewrite /IsOp' /IsOp counting_op' //=.
Time (destruct (cmra_pcore_ne n b b' cb) as (cb', (->, ?)); auto).
Time (exists (Cinr cb'); by repeat constructor).
Time -
Time (intros ? [a| b| ] [a'| b'| ] H; inversion_clear H; ofe_subst; done).
Time by_cases.
Time move : {}Hmfi {}.
Time f_equal.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_op lookup_empty left_id_L
 =>Hmfi).
Time lia.
Time (intros j).
Time rewrite lookup_op.
Time Qed.
Time (destruct (decide (positives_flatten N = j)) as [<-| ]).
Time #[global]Instance counting_id_free  (z : counting): (IdFree z).
Time Proof.
Time (intros y).
Time rewrite counting_op' counting_validN'.
Time +
Time rewrite Hmfi lookup_singleton right_id_L.
Time by_cases.
Time by apply cmra_valid_validN.
Time +
Time by rewrite lookup_singleton_ne // left_id_L.
Time (destruct y; by_cases; intros _; inversion 1).
Time -
Time (intros j).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide (positives_flatten N = j))
 ; first  set_solver).
Time -
Time
(intros [a| b| ]; rewrite /= ?cmra_valid_validN; naive_solver eauto using O).
Time lia.
Time Qed.
Time #[global]Instance counting_full_exclusive : (Exclusive (Count 0)).
Time Proof.
Time (intros y).
Time rewrite counting_validN' counting_op'.
Time -
Time (intros n [a| b| ]; simpl; auto using cmra_validN_S).
Time -
Time
(intros [a1| b1| ] [a2| b2| ] [a3| b3| ]; constructor; by rewrite ?assoc).
Time (<ssreflect_plugin::ssrtclintros@0> destruct y =>//=; by_cases).
Time Qed.
Time -
Time (intros [a1| b1| ] [a2| b2| ]; constructor; by rewrite 1?comm).
Time -
Time (intros [a| b| ] ? [=]; subst; auto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time (constructor; eauto using cmra_pcore_l).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time (constructor; eauto using cmra_pcore_l).
Time -
Time (intros [a| b| ] ? [=]; subst; auto).
Time +
Time rewrite lookup_op lookup_singleton_ne //.
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (Hdisj j) as [Hmfi| ?] ; last 
 set_solver).
Time (feed inversion cmra_pcore_idemp a ca; repeat constructor; auto).
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time (feed inversion cmra_pcore_idemp b cb; repeat constructor; auto).
Time -
Time
(intros x y ?
  [->| [(a, (a', (->, (->, ?))))| (b, (b', (->, (->, ?))))]]%csum_included
  [=]).
Time +
Time exists CsumBot.
Time (rewrite csum_included; eauto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; simplify_option_eq).
Time (destruct (cmra_pcore_mono a a' ca) as (ca', (->, ?)); auto).
Time exists (Cinl ca').
Time (rewrite csum_included; eauto  10).
Time move : {}Hmfi {}.
Time (rewrite lookup_op lookup_empty; auto).
Time Qed.
Time +
Time (destruct (pcore b) as [cb| ] eqn:?; simplify_option_eq).
Time
Lemma namespace_map_updateP P (Q : namespace_map A \226\134\146 Prop) 
  N a :
  a ~~>: P
  \226\134\146 (\226\136\128 a', P a' \226\134\146 Q (namespace_map_data N a'))
    \226\134\146 namespace_map_data N a ~~>: Q.
Time Proof.
Time (intros Hup HP).
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_total_updateP =>n 
 [mf [Ef|]] //).
Time rewrite namespace_map_validN_eq /= left_id_L.
Time (intros [Hmf Hdisj]).
Time (destruct (Hup n (mf !! positives_flatten N)) as (a', (?, ?))).
Time {
Time move : {}(Hmf (positives_flatten N)) {}.
Time by rewrite lookup_op lookup_singleton Some_op_opM.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (namespace_map_data N a'); split ;
 first  by eauto).
Time rewrite /= left_id_L.
Time (destruct (cmra_pcore_mono b b' cb) as (cb', (->, ?)); auto).
Time exists (Cinr cb').
Time (rewrite csum_included; eauto  10).
Time split.
Time -
Time (intros j).
Time (destruct (decide (positives_flatten N = j)) as [<-| ]).
Time +
Time by rewrite lookup_op lookup_singleton Some_op_opM.
Time +
Time rewrite lookup_op lookup_singleton_ne // left_id_L.
Time -
Time
(intros n [a1| b1| ] [a2| b2| ]; simpl; eauto using cmra_validN_op_l; done).
Time move : {}(Hmf j) {}.
Time rewrite lookup_op.
Time eauto using cmra_validN_op_r.
Time -
Time (intros j).
Time move : {}(Hdisj j) {}.
Time rewrite !lookup_op !op_None !lookup_singleton_None.
Time -
Time (intros n [a| b| ] y1 y2 Hx Hx').
Time +
Time
(destruct y1 as [a1| b1| ], y2 as [a2| b2| ]; try by exfalso; inversion Hx').
Time
(destruct (cmra_extend n a a1 a2) as (z1, (z2, (?, (?, ?))));
  [ done | apply (inj Cinl), Hx' |  ]).
Time exists (Cinl z1),(Cinl z2).
Time by repeat constructor.
Time +
Time
(destruct y1 as [a1| b1| ], y2 as [a2| b2| ]; try by exfalso; inversion Hx').
Time naive_solver.
Time Qed.
Time
Lemma namespace_map_update N a b :
  a ~~> b \226\134\146 namespace_map_data N a ~~> namespace_map_data N b.
Time Proof.
Time rewrite !cmra_update_updateP.
Time eauto using namespace_map_updateP with subst.
Time Qed.
Time End cmra.
Time
(destruct (cmra_extend n b b1 b2) as (z1, (z2, (?, (?, ?))));
  [ done | apply (inj Cinr), Hx' |  ]).
Time exists (Cinr z1),(Cinr z2).
Time by repeat constructor.
Time +
Time by exists CsumBot,CsumBot; destruct y1, y2; inversion_clear Hx'.
Time Arguments namespace_mapR : clear implicits.
Time Arguments namespace_mapUR : clear implicits.
Time Qed.
Time Canonical Structure csumR := CmraT (csum A B) csum_cmra_mixin.
Time #[global]
Instance csum_cmra_discrete :
 (CmraDiscrete A \226\134\146 CmraDiscrete B \226\134\146 CmraDiscrete csumR).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time by move  {}=>[a|b|] HH /=; try apply cmra_discrete_valid.
Time Qed.
Time #[global]Instance Cinl_core_id  a: (CoreId a \226\134\146 CoreId (Cinl a)).
Time Proof.
Time rewrite /CoreId /=.
Time (inversion_clear 1; by repeat constructor).
Time Qed.
Time #[global]Instance Cinr_core_id  b: (CoreId b \226\134\146 CoreId (Cinr b)).
Time Proof.
Time rewrite /CoreId /=.
Time (inversion_clear 1; by repeat constructor).
Time Qed.
Time #[global]Instance Cinl_exclusive  a: (Exclusive a \226\134\146 Exclusive (Cinl a)).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> move  {}=>H [] ? =>[/H||].
Time Qed.
Time #[global]Instance Cinr_exclusive  b: (Exclusive b \226\134\146 Exclusive (Cinr b)).
Time Proof.
Time by <ssreflect_plugin::ssrtclintros@0> move  {}=>H [] ? =>[|/H|].
Time Qed.
Time #[global]
Instance Cinl_cancelable  a: (Cancelable a \226\134\146 Cancelable (Cinl a)).
Time Proof.
Time (move  {}=>? ? [y|y|] [z|z|] ? EQ //; inversion_clear EQ).
Time constructor.
Time by eapply (cancelableN a).
Time Qed.
Time #[global]
Instance Cinr_cancelable  b: (Cancelable b \226\134\146 Cancelable (Cinr b)).
Time Proof.
Time (move  {}=>? ? [y|y|] [z|z|] ? EQ //; inversion_clear EQ).
Time constructor.
Time by eapply (cancelableN b).
Time Qed.
Time #[global]Instance Cinl_id_free  a: (IdFree a \226\134\146 IdFree (Cinl a)).
Time Proof.
Time (intros ? [] ? EQ; inversion_clear EQ).
Time by eapply id_free0_r.
Time Qed.
Time #[global]Instance Cinr_id_free  b: (IdFree b \226\134\146 IdFree (Cinr b)).
Time Proof.
Time (intros ? [] ? EQ; inversion_clear EQ).
Time by eapply id_free0_r.
Time Qed.
Time
Lemma csum_equivI {M} (x y : csum A B) :
  x \226\137\161 y
  \226\138\163\226\138\162@{ uPredI M} match x, y with
                 | Cinl a, Cinl a' => a \226\137\161 a'
                 | Cinr b, Cinr b' => b \226\137\161 b'
                 | CsumBot, CsumBot => True
                 | _, _ => False
                 end.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> uPred.unseal; do 2 split ; first  by
 destruct 1).
Time by destruct x, y; try destruct 1; try constructor.
Time Qed.
Time
Lemma csum_validI {M} (x : csum A B) :
  \226\156\147 x
  \226\138\163\226\138\162@{ uPredI M} match x with
                 | Cinl a => \226\156\147 a
                 | Cinr b => \226\156\147 b
                 | CsumBot => False
                 end.
Time Proof.
Time uPred.unseal.
Time by destruct x.
Time Qed.
Time Lemma csum_update_l (a1 a2 : A) : a1 ~~> a2 \226\134\146 Cinl a1 ~~> Cinl a2.
Time Proof.
Time (intros Ha n [[a| b| ]| ] ?; simpl in *; auto).
Time -
Time by apply (Ha n (Some a)).
Time -
Time by apply (Ha n None).
Time Qed.
Time Lemma csum_update_r (b1 b2 : B) : b1 ~~> b2 \226\134\146 Cinr b1 ~~> Cinr b2.
Time Proof.
Time (intros Hb n [[a| b| ]| ] ?; simpl in *; auto).
Time -
Time by apply (Hb n (Some b)).
Time -
Time by apply (Hb n None).
Time Qed.
Time
Lemma csum_updateP_l (P : A \226\134\146 Prop) (Q : csum A B \226\134\146 Prop) 
  a : a ~~>: P \226\134\146 (\226\136\128 a', P a' \226\134\146 Q (Cinl a')) \226\134\146 Cinl a ~~>: Q.
Time Proof.
Time (intros Hx HP n mf Hm).
Time (destruct mf as [[a'| b'| ]| ]; try by destruct Hm).
Time -
Time (destruct (Hx n (Some a')) as (c, (?, ?)); naive_solver).
Time -
Time
(destruct (Hx n None) as (c, (?, ?)); naive_solver eauto
  using cmra_validN_op_l).
Time Qed.
Time
Lemma csum_updateP_r (P : B \226\134\146 Prop) (Q : csum A B \226\134\146 Prop) 
  b : b ~~>: P \226\134\146 (\226\136\128 b', P b' \226\134\146 Q (Cinr b')) \226\134\146 Cinr b ~~>: Q.
Time Proof.
Time (intros Hx HP n mf Hm).
Time (destruct mf as [[a'| b'| ]| ]; try by destruct Hm).
Time -
Time (destruct (Hx n (Some b')) as (c, (?, ?)); naive_solver).
Time -
Time
(destruct (Hx n None) as (c, (?, ?)); naive_solver eauto
  using cmra_validN_op_l).
Time Qed.
Time
Lemma csum_updateP'_l (P : A \226\134\146 Prop) a :
  a ~~>: P \226\134\146 Cinl a ~~>: (\206\187 m', \226\136\131 a', m' = Cinl a' \226\136\167 P a').
Time Proof.
Time eauto using csum_updateP_l.
Time Qed.
Time
Lemma csum_updateP'_r (P : B \226\134\146 Prop) b :
  b ~~>: P \226\134\146 Cinr b ~~>: (\206\187 m', \226\136\131 b', m' = Cinr b' \226\136\167 P b').
Time Proof.
Time eauto using csum_updateP_r.
Time Qed.
Time
Lemma csum_local_update_l (a1 a2 a1' a2' : A) :
  (a1, a2) ~l~> (a1', a2') \226\134\146 (Cinl a1, Cinl a2) ~l~> (Cinl a1', Cinl a2').
Time Proof.
Time (intros Hup n mf ? Ha1; simpl in *).
Time (destruct (Hup n (mf \226\137\171= maybe Cinl)); auto).
Time {
Time by destruct mf as [[]| ]; inversion_clear Ha1.
Time }
Time split.
Time done.
Time by destruct mf as [[]| ]; inversion_clear Ha1; constructor.
Time Qed.
Time
Lemma csum_local_update_r (b1 b2 b1' b2' : B) :
  (b1, b2) ~l~> (b1', b2') \226\134\146 (Cinr b1, Cinr b2) ~l~> (Cinr b1', Cinr b2').
Time Proof.
Time (intros Hup n mf ? Ha1; simpl in *).
Time (destruct (Hup n (mf \226\137\171= maybe Cinr)); auto).
Time {
Time by destruct mf as [[]| ]; inversion_clear Ha1.
Time }
Time split.
Time done.
Time by destruct mf as [[]| ]; inversion_clear Ha1; constructor.
Time Qed.
Time End cmra.
Time Arguments csumR : clear implicits.
Time
Instance csum_map_cmra_morphism  {A A' B B' : cmraT} 
 (f : A \226\134\146 A') (g : B \226\134\146 B'):
 (CmraMorphism f \226\134\146 CmraMorphism g \226\134\146 CmraMorphism (csum_map f g)).
Time Proof.
Time (split; try apply _).
Time -
Time (intros n [a| b| ]; simpl; auto using cmra_morphism_validN).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>[a|b|] =>//=; rewrite
  cmra_morphism_pcore; by destruct pcore).
Time -
Time
(<ssreflect_plugin::ssrtclintros@0> intros [xa| ya| ] [xb| yb| ] =>//=; by
  rewrite -cmra_morphism_op).
Time Qed.
Time #[program]
Definition csumRF (Fa Fb : rFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ =>
                  csumR (rFunctor_car Fa A B) (rFunctor_car Fb A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  csumC_map (rFunctor_map Fa fg) (rFunctor_map Fb fg) |}.
Time Next Obligation.
Time
by
 intros Fa Fb A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply csumC_map_ne;
  try apply rFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros Fa Fb A ? B ? x).
Time rewrite /= -{+2}(csum_map_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply csum_map_ext =>y; apply rFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros Fa Fb A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -csum_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply csum_map_ext =>y;
  apply rFunctor_compose).
Time Qed.
Time
Instance csumRF_contractive  Fa Fb:
 (rFunctorContractive Fa
  \226\134\146 rFunctorContractive Fb \226\134\146 rFunctorContractive (csumRF Fa Fb)).
Time Proof.
Time (intros ? ? A1 ? A2 ? B1 ? B2 ? n f g Hfg).
Time by apply csumC_map_ne; try apply rFunctor_contractive.
Time Qed.
