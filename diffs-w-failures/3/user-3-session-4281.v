Time From iris.algebra Require Export ofe.
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
Time
Lemma pure_step_nsteps_ctx K `{!@LanguageCtx \206\155 K} 
  n e1 e2 :
  relations.nsteps pure_step n e1 e2
  \226\134\146 relations.nsteps pure_step n (K e1) (K e2).
Time Proof.
Time (induction 1; econstructor; eauto using pure_step_ctx).
Time Qed.
Time
Lemma pure_exec_ctx K `{!@LanguageCtx \206\155 K} \207\134 n e1 
  e2 : PureExec \207\134 n e1 e2 \226\134\146 PureExec \207\134 n (K e1) (K e2).
Time Proof.
Time (rewrite /PureExec; eauto using pure_step_nsteps_ctx).
Time Qed.
Time Class IntoVal (e : expr \206\155) (v : val \206\155) :=
         into_val : of_val v = e.
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
