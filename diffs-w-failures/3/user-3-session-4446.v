Time From stdpp Require Export telescopes.
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
Time +
Time (<ssreflect_plugin::ssrtclseq@0> rewrite -forall_intro ; first  done).
Time (intros p).
Time rewrite (tele_arg_O_inv p) /= //.
Time -
Time (simpl).
Time (apply (anti_symm _); apply forall_intro; intros a).
Time +
Time rewrite /= -IH.
Time (apply forall_intro; intros p).
Time by rewrite (forall_elim (TargS a p)).
Time +
Time move /tele_arg_inv: {}a {} =>[x [pf {+}->]] {a} /=.
Time setoid_rewrite  <- IH.
Time rewrite 2!forall_elim.
Time done.
Time Qed.
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
Time -
Time (simpl).
Time (apply (anti_symm _); apply exist_elim).
Time +
Time (intros p).
Time move /tele_arg_inv: {}p {} =>[x [pf {+}->]] {p} /=.
Time by rewrite -exist_intro -IH -exist_intro.
Time +
Time (intros x).
Time rewrite /= -IH.
Time (apply exist_elim; intros p).
Time by rewrite -(exist_intro (TargS x p)).
Time Qed.
Time #[global]
Instance bi_tforall_ne  n:
 (Proper (pointwise_relation _ (dist n) ==> dist n) (@bi_tforall PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_tforall_forall.
Time rewrite EQ //.
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
Time rewrite EQ //.
Time Qed.
Time #[global]
Instance bi_texist_proper :
 (Proper (pointwise_relation _ (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@bi_texist PROP TT)).
Time Proof.
Time (intros ? ? EQ).
Time rewrite !bi_texist_exist.
Time rewrite EQ //.
Time Qed.
Time End telescope_quantifiers.
