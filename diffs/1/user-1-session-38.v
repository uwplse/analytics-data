Set Bullet Behavior "Strict Subproofs".
Require Import Coq.Sets.Powerset_facts.
Inductive zipWith_ensembles {A : Type} (f : A -> A -> A)
(dom cod : Ensemble A) : Ensemble A :=
    zipWith_ensembles_intro :
      forall x y,
      In _ dom x -> In _ cod y -> In _ (zipWith_ensembles f dom cod) (f x y).
Theorem zipWith_ensembles_propagation_left {A : Type} :
  forall x S1 S2 f,
  Inhabited A S2 ->
  In A S1 x -> exists y, In _ (zipWith_ensembles f S1 S2) (f x y).
Proof.
(intros).
(inversion H).
eexists.
(eapply zipWith_ensembles_intro).
eassumption.
eassumption.
Qed.
Theorem zipWith_ensembles_propagation_right {A : Type} :
  forall y S1 S2 f,
  Inhabited A S1 ->
  In A S2 y -> exists x, In _ (zipWith_ensembles f S1 S2) (f x y).
Proof.
(intros).
(inversion H).
eexists.
(eapply zipWith_ensembles_intro).
eassumption.
eassumption.
Qed.
Inductive SetPMap {A B : Type} (st : Ensemble A) (f : A -> option B) :
Ensemble B :=
    setpmap_intro :
      forall x y, In _ st x -> f x = Some y -> In _ (SetPMap st f) y.
Lemma inversion_setpmap {A : Type} :
  forall S f x, In A (SetPMap S f) x -> exists y, Some x = f y /\ In A S y.
Proof.
(intros).
(inversion H).
subst.
eexists.
symmetry in H1.
(intros).
(split; eassumption).
Qed.
Lemma included_refl : forall T S, Included T S S.
Proof.
(intros).
(unfold Included).
eauto.
Qed.
Lemma included_singleton {A : Type} :
  forall a b,
  Inhabited A a -> Included A a (Singleton A b) -> a = Singleton A b.
Proof.
(intros).
(eapply Extensionality_Ensembles).
(unfold Same_set).
split.
eassumption.
(unfold Included).
(intros).
(apply Singleton_inv in H1).
subst.
(unfold Included in H0).
(inversion H).
(pose proof (H0 _ H1)).
(apply Singleton_inv in H2).
subst.
assumption.
Qed.
Lemma Inhabited_singleton {A : Type} : forall a, Inhabited A (Singleton _ a).
Proof.
(intros).
econstructor.
(apply In_singleton).
Qed.
Lemma Inhabited_SetPMap {A B : Type} :
  forall st (f : A -> option B),
  (exists x, In _ st x /\ f x <> None) -> Inhabited _ (SetPMap st f).
Proof.
(intros).
(repeat destruct H).
(destruct (f x) eqn:?).
(repeat econstructor; eauto).
congruence.
Qed.
Lemma SetMap_eq {A : Type} :
  forall st (f : A -> option A),
  (forall x, In _ st x <-> f x = Some x) -> st = SetPMap st f.
Proof.
(intros).
(eapply Extensionality_Ensembles).
(unfold Same_set).
(split; unfold Included).
-
(econstructor; eauto).
(eapply H; eauto).
-
(intros).
(inversion H0).
subst.
(apply H in H1).
(apply H).
(rewrite H1 in H2).
(inversion H2; subst; eauto).
Qed.
Lemma singleton_not_empty {A : Type} :
  forall (e : A) s, s = Singleton _ e -> s <> Empty_set _.
Proof.
(intros).
(intros contra).
(pose proof (Noone_in_empty _ e)).
(pose proof (Singleton_intro _ e e eq_refl)).
subst.
congruence.
Qed.
Lemma singleton_eq {A : Type} :
  forall e1 e2 : A, Singleton _ e1 = Singleton _ e2 -> e1 = e2.
Proof.
(intros).
(eapply Singleton_inv).
(pose proof (Singleton_intro _ e2 e2 eq_refl)).
(rewrite H).
eassumption.
Qed.
