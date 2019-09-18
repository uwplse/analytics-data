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
Require Export Arith.
Require Export Lia.
Require Export Program.Tactics.
Require Export Coq.Arith.Wf_nat.
Create HintDb math discriminated.
Hint Resolve le_lt_n_Sm: math.
Hint Extern 100  => lia: math.
Hint Extern 100  => congruence: math.
Tactic Notation
 "dependent" "strong" "induction" constr(e) "generalizing" constr(l) :=
 (let v := fresh "v" in
  let Heq := fresh "Heqv" in
  remember e as v eqn:Heq ; generalize Heq; clear Heq; generalize l; clear l;
   induction v using lt_wf_ind; intros l;
   (let Heq' := fresh "Heqn" in
    intros Heq'; subst;
     (let l' := fresh "v" in
      let H' := fresh "H" in
      match goal with
      | H:forall m, @?A m -> forall l, m = @?B l -> @?C l
        |- _ =>
            let H0 := fresh "IH" in
            assert (H0 : forall l, A (B l) -> C l);
             [ intros l' H'; apply (H _ H'); reflexivity
             | clear H; cbn beta in H0 ]
      end))).
Tactic Notation
 "dependent" "strong" "induction" constr(e) "generalizing" constr(l)
 constr(l0) :=
 (let v := fresh "v" in
  let Heq := fresh "Heqv" in
  remember e as v eqn:Heq ; generalize Heq; clear Heq; generalize l, l0;
   clear l l0; induction v using lt_wf_ind; intros l l0;
   (let Heq' := fresh "Heqn" in
    intros Heq'; subst;
     (let l' := fresh "v" in
      let l0' := fresh "v" in
      let H' := fresh "H" in
      match goal with
      | H:forall m, @?A m -> forall l l0, m = @?B l l0 -> @?C l l0
        |- _ =>
            let H0 := fresh "IH" in
            assert (H0 : forall l l0, A (B l l0) -> C l l0);
             [ intros l' l0' H'; apply (H _ H'); reflexivity
             | clear H; cbn beta in H0 ]
      end))).
Tactic Notation
 "dependent" "strong" "induction" constr(e) "generalizing" constr(l)
 constr(l0) constr(l1) :=
 (let v := fresh "v" in
  let Heq := fresh "Heqv" in
  remember e as v eqn:Heq ; generalize Heq; clear Heq; generalize l, l0, l1;
   clear l l0 l1; induction v using lt_wf_ind; intros l l0 l1;
   (let Heq' := fresh "Heqn" in
    intros Heq'; subst;
     (let l' := fresh "v" in
      let l0' := fresh "v" in
      let l1' := fresh "v" in
      let H' := fresh "H" in
      match goal with
      | H:forall m, @?A m -> forall l l0 l1, m = @?B l l0 l1 -> @?C l l0 l1
        |- _ =>
            let H0 := fresh "IH" in
            assert (H0 : forall l l0 l1, A (B l l0 l1) -> C l l0 l1);
             [ intros l' l0' l1' H'; apply (H _ H'); reflexivity
             | clear H; cbn beta in H0 ]
      end))).
Tactic Notation
 "dependent" "strong" "induction" constr(e) "generalizing" constr(l)
 constr(l0) constr(l1) constr(l2) constr(l3) constr(l4) :=
 (let v := fresh "v" in
  let Heq := fresh "Heqv" in
  remember e as v eqn:Heq ; generalize Heq; clear Heq;
   generalize l, l0, l1, l2, l3, l4; clear l l0 l1 l2 l3 l4;
   induction v using lt_wf_ind; intros l l0 l1 l2 l3 l4;
   (let Heq' := fresh "Heqn" in
    intros Heq'; subst;
     (let l' := fresh "v" in
      let l0' := fresh "v" in
      let l1' := fresh "v" in
      let l2' := fresh "v" in
      let l3' := fresh "v" in
      let l4' := fresh "v" in
      let H' := fresh "H" in
      match goal with
      | H:forall m,
          @?A m ->
          forall l l0 l1 l2 l3 l4,
          m = @?B l l0 l1 l2 l3 l4 -> @?C l l0 l1 l2 l3 l4
        |- _ =>
            let H0 := fresh "IH" in
            assert
             (H0 :
              forall l l0 l1 l2 l3 l4,
              A (B l l0 l1 l2 l3 l4) -> C l l0 l1 l2 l3 l4);
             [ intros l' l0' l1' l2' l3' l4' H'; apply (H _ H'); reflexivity
             | clear H; cbn beta in H0 ]
      end))).
Ltac
 destruct_pairs :=
  repeat
   (try
     match goal with
     | H:(_ && _)%bool = true |- _ => apply andb_prop in H
     end; Tactics.destruct_pairs).
