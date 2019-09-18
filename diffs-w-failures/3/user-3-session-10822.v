Time Require Import Setoid.
Time Require Import Morphisms.
Time Require Classical_Prop.
Time Require Import Tactical.Propositional.
Time Require Import Tactical.Misc.
Time From Classes Require Import Classes.
Time Set Implicit Arguments.
Time Generalizable Variables all.
Time Set Warnings "-undeclared-scope".
Time Section TransitionRelations.
Time
Inductive Return (B T : Type) : Type :=
  | Val : forall (b : B) (t : T), _
  | Err : _.
Time Arguments Val {_} {_}.
Time Arguments Err {_} {_}.
Time Definition relation A B T := A -> Return B T -> Prop.
Time
Definition and_then {A} {B} {C} {T1} {T2} (r1 : relation A B T1)
  (r2 : T1 -> relation B C T2) : relation A C T2 :=
  fun x mz =>
  match mz with
  | Val z o2 => exists o1 y, r1 x (Val y o1) /\ (r2 o1) y (Val z o2)
  | Err => r1 x Err \/ (exists o1 y, r1 x (Val y o1) /\ (r2 o1) y Err)
  end.
Time
Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
  (at level 55, p2  at next level, right associativity).
Time
Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
  (at level 54, right associativity).
Time
Definition pure A T (o0 : T) : relation A A T := fun x y => Val x o0 = y.
Time
Definition identity {A} {T} : relation A A T :=
  fun x y => exists t, Val x t = y.
Time Definition any {A} {B} {T} : relation A B T := fun x y => True.
Time Definition none {A} {B} {T} : relation A B T := fun x y => False.
Time
Definition reads {A} {T} (f : A -> T) : relation A A T :=
  fun x y => Val x (f x) = y.
Time
Definition puts {A} (f : A -> A) : relation A A unit :=
  fun x y => y = Val (f x) tt.
Time Definition error {A} {B} {T} : relation A B T := fun _ r => r = Err.
Time
Definition fst_lift {A1} {A2} {B} {T} (r : relation A1 A2 T) :
  relation (A1 * B) (A2 * B) T :=
  fun '(a, b) y =>
  match y with
  | Err => r a Err
  | Val (a', b') t => r a (Val a' t) /\ b = b'
  end.
Time
Definition snd_lift {A1} {A2} {B} {T} (r : relation A1 A2 T) :
  relation (B * A1) (B * A2) T :=
  fun '(b, a) y =>
  match y with
  | Err => r a Err
  | Val (b', a') t => r a (Val a' t) /\ b = b'
  end.
Time
Definition zoom A C (proj : A -> C) (inj : C -> A -> A) 
  T (r : relation C C T) : relation A A T :=
  fun s y =>
  match y with
  | Err => r (proj s) Err
  | Val s' t => r (proj s) (Val (proj s') t) /\ s' = inj (proj s') s
  end.
Time
Definition readSome {A} {T} (f : A -> option T) : 
  relation A A T :=
  fun s r => match f s with
             | Some v => r = Val s v
             | None => r = Err
             end.
Time
Definition readNone {A} {T} (f : A -> option T) : 
  relation A A unit :=
  fun s r => match f s with
             | Some _ => r = Err
             | None => r = Val s tt
             end.
Time
Inductive such_that {A} {T} (f : A -> T -> Prop) : relation A A T :=
    such_that_holds : forall s v, f s v -> such_that f s (Val s v).
Time Definition predicate A := A -> Prop.
Time
Definition test {A} (P : predicate A) : relation A A unit :=
  fun x y => P x /\ Val x tt = y.
Time
Definition rel_or A B T (r1 r2 : relation A B T) : 
  relation A B T := fun x y => r1 x y \/ r2 x y.
Time Infix "+" := rel_or.
Time
Inductive seq_star A `(r : relation A A T) : relation A A T :=
  | seq_star_refl : forall x o, seq_star r x (Val x o)
  | seq_star_one_more_valid :
      forall x y z o1, r x (Val y o1) -> seq_star r y z -> seq_star r x z
  | seq_star_one_more_err : forall x, r x Err -> seq_star r x Err.
Time
Inductive seq_plus A `(r : relation A A T) : relation A A T :=
  | seq_plus_once : forall x y, r x y -> seq_plus r x y
  | seq_plus_one_more_valid :
      forall x y z o1, r x (Val y o1) -> seq_plus r y z -> seq_plus r x z.
Time
Inductive bind_star A `(r : T -> relation A A T) : T -> relation A A T :=
  | bind_star_pure : forall (o : T) x, bind_star r o x (Val x o)
  | bind_star_one_more_valid :
      forall (o1 : T) x y z o2,
      r o1 x (Val y o2) -> bind_star r o2 y z -> bind_star r o1 x z
  | bind_star_one_more_err :
      forall (o1 : T) x, r o1 x Err -> bind_star r o1 x Err.
Time
Inductive bind_star_r A `(r : T -> relation A A T) : T -> relation A A T :=
  | bind_star_r_pure : forall (o : T) x, bind_star_r r o x (Val x o)
  | bind_star_r_one_more_valid :
      forall (o1 : T) x y z o2,
      bind_star_r r o1 x (Val y o2) -> r o2 y z -> bind_star_r r o1 x z
  | bind_star_r_one_more_err :
      forall (o1 o2 : T) x y,
      bind_star_r r o1 x (Val y o2) -> r o2 y Err -> bind_star_r r o1 x Err.
Time
Definition rimpl {A} {B} {T} (r1 r2 : relation A B T) :=
  forall x y, r1 x y -> r2 x Err \/ r2 x y.
Time #[global]
Instance rimpl_preorder  T: (PreOrder (rimpl (A:=A) (B:=B) (T:=T))).
Time split.
Time -
Time (intros x y).
Time firstorder.
Time -
Time (intros x y z H1 H2 ? ? ?).
Time (destruct (H1 x0 y0); intuition).
Time (destruct (H2 x0 Err); intuition).
Time Qed.
Time
Definition requiv {A} {B} {T} (r1 r2 : relation A B T) :=
  rimpl r1 r2 /\ rimpl r2 r1.
Time #[global]
Instance requiv_equivalence : (Equivalence (requiv (A:=A) (B:=B) (T:=T))).
Time Proof.
Time split.
Time -
Time (intros ?; split; reflexivity).
Time -
Time (intros ? ? (?, ?); split; eauto).
Time -
Time (intros ? ? ? (?, ?) (?, ?); split).
Time *
Time (etransitivity; eauto).
Time *
Time (etransitivity; eauto).
Time Qed.
Time Infix "--->" := rimpl (at level 60, no associativity).
Time Infix "<--->" := requiv (at level 60, no associativity).
Time #[global]
Instance rimpl_requiv_sub : (subrelation (requiv (A:=A) (B:=B) (T:=T)) rimpl)
 := _.
Time #[global]
Instance rimpl_proper_basics_flip  A B T (r : relation A B T):
 (Proper (Basics.flip rimpl ==> Basics.flip Basics.impl) (rimpl r)).
Time Proof.
Time (unfold Basics.flip, Basics.impl).
Time (intros ? ? ? ?).
Time (etransitivity; eauto).
Time Qed.
Time
Lemma rimpl_elim A B T (r1 r2 : relation A B T) a 
  b : r1 a b -> r1 ---> r2 -> r2 a Err \/ r2 a b.
Time Proof.
Time firstorder.
Time Qed.
Time
Lemma requiv_no_err_elim A B T (r1 r2 : relation A B T) 
  a b : r1 a b -> r1 <---> r2 -> ~ r1 a Err -> r2 a b.
Time Proof.
Time (intros Hr1 (Hlr, Hrl) Hno_err).
Time (eapply Hlr in Hr1).
Time (destruct Hr1 as [Herr| ?]; eauto).
Time (apply Hrl in Herr).
Time intuition.
Time Qed.
Time
Lemma requiv_no_err_elim' A B T (r1 r2 : relation A B T) 
  a b : r1 a b -> r1 <---> r2 -> ~ r2 a Err -> r2 a b.
Time Proof.
Time (intros Hr1 (Hlr, Hrl) Hno_err).
Time (eapply Hlr in Hr1).
Time (destruct Hr1 as [Herr| ?]; eauto).
Time intuition.
Time Qed.
Time
Lemma requiv_err_elim A B T (r1 r2 : relation A B T) 
  a : r1 a Err -> r1 <---> r2 -> r2 a Err.
Time Proof.
Time (intros Hr1 (Hlr, Hrl)).
Time (eapply Hlr in Hr1; intuition).
Time Qed.
Time
Theorem rimpl_to_requiv A B T (r1 r2 : relation A B T) :
  r1 ---> r2 -> r2 ---> r1 -> r1 <---> r2.
Time Proof.
Time firstorder.
Time Qed.
Time
Theorem requiv_to_rimpl1 A B T (r1 r2 : relation A B T) :
  r1 <---> r2 -> r1 ---> r2.
Time Proof.
Time firstorder.
Time Qed.
Time
Theorem requiv_to_rimpl2 A B T (r1 r2 : relation A B T) :
  r1 <---> r2 -> r2 ---> r1.
Time Proof.
Time firstorder.
Time Qed.
Time
Theorem requiv_to_rimpls A B T (r1 r2 : relation A B T) :
  r1 <---> r2 -> r1 ---> r2 /\ r2 ---> r1.
Time Proof.
Time firstorder.
Time Qed.
Time Hint Immediate rimpl_to_requiv requiv_to_rimpl1 requiv_to_rimpl2: core.
Time
Theorem rimpl_or A B T (r1 r2 : relation A B T) :
  r1 ---> r2 -> r1 + r2 <---> r2.
Time Proof.
Time firstorder.
Time Qed.
Time
Theorem rel_or_to_rimpl A B T (r1 r2 : relation A B T) :
  r1 + r2 <---> r2 -> r1 ---> r2.
Time Proof.
Time firstorder.
Time Qed.
Time Hint Unfold Proper respectful pointwise_relation: t.
Time Hint Unfold Basics.flip Basics.impl: t.
Time Hint Unfold and_then rel_or pure any identity reads: t.
Time
Ltac
 add_hypothesis' pf :=
  let P := type of pf in
  lazymatch P with
  | ?P' \/ ?Q' =>
      lazymatch goal with
      | H:P' \/ Q' |- _ => fail "already known"
      | H:Q' \/ P' |- _ => fail "already known"
      | H:P' |- _ => fail "already known"
      | H:Q' |- _ => fail "already known"
      | _ => pose proof pf
      end
  | ?P' =>
      lazymatch goal with
      | H:P' |- _ => fail "already known"
      | _ => pose proof pf
      end
  end.
Time
Ltac
 t :=
  autounfold with t;
   repeat
    match goal with
    | |- _ <---> _ => split
    | |- _ ---> _ => unfold "--->"
    | H:?r <---> _, H':?r ?x ?y |- _ => add_hypothesis (proj1 H x y H')
    | H:_ <---> ?r, H':?r ?x ?y |- _ => add_hypothesis (proj2 H x y H')
    | H:?r ---> _, H':?r ?x ?y |- _ => add_hypothesis (H x y H')
    | u:unit |- _ => destruct u
    | |- exists _ : unit, _ => exists tt
    | _ => progress propositional
    | _ => solve
    [ eauto  10 ]
    | H:_ \/ _ |- _ => destruct H
    | H:none _ _ |- _ => destruct H
    | H:Val _ _ = Val _ _ |- _ => inversion H; subst; clear H
    | H:Val _ _ = Err |- _ => inversion H
    | H:Err = Val _ _ |- _ => inversion H
    end.
Time
Ltac destruct_return := match goal with
                        | y:Return _ _ |- _ => destruct y
                        end.
Time #[global]
Instance or_respects_equiv :
 (Proper (requiv ==> requiv ==> requiv) (rel_or (A:=A) (B:=B) (T:=T))).
Time Proof.
Time t.
Time Qed.
Time #[global]
Instance or_respects_impl :
 (Proper (rimpl ==> rimpl ==> rimpl) (rel_or (A:=A) (B:=B) (T:=T))).
Time Proof.
Time t.
Time Qed.
Time
Theorem and_then_monotonic A B C T1 T2 (r1 r1' : relation A B T1)
  (r2 r2' : T1 -> relation B C T2) :
  r1 ---> r1' ->
  (forall x, r2 x ---> r2' x) -> and_then r1 r2 ---> and_then r1' r2'.
Time Proof.
Time t.
Time destruct_return.
Time -
Time (destruct H1 as (o1, (y, (?, ?)))).
Time (edestruct (H0 o1); t).
Time -
Time (destruct H1 as [| (o1, (y, (?, ?)))]).
Time t.
Time (edestruct (H0 o1); t).
Time Qed.
Time #[global]
Instance and_then_respectful :
 (Proper (rimpl ==> pointwise_relation _ rimpl ==> rimpl)
    (and_then (A:=A) (B:=B) (C:=C) (T1:=T1) (T2:=T2))).
Time Proof.
Time (unfold Proper, "==>"; intros).
Time (apply and_then_monotonic; auto).
Time Qed.
Time
Lemma and_then_err_cancel A B C T1 T2 a (r1 : relation A B T1)
  (r2 r2' : T1 -> relation B C T2) :
  and_then r1 r2 a Err ->
  (forall x b, r2 x b Err -> r2' x b Err) -> and_then r1 r2' a Err.
Time Proof.
Time (intros Hand_then1 Himpl).
Time (destruct Hand_then1; t).
Time Qed.
Time
Theorem and_then_equiv_cong A B C T1 T2 (r1 r1' : relation A B T1)
  (r2 r2' : T1 -> relation B C T2) :
  r1 <---> r1' ->
  (forall x, r2 x <---> r2' x) -> and_then r1 r2 <---> and_then r1' r2'.
Time Proof.
Time (intros).
Time (split; apply and_then_monotonic; eauto).
Time Qed.
Time
Theorem and_then_cong_l A B C T1 T2 (r1 r1' : relation A B T1)
  (r2 : T1 -> relation B C T2) :
  r1 <---> r1' -> and_then r1 r2 <---> and_then r1' r2.
Time Proof.
Time (intros).
Time (split; apply and_then_monotonic; eauto; intros; reflexivity).
Time Qed.
Time
Theorem and_then_cong_r A B C T1 T2 (r1 : relation A B T1)
  (r2 r2' : T1 -> relation B C T2) :
  (forall x, r2 x <---> r2' x) -> and_then r1 r2 <---> and_then r1 r2'.
Time Proof.
Time (intros).
Time (split; apply and_then_monotonic; eauto; intros; reflexivity).
Time Qed.
Time
Theorem bind_identity1 A B T1 T2 (r : relation A B T2) :
  _ <- identity (T:=T1); r ---> r.
Time Proof.
Time t.
Time (destruct_return; t; intuition congruence).
Time Qed.
Time
Theorem bind_identity A B T1 T2 (r : relation A B T2) 
  (_ : Default T1) : _ <- identity (T:=T1); r <---> r.
Time Proof.
Time (unshelve (t; destruct_return; t; intuition congruence); eauto).
Time Qed.
Time Theorem reads_identity A T (f : A -> T) : reads f ---> identity.
Time Proof.
Time t.
Time Qed.
Time #[global]
Instance and_then_respectful_equiv :
 (Proper (requiv ==> pointwise_relation _ requiv ==> requiv)
    (and_then (A:=A) (B:=B) (C:=C) (T1:=T1) (T2:=T2))).
Time Proof.
Time (unfold Proper, "==>"; intros).
Time (apply and_then_equiv_cong; auto).
Time Qed.
Time Hint Constructors seq_star: core.
Time #[global]
Instance seq_star_respectful :
 (Proper (rimpl ==> rimpl) (seq_star (A:=A) (T:=T))).
Time Proof.
Time t.
Time (induction H0; intuition eauto; t).
Time Qed.
Time #[global]
Instance seq_star_equiv_respectful :
 (Proper (requiv ==> requiv) (seq_star (A:=A) (T:=T))).
Time Proof.
Time t.
Time (eapply seq_star_respectful; eauto).
Time (eapply seq_star_respectful; eauto).
Time Qed.
Time Hint Constructors bind_star: core.
Time #[global]
Instance bind_star_respectful :
 (Proper (pointwise_relation _ rimpl ==> eq ==> rimpl)
    (bind_star (A:=A) (T:=T))).
Time Proof.
Time t.
Time (induction H0; (eauto; specialize (H o1); intuition eauto); t).
Time Qed.
Time #[global]
Instance bind_star_equiv_respectful :
 (Proper (pointwise_relation _ requiv ==> eq ==> requiv)
    (bind_star (A:=A) (T:=T))).
Time Proof.
Time t.
Time -
Time
(induction H0; eauto; specialize (H o1);
  (apply requiv_to_rimpls in H; propositional; intuition eauto); t).
Time -
Time
(induction H0; eauto; specialize (H o1);
  (apply requiv_to_rimpls in H; propositional; intuition eauto); t).
Time Qed.
Time
Theorem and_then_monotonic_r A B C T1 T2 (r1 r2 : relation A B T1)
  (rx : T1 -> relation B C T2) :
  r1 ---> r2 -> and_then r1 rx ---> and_then r2 rx.
Time Proof.
Time (intros).
Time (rewrite H; reflexivity).
Time Qed.
Time
Theorem rel_or_symmetric A B T (r1 r2 : relation A B T) :
  r1 + r2 <---> r2 + r1.
Time Proof.
Time t.
Time Qed.
Time
Theorem rel_or_assoc A B T (r1 r2 r3 : relation A B T) :
  r1 + (r2 + r3) <---> r1 + r2 + r3.
Time Proof.
Time t.
Time Qed.
Time Theorem rel_or_idem A B T (r : relation A B T) : r + r <---> r.
Time Proof.
Time t.
Time Qed.
Time
Theorem rel_or_monotonic A B T (r1 r2 : relation A B T) 
  r : r1 ---> r2 -> r1 + r ---> r2 + r.
Time Proof.
Time t.
Time Qed.
Time Theorem rel_or_introl A B T (r1 r2 : relation A B T) : r1 ---> r1 + r2.
Time Proof.
Time t.
Time Qed.
Time Theorem rel_or_intror A B T (r1 r2 : relation A B T) : r2 ---> r1 + r2.
Time Proof.
Time t.
Time Qed.
Time
Theorem rel_or_elim A B T (r1 r2 : relation A B T) 
  r : r1 ---> r -> r2 ---> r -> r1 + r2 ---> r.
Time Proof.
Time t.
Time Qed.
Time
Theorem rel_or_elim_rx A B T (r1 r2 : relation A B T) 
  C T' (rx : T -> relation B C T') r :
  and_then r1 rx ---> r ->
  and_then r2 rx ---> r -> and_then (r1 + r2) rx ---> r.
Time Proof.
Time t.
Time (destruct_return; t).
Time Qed.
Time
Theorem bind_left_id A B T1 T2 (v : T1) (r : T1 -> relation A B T2) :
  and_then (pure v) r <---> r v.
Time Proof.
Time (t; destruct_return; t; intuition congruence).
Time Qed.
Time
Theorem bind_right_id A B T (r : relation A B T) :
  and_then r (@pure B T) <---> r.
Time Proof.
Time (t; destruct_return; t; intuition congruence).
Time Qed.
Time
Theorem bind_right_id_unit A B (r : relation A B unit) :
  and_then r (fun _ => pure tt) <---> r.
Time Proof.
Time (t; destruct_return; t; intuition congruence).
Time Qed.
Time
Theorem bind_assoc A B C D T1 T2 T3 (r1 : relation A B T1)
  (r2 : T1 -> relation B C T2) (r3 : T2 -> relation C D T3) :
  and_then (and_then r1 r2) r3 <--->
  and_then r1 (fun v => and_then (r2 v) r3).
Time Proof.
Time (repeat (t; destruct_return; t)).
Time Qed.
Time Theorem to_any A B T (r : relation A B T) : r ---> any.
Time Proof.
Time t.
Time Qed.
Time Theorem identity_to_any A : pure tt ---> any (A:=A).
Time Proof.
Time t.
Time Qed.
Time
Theorem any_idem A B C T1 T2 :
  any (B:=B) (T:=T1);; any ---> any (A:=A) (B:=C) (T:=T2).
Time Proof.
Time t.
Time Qed.
Time Theorem from_none A B T (r : relation A B T) : none ---> r.
Time Proof.
Time t.
Time Qed.
Time
Theorem none_idem A B C T1 T2 :
  none (B:=B) (T:=T1);; none ---> none (A:=A) (B:=C) (T:=T2).
Time Proof.
Time t.
Time (destruct_return; t).
Time Qed.
Time
Theorem none_absorb_l A B C T1 T2 p :
  x <- none (B:=B) (T:=T1); p x ---> none (A:=A) (B:=C) (T:=T2).
Time Proof.
Time t.
Time (destruct_return; t).
Time Qed.
Time
Theorem none_absorb_l_equiv A B C T1 T2 p :
  x <- none (B:=B) (T:=T1); p x <---> none (A:=A) (B:=C) (T:=T2).
Time Proof.
Time t.
Time (destruct_return; t).
Time Qed.
Time Theorem none_plus_r A B T1 (p : relation A B T1) : p + none <---> p.
Time Proof.
Time t.
Time Qed.
Time Theorem none_plus_l A B T1 (p : relation A B T1) : none + p <---> p.
Time Proof.
Time t.
Time Qed.
Time
Theorem seq_star_to_bind_star :
  forall A (r : relation A A unit),
  seq_star r <---> bind_star (fun _ => r) tt.
Time Proof.
Time t.
Time -
Time (induction H; t).
Time -
Time (induction H; t).
Time Qed.
Time
Lemma bind_star_fun_ext A T (r r' : T -> relation A A T) 
  (init : T) :
  (forall x, r x <---> r' x) -> bind_star r init <---> bind_star r' init.
Time Proof.
Time t.
Time -
Time (induction H0; eauto; edestruct (H o1); intuition; t).
Time -
Time (induction H0; eauto; edestruct (H o1); intuition; t).
Time Qed.
Time
Theorem bind_star_unit A (r : unit -> relation A A unit) 
  u : bind_star r u <---> seq_star (r tt).
Time Proof.
Time (intros).
Time (destruct u).
Time (rewrite seq_star_to_bind_star).
Time (apply bind_star_fun_ext; intros).
Time (destruct x; reflexivity).
Time Qed.
Time
Theorem bind_star_expand A T (r : T -> relation A A T) 
  (v : T) : pure v + and_then (r v) (bind_star r) <---> bind_star r v.
Time Proof.
Time (t; destruct_return; t; induction H; eauto; t; destruct_return; t).
Time Qed.
Time #[global]
Instance rimpl_equiv_proper  A B T (r : relation A B T):
 (Proper (requiv ==> Basics.flip Basics.impl) (rimpl r)).
Time Proof.
Time (intros ? ? (?, ?) ?).
Time (etransitivity; eauto).
Time Qed.
Time #[global]
Instance rimpl_equiv_applied_proper  A B T:
 (Proper (requiv ==> requiv ==> iff) (rimpl (A:=A) (B:=B) (T:=T))).
Time Proof.
Time (intros ? ? (?, ?) ? ? (?, ?)).
Time (split; intros; repeat (etransitivity; eauto)).
Time Qed.
Time Definition rimpl_refl A B T (r : relation A B T) : r ---> r := _.
Time Definition requiv_refl A B T (r : relation A B T) : r <---> r := _.
Time Hint Resolve rimpl_refl requiv_refl: core.
Time
Theorem bind_dist_r A B C T1 T2 (r1 r2 : relation A B T1)
  (r3 : T1 -> relation B C T2) :
  and_then (r1 + r2) r3 <---> and_then r1 r3 + and_then r2 r3.
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time
Theorem bind_dist_l A B C T1 T2 (r1 : relation A B T1)
  (r2 r3 : T1 -> relation B C T2) :
  and_then r1 (fun v => r2 v + r3 v) <---> and_then r1 r2 + and_then r1 r3.
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time
Theorem star_ind A T (r x : relation A A T) :
  identity ---> x -> r;; x ---> x -> seq_star r ---> x.
Time Proof.
Time (intros H1 H2 a y).
Time (induction 1).
Time -
Time (eapply H1).
Time (econstructor; eauto).
Time -
Time t.
Time *
Time left.
Time (edestruct (H2 x0 Err); eauto).
Time (simpl; intuition eauto).
Time *
Time (eapply H2).
Time (destruct z).
Time **
Time (econstructor; eauto).
Time **
Time right.
Time intuition eauto.
Time -
Time (eapply H2; left; eauto).
Time Qed.
Time
Theorem star_expand A T (r : relation A A T) :
  seq_star r <---> identity + (r;; seq_star r).
Time Proof.
Time (apply rimpl_to_requiv).
Time -
Time (apply star_ind; t; destruct_return; t).
Time -
Time (t; destruct_return; t).
Time Qed.
Time
Theorem seq_star1 A T (r : relation A A T) : r;; seq_star r ---> seq_star r.
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time
Theorem seq_star_fold A T (r r' : relation A A T) :
  r' ---> r -> r';; seq_star r ---> seq_star r.
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time
Theorem seq_star_none A T (r : relation A A T) : identity ---> seq_star r.
Time Proof.
Time t.
Time Qed.
Time Theorem seq_star_one A T (r : relation A A T) : r ---> seq_star r.
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time Hint Constructors seq_plus: core.
Time Theorem plus_one `(r : relation A A T) : r ---> seq_plus r.
Time Proof.
Time t.
Time Qed.
Time
Theorem plus_expand A T (r : relation A A T) :
  seq_plus r <---> r + (r;; seq_plus r).
Time Proof.
Time (t; destruct_return; t; induction H; eauto; t).
Time Qed.
Time #[global]
Instance and_then_pointwise  A B C T1 T2 (r : relation A B T1):
 (Proper
    (pointwise_relation _ (Basics.flip rimpl) ==>
     Basics.flip (rimpl (B:=C) (T:=T2))) (and_then r)).
Time Proof.
Time t.
Time (destruct_return; t; specialize (H o1); t).
Time Qed.
Time
Theorem star_duplicate A T (r : relation A A T) :
  seq_star r <---> seq_star r;; seq_star r.
Time Proof.
Time t.
Time -
Time (induction H).
Time *
Time (unshelve eauto; eauto).
Time *
Time (unshelve (destruct_return; t); eauto).
Time *
Time (do 2 left).
Time (eapply seq_star_one_more_err; eauto).
Time -
Time (destruct_return; t).
Time *
Time (remember (Val y o1) as z eqn:Heq ).
Time revert y o1 H0 Heq.
Time revert H.
Time (induction 1; intros).
Time **
Time (inversion Heq; subst).
Time intuition.
Time **
Time subst.
Time (edestruct IHseq_star; eauto).
Time **
Time congruence.
Time *
Time (remember (Val y o1) as z eqn:Heq ).
Time revert y o1 H0 Heq.
Time revert H.
Time (induction 1; intros).
Time **
Time (inversion Heq; subst).
Time intuition.
Time **
Time subst.
Time (edestruct IHseq_star; eauto).
Time **
Time congruence.
Time Qed.
Time Theorem star_one A T (r : relation A A T) : r ---> seq_star r.
Time Proof.
Time t.
Time (destruct_return; t).
Time Qed.
Time
Lemma star_monotonic A T (r1 r2 : relation A A T) :
  r1 ---> r2 -> seq_star r1 ---> seq_star r2.
Time Proof.
Time (intros).
Time (rewrite H; reflexivity).
Time Qed.
Time
Lemma star_congruent A T (r1 r2 : relation A A T) :
  r1 <---> r2 -> seq_star r1 <---> seq_star r2.
Time Proof.
Time (intros).
Time (rewrite H; reflexivity).
Time Qed.
Time
Lemma bind_star_congruent A T (r1 r2 : T -> relation A A T) 
  (v : T) :
  (forall v, r1 v <---> r2 v) -> bind_star r1 v <---> bind_star r2 v.
Time Proof.
Time (intros).
Time (apply bind_star_equiv_respectful; auto).
Time Qed.
Time
Theorem star_expand_r A (r : relation A A unit) :
  seq_star r <---> identity + (seq_star r;; r).
Time Proof.
Time (apply rimpl_to_requiv).
Time -
Time
(unshelve
  (apply star_ind; t; destruct_return; t; inversion H0; subst; t; congruence);
  exact tt).
Time -
Time (apply rel_or_elim).
Time *
Time t.
Time *
Time (rewrite star_duplicate  at 2).
Time (apply and_then_monotonic; eauto).
Time (intros []).
Time (apply star_one).
Time Qed.
Time
Ltac
 cong :=
  let solver := try reflexivity; try (solve [ t ]) in
  match goal with
  | |- and_then _ _ ---> and_then _ _ =>
        apply and_then_monotonic; intros; solver
  | |- seq_star _ ---> seq_star _ => apply star_monotonic; solver
  end.
Time
Theorem bind_unit' B C T (q : unit -> relation B C T) v : q v <---> q tt.
Time Proof.
Time t.
Time Qed.
Time
Theorem bind_unit A B C T (p : relation A B unit)
  (q : unit -> relation B C T) : and_then p q <---> p;; q tt.
Time Proof.
Time (setoid_rewrite  <- bind_unit'; reflexivity).
Time Qed.
Time
Theorem denesting A T (r1 r2 : relation A A T) (_ : Default T) :
  seq_star (r1 + r2) <---> seq_star r1;; seq_star (r2;; seq_star r1).
Time Proof.
Time (apply rimpl_to_requiv).
Time -
Time (unshelve (apply star_ind; t; destruct_return; t; intuition t); eauto).
Time -
Time (setoid_rewrite star_duplicate at 4; cong).
Time cong.
Time (apply star_ind; try (solve [ t ])).
Time (setoid_rewrite star_duplicate at 3; cong).
Time (setoid_rewrite star_duplicate at 2; cong).
Time *
Time setoid_rewrite  <- star_one.
Time (apply rel_or_intror).
Time *
Time cong.
Time Qed.
Time
Theorem bind_sliding A T1 (p : relation A A T1) (q : T1 -> relation A A unit)
  :
  seq_star (and_then p q);; p <---> v <- p; bind_star (fun v0 => q v0;; p) v.
Time Proof.
Time (apply rimpl_to_requiv).
Time -
Time t.
Time destruct_return.
Time *
Time (destruct H as ([], (y, (Hstar, Hy)))).
Time (remember (Val y tt) as ret eqn:Heq ).
Time gen y Heq.
Time (induction Hstar; subst; t).
Time **
Time (specialize (IHHstar _ _ _); t).
Time left.
Time right.
Time (do 2 eexists; split; eauto).
Time (eapply bind_star_one_more_err).
Time eauto.
Time *
Time t.
Time **
Time (set (ret := @Err A unit)).
Time (replace Err with ret in H at 1; eauto).
Time (remember ret as ret' eqn:Heq ).
Time (unfold ret in Heq).
Time (induction H).
Time ***
Time congruence.
Time ***
Time (t; left; right; do 2 eexists; split; eauto; t).
Time ***
Time t.
Time **
Time (remember (Val y tt) as ret eqn:Heq ).
Time gen y Heq.
Time (induction H; subst; t).
Time ***
Time (specialize (IHseq_star _ _ _); t).
Time ****
Time left.
Time right.
Time (do 2 eexists; split; eauto).
Time (eapply bind_star_one_more_err).
Time eauto.
Time ****
Time left.
Time right.
Time (do 2 eexists; split; eauto).
Time (eapply bind_star_one_more_err).
Time eauto.
Time -
Time t.
Time destruct_return.
Time *
Time t.
Time gen x.
Time (unshelve (induction H0; t); try exact tt).
Time (specialize (IHbind_star _ _); t).
Time *
Time (unshelve t; try exact tt).
Time **
Time gen x.
Time (unshelve (induction H0; t); try exact tt).
Time (unshelve (specialize (IHbind_star _ _); t); try exact tt).
Time Qed.
Time
Theorem seq_sliding A T1 (p : relation A A T1) (q : relation A A unit) :
  seq_star (p;; q);; p ---> p;; seq_star (q;; p).
Time Proof.
Time -
Time t.
Time destruct_return.
Time *
Time (destruct H as ([], (y, (Hstar, Hy)))).
Time (remember (Val y tt) as ret eqn:Heq ).
Time gen y Heq.
Time (induction Hstar; subst; t).
Time (specialize (IHHstar _ _ _); t).
Time left.
Time right.
Time (do 2 eexists; split; eauto).
Time (eapply seq_star_one_more_err).
Time eauto.
Time *
Time t.
Time **
Time (set (ret := @Err A unit)).
Time (replace Err with ret in H at 1; eauto).
Time (remember ret as ret' eqn:Heq ).
Time (unfold ret in Heq).
Time (induction H).
Time ***
Time congruence.
Time ***
Time (t; left; right; do 2 eexists; split; eauto; t).
Time ***
Time t.
Time **
Time (remember (Val y tt) as ret eqn:Heq ).
Time gen y Heq.
Time (induction H; subst; t).
Time (specialize (IHseq_star _ _ _); t).
Time ***
Time left.
Time right.
Time (do 2 eexists; split; eauto).
Time (eapply seq_star_one_more_err).
Time eauto.
Time ***
Time left.
Time right.
Time (do 2 eexists; split; eauto).
Time (eapply seq_star_one_more_err).
Time eauto.
Time Qed.
Time
Theorem seq_unit_sliding A (p : relation A A unit) 
  (q : relation A A unit) : p;; seq_star (q;; p) ---> seq_star (p;; q);; p.
Time Proof.
Time setoid_rewrite seq_star_to_bind_star at 1.
Time setoid_rewrite bind_sliding.
Time (eapply bind_unit).
Time Qed.
Time
Theorem seq_unit_sliding_equiv A (p : relation A A unit)
  (q : relation A A unit) : seq_star (p;; q);; p <---> p;; seq_star (q;; p).
Time Proof.
Time (apply rimpl_to_requiv; auto using seq_sliding, seq_unit_sliding).
Time Qed.
Time
Inductive seq_star_r A `(r : relation A A T) : relation A A T :=
  | seq_star_r_refl : forall x o, seq_star_r r x (Val x o)
  | seq_star_r_err_refl : forall x, r x Err -> seq_star_r r x Err
  | seq_star_r_one_more_valid :
      forall x y z o1 o2,
      seq_star_r r x (Val y o1) ->
      r y (Val z o2) -> seq_star_r r x (Val z o2)
  | seq_star_r_one_more_err :
      forall x y o1,
      seq_star_r r x (Val y o1) -> r y Err -> seq_star_r r x Err.
Time Hint Constructors seq_star_r: core.
Time
Lemma seq_star_r_one_more_valid_left {A} {T} (r : relation A A T) 
  x y z o1 o2 :
  r x (Val y o1) ->
  seq_star_r r y (Val z o2) -> exists o3, seq_star_r r x (Val z o3).
Time Proof.
Time (intros Hr Hseq).
Time (remember (Val z o2) as ret eqn:Heq ).
Time revert x z o1 o2 Hr Heq.
Time (induction Hseq; intros).
Time -
Time (unshelve t; eauto).
Time -
Time (unshelve t; eauto).
Time -
Time t.
Time (edestruct IHHseq; eauto).
Time -
Time t.
Time Qed.
Time
Lemma seq_star_trans A `(r : relation A A T) (x y : A) 
  (o : T) z : seq_star r x (Val y o) -> seq_star r y z -> seq_star r x z.
Time Proof.
Time (intros Hstar).
Time (remember (Val y o) as ret eqn:Heq ).
Time revert y o Heq.
Time (induction Hstar; t).
Time Qed.
Time
Lemma seq_star_rl_valid A `(r : relation A A T) x 
  b o1 o2 : seq_star_r r x (Val b o1) -> seq_star r x (Val b o2).
Time Proof.
Time (intros Hstar).
Time (remember (Val b o1) as ret eqn:Heq ).
Time revert b o1 Heq.
Time (induction Hstar; t).
Time (specialize (IHHstar y o1 _); t).
Time clear Hstar.
Time (remember (Val y o2) as ret eqn:Heq ).
Time revert o2 Heq.
Time (induction IHHstar; t).
Time Qed.
Time Hint Resolve seq_star_r_one_more_valid_left: core.
Time
Theorem seq_star_lr A `(r : relation A A T) :
  seq_star r <---> seq_star_r r;; identity.
Time Proof.
Time t.
Time -
Time (induction H).
Time *
Time (unshelve t; eauto).
Time *
Time t.
Time **
Time
(unshelve (induction H1; propositional; eauto; t; destruct_return; t); eauto).
Time **
Time (destruct_return; t).
Time ***
Time (edestruct (@seq_star_r_one_more_valid_left A _ r); eauto; t).
Time ***
Time (remember Err as ret eqn:Heq ).
Time gen Heq.
Time (unshelve (induction H1; intros; t); eauto).
Time left.
Time left.
Time (edestruct (@seq_star_r_one_more_valid_left A _ r); eauto; t).
Time *
Time left.
Time left.
Time econstructor.
Time (unshelve t; eauto).
Time -
Time (destruct_return; t).
Time *
Time right.
Time (eapply seq_star_rl_valid; eauto).
Time *
Time left.
Time (inversion H; subst).
Time **
Time (eapply seq_star_one_more_err; eauto).
Time **
Time
(unshelve
  (eapply seq_star_trans; [  | eapply seq_star_one_more_err; eauto ]); eauto).
Time (eapply seq_star_rl_valid; eauto).
Time Qed.
Time Hint Constructors bind_star_r: core.
Time
Lemma bind_star_r_one_more_valid_left {A} {T} (r : T -> relation A A T) 
  x y z o1 o2 o3 :
  r o1 x (Val y o2) ->
  bind_star_r r o2 y (Val z o3) -> bind_star_r r o1 x (Val z o3).
Time Proof.
Time (intros Hr Hseq).
Time (remember (Val z o2) as ret eqn:Heq ).
Time revert x o1 Hr Heq.
Time (induction Hseq; intros; unshelve t; eauto).
Time Qed.
Time
Lemma bind_star_trans A `(r : T -> relation A A T) 
  (x y : A) (o1 o2 : T) z :
  bind_star r o1 x (Val y o2) -> bind_star r o2 y z -> bind_star r o1 x z.
Time Proof.
Time (intros Hstar).
Time (remember (Val y o2) as ret eqn:Heq ).
Time revert y o2 Heq.
Time (induction Hstar; t).
Time Qed.
Time
Lemma bind_star_rl_valid A `(r : T -> relation A A T) 
  x b o1 o2 : bind_star_r r o1 x (Val b o2) -> bind_star r o1 x (Val b o2).
Time Proof.
Time (intros Hstar).
Time (remember (Val b o2) as ret eqn:Heq ).
Time revert b o2 Heq.
Time (induction Hstar; t).
Time (specialize (IHHstar y o2 _); t).
Time clear Hstar.
Time (remember (Val y o2) as ret eqn:Heq ).
Time revert o2 Heq H.
Time (induction IHHstar; t).
Time Qed.
Time
Lemma bind_star_lr_valid A `(r : T -> relation A A T) 
  x b o1 o2 : bind_star r o1 x (Val b o2) -> bind_star_r r o1 x (Val b o2).
Time Proof.
Time (intros Hstar).
Time (remember (Val b o2) as ret eqn:Heq ).
Time revert b o2 Heq.
Time (induction Hstar; t).
Time (specialize (IHHstar _ _ _); t).
Time clear Hstar.
Time (remember (Val y o2) as ret eqn:Heq ).
Time subst.
Time (induction IHHstar; t).
Time Qed.
Time Hint Resolve bind_star_r_one_more_valid_left: core.
Time
Theorem bind_star_lr A `(r : T -> relation A A T) 
  (v : T) : bind_star r v <---> bind_star_r r v.
Time Proof.
Time t.
Time -
Time (induction H).
Time *
Time (unshelve t; eauto).
Time *
Time t.
Time **
Time
(unshelve (induction H1; propositional; eauto; t; destruct_return; t); eauto).
Time **
Time (destruct_return; t; unshelve (induction H1; intros; t); eauto).
Time *
Time t.
Time -
Time (destruct_return; t).
Time *
Time right.
Time (eapply bind_star_rl_valid; eauto).
Time *
Time left.
Time
(inversion H; subst; unshelve
  (eapply bind_star_trans; [  | eapply bind_star_one_more_err; eauto ]);
  eauto using bind_star_rl_valid).
Time Qed.
Time
Theorem bind_star_expand_r_valid `(r : T -> relation A A T) 
  (v : T) x b o :
  rel_or (pure v) (and_then (bind_star r v) r) x (Val b o) <->
  bind_star r v x (Val b o).
Time Proof.
Time split.
Time -
Time (intros).
Time (apply bind_star_rl_valid).
Time (destruct H; t).
Time *
Time (inversion H; subst).
Time econstructor.
Time *
Time (inversion H; subst).
Time t.
Time (eapply bind_star_r_one_more_valid).
Time {
Time (eapply bind_star_lr_valid; eauto).
Time }
Time {
Time eauto.
Time }
Time -
Time (intros [?| ?| ?]%bind_star_lr_valid).
Time *
Time (left; econstructor).
Time *
Time right.
Time destruct_return.
Time **
Time (do 2 eexists; split).
Time ***
Time (eapply bind_star_rl_valid; eauto).
Time ***
Time eauto.
Time **
Time right.
Time (do 2 eexists; split).
Time ***
Time (eapply bind_star_rl_valid; eauto).
Time ***
Time eauto.
Time *
Time right.
Time **
Time right.
Time (do 2 eexists; split).
Time ***
Time (eapply bind_star_rl_valid; eauto).
Time ***
Time eauto.
Time Qed.
Time
Theorem bind_star_expand_r `(r : T -> relation A A T) 
  (v : T) : pure v + and_then (bind_star r v) r <---> bind_star r v.
Time Proof.
Time (rewrite bind_star_lr).
Time (t; destruct_return; t; induction H; eauto; t; destruct_return; t).
Time Qed.
Time
Theorem bind_star_expand_r_err `(r : T -> relation A A T) 
  (v : T) x :
  rel_or (pure v) (and_then (bind_star r v) r) x Err <-> bind_star r v x Err.
Time Proof.
Time
(split; intros; (eapply requiv_err_elim; [ eassumption |  ]);
  rewrite bind_star_expand_r; eauto).
Time Qed.
Time
Theorem seq_star_ind_l A B T1 (q x : relation A B T1) 
  T2 (p : relation A A T2) :
  q + and_then p (fun _ => x) ---> x ->
  and_then (seq_star p) (fun _ => q) ---> x.
Time Proof.
Time (t; destruct_return; t).
Time *
Time (remember (Val y o1) as ret eqn:Heq ).
Time revert y b o1 Heq H1.
Time (induction H0; intros; t).
Time (edestruct IHseq_star; t).
Time (edestruct (H x0 Err); t).
Time *
Time (remember Err as ret eqn:Heq ).
Time revert Heq.
Time (induction H0; t).
Time *
Time (remember (Val y o1) as ret eqn:Heq ).
Time revert y o1 Heq H1.
Time (induction H0; intros; t).
Time (edestruct IHseq_star; t).
Time Qed.
Time Theorem pure_no_err A T (a : A) (v : T) : pure v a Err -> False.
Time Proof.
Time (inversion 1).
Time Qed.
Time
Theorem bind_with_no_err A B C T S (p : relation A B T)
  (r : T -> relation B C S) a :
  (forall b t, r t b Err -> False) -> and_then p r a Err -> p a Err.
Time Proof.
Time (intros Hno_err).
Time (inversion 1; auto).
Time (exfalso; t).
Time Qed.
Time Hint Unfold test: t.
Time Theorem test_to_id A (P : predicate A) : test P ---> identity.
Time Proof.
Time t.
Time Qed.
Time
Definition pred_and A (P1 P2 : predicate A) : predicate A :=
  fun x => P1 x /\ P2 x.
Time Hint Unfold pred_and: t.
Time
Theorem test_and A (P1 P2 : predicate A) :
  test P1;; test P2 <---> test (pred_and P1 P2).
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time Theorem test_idem A (P : predicate A) : test P;; test P <---> test P.
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time Theorem test_identity A : identity (A:=A) <---> test (fun _ => True).
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time Lemma unit_identity A : identity (A:=A) <---> pure tt.
Time Proof.
Time (t; destruct_return; t).
Time Qed.
Time End TransitionRelations.
Time Module RelationNotations.
Time Delimit Scope relation_scope with rel.
Time Open Scope relation_scope.
Time
Notation "r1 ---> r2" := (rimpl r1 r2)
  (at level 60, no associativity, format "'[hv' r1  '/' ---> '/'  r2 ']'") :
  relation_scope.
Time
Notation "r1 <---> r2" := (requiv r1 r2)
  (at level 60, no associativity, format "'[hv' r1  '/' <---> '/'  r2 ']'") :
  relation_scope.
Time Infix "+" := rel_or : relation_scope.
Time
Notation "p1 ;; p2" := (and_then p1 (fun _ => p2))
  (at level 100, p2  at level 200, only parsing, right associativity) :
  relation_scope.
Time
Notation "x <- p1 ; p2" := (and_then p1 (fun x => p2))
  (at level 20, p1  at level 100, p2  at level 200, right associativity,
   format "'[' x  <-  '[v    ' p1 ']' ; ']'  '/' p2") : relation_scope.
Time
Notation "'let!' x <- p1 ; p2" := (and_then p1 (fun x => p2))
  (at level 20, x pattern, p1  at level 100, p2  at level 200,
   right associativity,
   format "'[' 'let!'  x  <-  '[v    ' p1 ']' ; ']'  '/' p2") :
  relation_scope.
Time
Ltac destruct_return := match goal with
                        | y:Return _ _ |- _ => destruct y
                        end.
Time End RelationNotations.
