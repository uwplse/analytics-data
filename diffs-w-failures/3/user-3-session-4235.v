Time From Coq Require Export Morphisms RelationClasses List Bool Utf8 Setoid.
Time From Coq Require Import Permutation.
Time Set Default Proof Using "Type".
Time Export ListNotations.
Time From Coq.Program Require Export Basics Syntax.
Time #[global]Generalizable Variables all.
Time #[global]Unset Transparent Obligations.
Time Obligation Tactic := idtac.
Time Add Search Blacklist "_obligation_".
Time Section seal.
Time #[local]Set Primitive Projections.
Time Record seal {A} (f : A) :={unseal : A; seal_eq : unseal = f}.
Time End seal.
Time Arguments unseal {_} {_} _ : assert.
Time Arguments seal_eq {_} {_} _ : assert.
Time Class TCNoBackTrack (P : Prop) :={tc_no_backtrack : P}.
Time
Hint Extern 0 (TCNoBackTrack _) => (constructor; apply _):
  typeclass_instances.
Time
Inductive TCIf (P Q R : Prop) : Prop :=
  | TCIf_true : P \226\134\146 Q \226\134\146 TCIf P Q R
  | TCIf_false : R \226\134\146 TCIf P Q R.
Time Existing Class TCIf.
Time
Hint Extern 0 (TCIf _ _ _) => (first
  [ apply TCIf_true; [ apply _ |  ] | apply TCIf_false ]):
  typeclass_instances.
Time Definition tc_opaque {A} (x : A) : A := x.
Time Typeclasses Opaque tc_opaque.
Time Arguments tc_opaque {_} _ /.
Time
Inductive TCOr (P1 P2 : Prop) : Prop :=
  | TCOr_l : P1 \226\134\146 TCOr P1 P2
  | TCOr_r : P2 \226\134\146 TCOr P1 P2.
Time Existing Class TCOr.
Time Existing Instance TCOr_l |9.
Time Existing Instance TCOr_r |10.
Time
Inductive TCAnd (P1 P2 : Prop) : Prop :=
    TCAnd_intro : P1 \226\134\146 P2 \226\134\146 TCAnd P1 P2.
Time Existing Class TCAnd.
Time Existing Instance TCAnd_intro.
Time Inductive TCTrue : Prop :=
         TCTrue_intro : TCTrue.
Time Existing Class TCTrue.
Time Existing Instance TCTrue_intro.
Time
Inductive TCForall {A} (P : A \226\134\146 Prop) : list A \226\134\146 Prop :=
  | TCForall_nil : TCForall P []
  | TCForall_cons : forall x xs, P x \226\134\146 TCForall P xs \226\134\146 TCForall P (x :: xs).
Time Existing Class TCForall.
Time Existing Instance TCForall_nil.
Time Existing Instance TCForall_cons.
Time
Inductive TCForall2 {A} {B} (P : A \226\134\146 B \226\134\146 Prop) : list A \226\134\146 list B \226\134\146 Prop :=
  | TCForall2_nil : TCForall2 P [] []
  | TCForall2_cons :
      forall x y xs ys,
      P x y \226\134\146 TCForall2 P xs ys \226\134\146 TCForall2 P (x :: xs) (y :: ys).
Time Existing Class TCForall2.
Time Existing Instance TCForall2_nil.
Time Existing Instance TCForall2_cons.
Time
Inductive TCElemOf {A} (x : A) : list A \226\134\146 Prop :=
  | TCElemOf_here : forall xs, TCElemOf x (x :: xs)
  | TCElemOf_further : forall y xs, TCElemOf x xs \226\134\146 TCElemOf x (y :: xs).
Time Existing Class TCElemOf.
Time Existing Instance TCElemOf_here.
Time Existing Instance TCElemOf_further.
Time Inductive TCEq {A} (x : A) : A \226\134\146 Prop :=
         TCEq_refl : TCEq x x.
Time Existing Class TCEq.
Time Existing Instance TCEq_refl.
Time
Inductive TCDiag {A} (C : A \226\134\146 Prop) : A \226\134\146 A \226\134\146 Prop :=
    TCDiag_diag : forall x, C x \226\134\146 TCDiag C x x.
Time Existing Class TCDiag.
Time Existing Instance TCDiag_diag.
Time
Definition tc_to_bool (P : Prop) {p : bool}
  `{TCIf P (TCEq p true) (TCEq p false)} : bool := p.
Time Delimit Scope stdpp_scope with stdpp.
Time #[global]Open Scope stdpp_scope.
Time Notation "'True'" := True (format "True") : type_scope.
Time Notation "'False'" := False (format "False") : type_scope.
Time Notation "(=)" := eq (only parsing) : stdpp_scope.
Time Notation "( x =)" := (eq x) (only parsing) : stdpp_scope.
Time Notation "(= x )" := (\206\187 y, eq y x) (only parsing) : stdpp_scope.
Time Notation "(\226\137\160)" := (\206\187 x y, x \226\137\160 y) (only parsing) : stdpp_scope.
Time Notation "( x \226\137\160)" := (\206\187 y, x \226\137\160 y) (only parsing) : stdpp_scope.
Time Notation "(\226\137\160 x )" := (\206\187 y, y \226\137\160 x) (only parsing) : stdpp_scope.
Time
Infix "=@{ A }" := (@eq A) (at level 70, only parsing, no associativity) :
stdpp_scope.
Time Notation "(=@{ A } )" := (@eq A) (only parsing) : stdpp_scope.
Time
Notation "(\226\137\160@{ A } )" := (\206\187 X Y, \194\172 X =@{ A} Y) (only parsing) : stdpp_scope.
Time
Notation "X \226\137\160@{ A } Y" := (\194\172 X =@{ A} Y)
  (at level 70, only parsing, no associativity) : stdpp_scope.
Time Hint Extern 0 (_ = _) => reflexivity: core.
Time Hint Extern 100 (_ \226\137\160 _) => discriminate: core.
Time Instance: (\226\136\128 A, PreOrder (=@{A} )).
Time Proof.
Time (split; repeat intro; congruence).
Time Qed.
Time Class Equiv A :=
         equiv : relation A.
Time Infix "\226\137\161" := equiv (at level 70, no associativity) : stdpp_scope.
Time
Infix "\226\137\161@{ A }" := (@equiv A _) (at level 70, only parsing, no associativity)
: stdpp_scope.
Time Notation "(\226\137\161)" := equiv (only parsing) : stdpp_scope.
Time Notation "( X \226\137\161)" := (equiv X) (only parsing) : stdpp_scope.
Time Notation "(\226\137\161 X )" := (\206\187 Y, Y \226\137\161 X) (only parsing) : stdpp_scope.
Time Notation "(\226\137\162)" := (\206\187 X Y, \194\172 X \226\137\161 Y) (only parsing) : stdpp_scope.
Time
Notation "X \226\137\162 Y" := (\194\172 X \226\137\161 Y) (at level 70, no associativity) : stdpp_scope.
Time Notation "( X \226\137\162)" := (\206\187 Y, X \226\137\162 Y) (only parsing) : stdpp_scope.
Time Notation "(\226\137\162 X )" := (\206\187 Y, Y \226\137\162 X) (only parsing) : stdpp_scope.
Time Notation "(\226\137\161@{ A } )" := (@equiv A _) (only parsing) : stdpp_scope.
Time
Notation "(\226\137\162@{ A } )" := (\206\187 X Y, \194\172 X \226\137\161@{ A} Y) (only parsing) : stdpp_scope.
Time
Notation "X \226\137\162@{ A } Y" := (\194\172 X \226\137\161@{ A} Y)
  (at level 70, only parsing, no associativity) : stdpp_scope.
Time
Class LeibnizEquiv A `{Equiv A} :=
    leibniz_equiv : forall x y, x \226\137\161 y \226\134\146 x = y.
Time Hint Mode LeibnizEquiv ! -: typeclass_instances.
Time
Lemma leibniz_equiv_iff `{LeibnizEquiv A} `{!Reflexive (\226\137\161@{A} )} 
  (x y : A) : x \226\137\161 y \226\134\148 x = y.
Time Proof.
Time split.
Time (apply leibniz_equiv).
Time (intros ->; reflexivity).
Time Qed.
Time
Ltac
 fold_leibniz :=
  repeat
   match goal with
   | H:context [ _ \226\137\161@{ ?A} _ ]
     |- _ => setoid_rewrite (leibniz_equiv_iff (A:=A)) in H
   | |- context [ _ \226\137\161@{ ?A} _ ] => setoid_rewrite (leibniz_equiv_iff (A:=A))
   end.
Time
Ltac
 unfold_leibniz :=
  repeat
   match goal with
   | H:context [ _ =@{ ?A} _ ]
     |- _ => setoid_rewrite  <- (leibniz_equiv_iff (A:=A)) in H
   | |- context [ _ =@{ ?A} _ ] => setoid_rewrite  <-
     (leibniz_equiv_iff (A:=A))
   end.
Time Definition equivL {A} : Equiv A := (=).
Time Instance: (Params (@equiv) 2) := { }.
Time
Instance equiv_default_relation  `{Equiv A}: (DefaultRelation (\226\137\161)) |3 := { }.
Time Hint Extern 0 (_ \226\137\161 _) => reflexivity: core.
Time Hint Extern 0 (_ \226\137\161 _) => (symmetry; assumption): core.
Time Class Decision (P : Prop) :=
         decide : {P} + {\194\172 P}.
Time Hint Mode Decision !: typeclass_instances.
Time Arguments decide _ {_} : simpl never,  assert.
Time
Class RelDecision {A} {B} (R : A \226\134\146 B \226\134\146 Prop) :=
    decide_rel :> forall x y, Decision (R x y).
Time Hint Mode RelDecision ! ! !: typeclass_instances.
Time Arguments decide_rel {_} {_} _ {_} _ _ : simpl never,  assert.
Time Notation EqDecision A:= (RelDecision (=@{A} )).
Time Class Inhabited (A : Type) : Type := populate {inhabitant : A}.
Time Hint Mode Inhabited !: typeclass_instances.
Time Arguments populate {_} _ : assert.
Time
Class ProofIrrel (A : Type) : Prop :=
    proof_irrel : forall x y : A, x = y.
Time Hint Mode ProofIrrel !: typeclass_instances.
Time
Class Inj {A} {B} (R : relation A) (S : relation B) (f : A \226\134\146 B) : Prop :=
    inj : forall x y, S (f x) (f y) \226\134\146 R x y.
Time
Class Inj2 {A} {B} {C} (R1 : relation A) (R2 : relation B) 
(S : relation C) (f : A \226\134\146 B \226\134\146 C) : Prop :=
    inj2 : forall x1 x2 y1 y2, S (f x1 x2) (f y1 y2) \226\134\146 R1 x1 y1 \226\136\167 R2 x2 y2.
Time
Class Cancel {A} {B} (S : relation B) (f : A \226\134\146 B) (g : B \226\134\146 A) : Prop :=
    cancel : \226\136\128 x, S (f (g x)) x.
Time
Class Surj {A} {B} (R : relation B) (f : A \226\134\146 B) :=
    surj : forall y, \226\136\131 x, R (f x) y.
Time
Class IdemP {A} (R : relation A) (f : A \226\134\146 A \226\134\146 A) : Prop :=
    idemp : forall x, R (f x x) x.
Time
Class Comm {A} {B} (R : relation A) (f : B \226\134\146 B \226\134\146 A) : Prop :=
    comm : forall x y, R (f x y) (f y x).
Time
Class LeftId {A} (R : relation A) (i : A) (f : A \226\134\146 A \226\134\146 A) : Prop :=
    left_id : forall x, R (f i x) x.
Time
Class RightId {A} (R : relation A) (i : A) (f : A \226\134\146 A \226\134\146 A) : Prop :=
    right_id : forall x, R (f x i) x.
Time
Class Assoc {A} (R : relation A) (f : A \226\134\146 A \226\134\146 A) : Prop :=
    assoc : forall x y z, R (f x (f y z)) (f (f x y) z).
Time
Class LeftAbsorb {A} (R : relation A) (i : A) (f : A \226\134\146 A \226\134\146 A) : Prop :=
    left_absorb : forall x, R (f i x) i.
Time
Class RightAbsorb {A} (R : relation A) (i : A) (f : A \226\134\146 A \226\134\146 A) : Prop :=
    right_absorb : forall x, R (f x i) i.
Time
Class AntiSymm {A} (R S : relation A) : Prop :=
    anti_symm : forall x y, S x y \226\134\146 S y x \226\134\146 R x y.
Time Class Total {A} (R : relation A) :=
         total : forall x y, R x y \226\136\168 R y x.
Time
Class Trichotomy {A} (R : relation A) :=
    trichotomy : forall x y, R x y \226\136\168 x = y \226\136\168 R y x.
Time
Class TrichotomyT {A} (R : relation A) :=
    trichotomyT : forall x y, {R x y} + {x = y} + {R y x}.
Time Notation Involutive R f:= (Cancel R f f).
Time
Lemma involutive {A} {R : relation A} (f : A \226\134\146 A) 
  `{Involutive R f} x : R (f (f x)) x.
Time Proof.
Time auto.
Time Qed.
Time Arguments irreflexivity {_} _ {_} _ _ : assert.
Time Arguments inj {_} {_} {_} {_} _ {_} _ _ _ : assert.
Time Arguments inj2 {_} {_} {_} {_} {_} {_} _ {_} _ _ _ _ _ : assert.
Time Arguments cancel {_} {_} {_} _ _ {_} _ : assert.
Time Arguments surj {_} {_} {_} _ {_} _ : assert.
Time Arguments idemp {_} {_} _ {_} _ : assert.
Time Arguments comm {_} {_} {_} _ {_} _ _ : assert.
Time Arguments left_id {_} {_} _ _ {_} _ : assert.
Time Arguments right_id {_} {_} _ _ {_} _ : assert.
Time Arguments assoc {_} {_} _ {_} _ _ _ : assert.
Time Arguments left_absorb {_} {_} _ _ {_} _ : assert.
Time Arguments right_absorb {_} {_} _ _ {_} _ : assert.
Time Arguments anti_symm {_} {_} _ {_} _ _ _ _ : assert.
Time Arguments total {_} _ {_} _ _ : assert.
Time Arguments trichotomy {_} _ {_} _ _ : assert.
Time Arguments trichotomyT {_} _ {_} _ _ : assert.
Time
Lemma not_symmetry `{R : relation A} `{!Symmetric R} x y : \194\172 R x y \226\134\146 \194\172 R y x.
Time Proof.
Time intuition.
Time Qed.
Time
Lemma symmetry_iff `(R : relation A) `{!Symmetric R} x y : R x y \226\134\148 R y x.
Time Proof.
Time intuition.
Time Qed.
Time Lemma not_inj `{Inj A B R R' f} x y : \194\172 R x y \226\134\146 \194\172 R' (f x) (f y).
Time Proof.
Time intuition.
Time Qed.
Time
Lemma not_inj2_1 `{Inj2 A B C R R' R'' f} x1 x2 y1 
  y2 : \194\172 R x1 x2 \226\134\146 \194\172 R'' (f x1 y1) (f x2 y2).
Time Proof.
Time (intros HR HR'').
Time (destruct (inj2 f x1 y1 x2 y2); auto).
Time Qed.
Time
Lemma not_inj2_2 `{Inj2 A B C R R' R'' f} x1 x2 y1 
  y2 : \194\172 R' y1 y2 \226\134\146 \194\172 R'' (f x1 y1) (f x2 y2).
Time Proof.
Time (intros HR' HR'').
Time (destruct (inj2 f x1 y1 x2 y2); auto).
Time Qed.
Time
Lemma inj_iff {A} {B} {R : relation A} {S : relation B} 
  (f : A \226\134\146 B) `{!Inj R S f} `{!Proper (R ==> S) f} 
  x y : S (f x) (f y) \226\134\148 R x y.
Time Proof.
Time firstorder.
Time Qed.
Time
Instance inj2_inj_1  `{Inj2 A B C R1 R2 R3 f} y: (Inj R1 R3 (\206\187 x, f x y)).
Time Proof.
Time (repeat intro; edestruct (inj2 f); eauto).
Time Qed.
Time Instance inj2_inj_2  `{Inj2 A B C R1 R2 R3 f} x: (Inj R2 R3 (f x)).
Time Proof.
Time (repeat intro; edestruct (inj2 f); eauto).
Time Qed.
Time
Lemma cancel_inj `{Cancel A B R1 f g} `{!Equivalence R1}
  `{!Proper (R2 ==> R1) f} : Inj R1 R2 g.
Time Proof.
Time (intros x y E).
Time (rewrite <- (cancel f g x), <- (cancel f g y), E).
Time reflexivity.
Time Qed.
Time Lemma cancel_surj `{Cancel A B R1 f g} : Surj R1 f.
Time Proof.
Time (intros y).
Time exists (g y).
Time auto.
Time Qed.
Time Lemma idemp_L {A} f `{!@IdemP A (=) f} x : f x x = x.
Time Proof.
Time auto.
Time Qed.
Time Lemma comm_L {A} {B} f `{!@Comm A B (=) f} x y : f x y = f y x.
Time Proof.
Time auto.
Time Qed.
Time Lemma left_id_L {A} i f `{!@LeftId A (=) i f} x : f i x = x.
Time Proof.
Time auto.
Time Qed.
Time Lemma right_id_L {A} i f `{!@RightId A (=) i f} x : f x i = x.
Time Proof.
Time auto.
Time Qed.
Time
Lemma assoc_L {A} f `{!@Assoc A (=) f} x y z : f x (f y z) = f (f x y) z.
Time Proof.
Time auto.
Time Qed.
Time Lemma left_absorb_L {A} i f `{!@LeftAbsorb A (=) i f} x : f i x = i.
Time Proof.
Time auto.
Time Qed.
Time Lemma right_absorb_L {A} i f `{!@RightAbsorb A (=) i f} x : f x i = i.
Time Proof.
Time auto.
Time Qed.
Time
Definition strict {A} (R : relation A) : relation A := \206\187 X Y, R X Y \226\136\167 \194\172 R Y X.
Time Instance: (Params (@strict) 2) := { }.
Time
Class PartialOrder {A} (R : relation A) : Prop :={
 partial_order_pre :> PreOrder R;
 partial_order_anti_symm :> AntiSymm (=) R}.
Time
Class TotalOrder {A} (R : relation A) : Prop :={total_order_partial :>
                                                 PartialOrder R;
                                                total_order_trichotomy :>
                                                 Trichotomy (strict R)}.
Time Notation "(\226\136\167)" := and (only parsing) : stdpp_scope.
Time Notation "( A \226\136\167)" := (and A) (only parsing) : stdpp_scope.
Time Notation "(\226\136\167 B )" := (\206\187 A, A \226\136\167 B) (only parsing) : stdpp_scope.
Time Notation "(\226\136\168)" := or (only parsing) : stdpp_scope.
Time Notation "( A \226\136\168)" := (or A) (only parsing) : stdpp_scope.
Time Notation "(\226\136\168 B )" := (\206\187 A, A \226\136\168 B) (only parsing) : stdpp_scope.
Time Notation "(\226\134\148)" := iff (only parsing) : stdpp_scope.
Time Notation "( A \226\134\148)" := (iff A) (only parsing) : stdpp_scope.
Time Notation "(\226\134\148 B )" := (\206\187 A, A \226\134\148 B) (only parsing) : stdpp_scope.
Time Hint Extern 0 (_ \226\134\148 _) => reflexivity: core.
Time Hint Extern 0 (_ \226\134\148 _) => (symmetry; assumption): core.
Time Lemma or_l P Q : \194\172 Q \226\134\146 P \226\136\168 Q \226\134\148 P.
Time Proof.
Time tauto.
Time Qed.
Time Lemma or_r P Q : \194\172 P \226\134\146 P \226\136\168 Q \226\134\148 Q.
Time Proof.
Time tauto.
Time Qed.
Time Lemma and_wlog_l (P Q : Prop) : (Q \226\134\146 P) \226\134\146 Q \226\134\146 P \226\136\167 Q.
Time Proof.
Time tauto.
Time Qed.
Time Lemma and_wlog_r (P Q : Prop) : P \226\134\146 (P \226\134\146 Q) \226\134\146 P \226\136\167 Q.
Time Proof.
Time tauto.
Time Qed.
Time Lemma impl_transitive (P Q R : Prop) : (P \226\134\146 Q) \226\134\146 (Q \226\134\146 R) \226\134\146 P \226\134\146 R.
Time Proof.
Time tauto.
Time Qed.
Time
Lemma forall_proper {A} (P Q : A \226\134\146 Prop) :
  (\226\136\128 x, P x \226\134\148 Q x) \226\134\146 (\226\136\128 x, P x) \226\134\148 (\226\136\128 x, Q x).
Time Proof.
Time firstorder.
Time Qed.
Time
Lemma exist_proper {A} (P Q : A \226\134\146 Prop) :
  (\226\136\128 x, P x \226\134\148 Q x) \226\134\146 (\226\136\131 x, P x) \226\134\148 (\226\136\131 x, Q x).
Time Proof.
Time firstorder.
Time Qed.
Time Instance: (Comm (\226\134\148) (=@{A} )).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (Comm (\226\134\148) (\206\187 x y, y =@{ A} x)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (Comm (\226\134\148) (\226\134\148)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (Comm (\226\134\148) (\226\136\167)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (Assoc (\226\134\148) (\226\136\167)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (IdemP (\226\134\148) (\226\136\167)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (Comm (\226\134\148) (\226\136\168)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (Assoc (\226\134\148) (\226\136\168)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (IdemP (\226\134\148) (\226\136\168)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (LeftId (\226\134\148) True (\226\136\167)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (RightId (\226\134\148) True (\226\136\167)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (LeftAbsorb (\226\134\148) False (\226\136\167)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (RightAbsorb (\226\134\148) False (\226\136\167)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (LeftId (\226\134\148) False (\226\136\168)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (RightId (\226\134\148) False (\226\136\168)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (LeftAbsorb (\226\134\148) True (\226\136\168)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (RightAbsorb (\226\134\148) True (\226\136\168)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance: (LeftId (\226\134\148) True impl).
Time Proof.
Time (unfold impl).
Time (red; intuition).
Time Qed.
Time Instance: (RightAbsorb (\226\134\148) True impl).
Time Proof.
Time (unfold impl).
Time (red; intuition).
Time Qed.
Time Notation "(\226\134\146)" := (\206\187 A B, A \226\134\146 B) (only parsing) : stdpp_scope.
Time Notation "( A \226\134\146)" := (\206\187 B, A \226\134\146 B) (only parsing) : stdpp_scope.
Time Notation "(\226\134\146 B )" := (\206\187 A, A \226\134\146 B) (only parsing) : stdpp_scope.
Time
Notation "t $ r" := (t r) (at level 65, right associativity, only parsing) :
  stdpp_scope.
Time Notation "($)" := (\206\187 f x, f x) (only parsing) : stdpp_scope.
Time Notation "($ x )" := (\206\187 f, f x) (only parsing) : stdpp_scope.
Time Infix "\226\136\152" := compose : stdpp_scope.
Time Notation "(\226\136\152)" := compose (only parsing) : stdpp_scope.
Time Notation "( f \226\136\152)" := (compose f) (only parsing) : stdpp_scope.
Time Notation "(\226\136\152 f )" := (\206\187 g, compose g f) (only parsing) : stdpp_scope.
Time
Instance impl_inhabited  {A} `{Inhabited B}: (Inhabited (A \226\134\146 B)) :=
 (populate (\206\187 _, inhabitant)).
Time Arguments id _ _ / : assert.
Time Arguments compose _ _ _ _ _ _ / : assert.
Time Arguments flip _ _ _ _ _ _ / : assert.
Time Arguments const _ _ _ _ / : assert.
Time Typeclasses Transparent id compose flip const.
Time
Definition fun_map {A} {A'} {B} {B'} (f : A' \226\134\146 A) 
  (g : B \226\134\146 B') (h : A \226\134\146 B) : A' \226\134\146 B' := g \226\136\152 h \226\136\152 f.
Time
Instance const_proper  `{R1 : relation A} `{R2 : relation B} 
 (x : B): (Reflexive R2 \226\134\146 Proper (R1 ==> R2) (\206\187 _, x)).
Time Proof.
Time (intros ? y1 y2; reflexivity).
Time Qed.
Time Instance id_inj  {A}: (Inj (=) (=) (@id A)).
Time Proof.
Time (intros ? ?; auto).
Time Qed.
Time
Instance compose_inj  {A} {B} {C} R1 R2 R3 (f : A \226\134\146 B) 
 (g : B \226\134\146 C): (Inj R1 R2 f \226\134\146 Inj R2 R3 g \226\134\146 Inj R1 R3 (g \226\136\152 f)).
Time Proof.
Time (red; intuition).
Time Qed.
Time Instance id_surj  {A}: (Surj (=) (@id A)).
Time Proof.
Time (intros y; exists y; reflexivity).
Time Qed.
Time
Instance compose_surj  {A} {B} {C} R (f : A \226\134\146 B) (g : B \226\134\146 C):
 (Surj (=) f \226\134\146 Surj R g \226\134\146 Surj R (g \226\136\152 f)).
Time Proof.
Time (intros ? ? x).
Time (unfold compose).
Time (destruct (surj g x) as [y ?]).
Time (destruct (surj f y) as [z ?]).
Time exists z.
Time congruence.
Time Qed.
Time Instance id_comm  {A} {B} (x : B): (Comm (=) (\206\187 _ _ : A, x)).
Time Proof.
Time (intros ?; reflexivity).
Time Qed.
Time Instance id_assoc  {A} (x : A): (Assoc (=) (\206\187 _ _ : A, x)).
Time Proof.
Time (intros ? ? ?; reflexivity).
Time Qed.
Time Instance const1_assoc  {A}: (Assoc (=) (\206\187 x _ : A, x)).
Time Proof.
Time (intros ? ? ?; reflexivity).
Time Qed.
Time Instance const2_assoc  {A}: (Assoc (=) (\206\187 _ x : A, x)).
Time Proof.
Time (intros ? ? ?; reflexivity).
Time Qed.
Time Instance const1_idemp  {A}: (IdemP (=) (\206\187 x _ : A, x)).
Time Proof.
Time (intros ?; reflexivity).
Time Qed.
Time Instance const2_idemp  {A}: (IdemP (=) (\206\187 _ x : A, x)).
Time Proof.
Time (intros ?; reflexivity).
Time Qed.
Time Instance list_inhabited  {A}: (Inhabited (list A)) := (populate []).
Time
Definition zip_with {A} {B} {C} (f : A \226\134\146 B \226\134\146 C) : 
  list A \226\134\146 list B \226\134\146 list C :=
  fix go l1 l2 :=
    match l1, l2 with
    | x1 :: l1, x2 :: l2 => f x1 x2 :: go l1 l2
    | _, _ => []
    end.
Time Notation zip := (zip_with pair).
Time Coercion Is_true : bool >-> Sortclass.
Time Hint Unfold Is_true: core.
Time Hint Immediate Is_true_eq_left: core.
Time Hint Resolve orb_prop_intro andb_prop_intro: core.
Time Notation "(&&)" := andb (only parsing).
Time Notation "(||)" := orb (only parsing).
Time Infix "&&*" := (zip_with (&&)) (at level 40).
Time Infix "||*" := (zip_with (||)) (at level 50).
Time Instance bool_inhabated : (Inhabited bool) := (populate true).
Time Definition bool_le (\206\1781 \206\1782 : bool) : Prop := negb \206\1781 || \206\1782.
Time Infix "=.>" := bool_le (at level 70).
Time Infix "=.>*" := (Forall2 bool_le) (at level 70).
Time Instance: (PartialOrder bool_le).
Time Proof.
Time (repeat split; repeat intros [| ]; compute; tauto).
Time Qed.
Time Lemma andb_True b1 b2 : b1 && b2 \226\134\148 b1 \226\136\167 b2.
Time Proof.
Time (destruct b1, b2; simpl; tauto).
Time Qed.
Time Lemma orb_True b1 b2 : b1 || b2 \226\134\148 b1 \226\136\168 b2.
Time Proof.
Time (destruct b1, b2; simpl; tauto).
Time Qed.
Time Lemma negb_True b : negb b \226\134\148 \194\172 b.
Time Proof.
Time (destruct b; simpl; tauto).
Time Qed.
Time Lemma Is_true_false (b : bool) : b = false \226\134\146 \194\172 b.
Time Proof.
Time now intros -> ?.
Time Qed.
Time Instance unit_equiv : (Equiv unit) := (\206\187 _ _, True).
Time Instance unit_equivalence : (Equivalence (\226\137\161@{unit} )).
Time Proof.
Time (repeat split).
Time Qed.
Time Instance unit_leibniz : (LeibnizEquiv unit).
Time Proof.
Time (intros [] []; reflexivity).
Time Qed.
Time Instance unit_inhabited : (Inhabited unit) := (populate ()).
Time Instance Empty_set_equiv : (Equiv Empty_set) := (\206\187 _ _, True).
Time Instance Empty_set_equivalence : (Equivalence (\226\137\161@{Empty_set} )).
Time Proof.
Time (repeat split).
Time Qed.
Time Instance Empty_set_leibniz : (LeibnizEquiv Empty_set).
Time Proof.
Time (intros [] []; reflexivity).
Time Qed.
Time Notation "( x ,)" := (pair x) (only parsing) : stdpp_scope.
Time Notation "(, y )" := (\206\187 x, (x, y)) (only parsing) : stdpp_scope.
Time
Notation "p .1" := (fst p) (at level 2, left associativity, format "p .1").
Time
Notation "p .2" := (snd p) (at level 2, left associativity, format "p .2").
Time Instance: (Params (@pair) 2) := { }.
Time Instance: (Params (@fst) 2) := { }.
Time Instance: (Params (@snd) 2) := { }.
Time Notation curry := prod_curry.
Time Notation uncurry := prod_uncurry.
Time
Definition curry3 {A} {B} {C} {D} (f : A \226\134\146 B \226\134\146 C \226\134\146 D) 
  (p : A * B * C) : D := let '(a, b, c) := p in f a b c.
Time
Definition curry4 {A} {B} {C} {D} {E} (f : A \226\134\146 B \226\134\146 C \226\134\146 D \226\134\146 E)
  (p : A * B * C * D) : E := let '(a, b, c, d) := p in f a b c d.
Time
Definition uncurry3 {A} {B} {C} {D} (f : A * B * C \226\134\146 D) 
  (a : A) (b : B) (c : C) : D := f (a, b, c).
Time
Definition uncurry4 {A} {B} {C} {D} {E} (f : A * B * C * D \226\134\146 E) 
  (a : A) (b : B) (c : C) (d : D) : E := f (a, b, c, d).
Time
Definition prod_map {A} {A'} {B} {B'} (f : A \226\134\146 A') 
  (g : B \226\134\146 B') (p : A * B) : A' * B' := (f p.1, g p.2).
Time Arguments prod_map {_} {_} {_} {_} _ _ !_ / : assert.
Time
Definition prod_zip {A} {A'} {A''} {B} {B'} {B''} 
  (f : A \226\134\146 A' \226\134\146 A'') (g : B \226\134\146 B' \226\134\146 B'') (p : A * B) 
  (q : A' * B') : A'' * B'' := (f p.1 q.1, g p.2 q.2).
Time Arguments prod_zip {_} {_} {_} {_} {_} {_} _ _ !_ !_ / : assert.
Time
Instance prod_inhabited  {A} {B} (iA : Inhabited A) 
 (iB : Inhabited B): (Inhabited (A * B)) :=
 match iA, iB with
 | populate x, populate y => populate (x, y)
 end.
Time Instance pair_inj : (Inj2 (=) (=) (=) (@pair A B)).
Time Proof.
Time (injection 1; auto).
Time Qed.
Time
Instance prod_map_inj  {A} {A'} {B} {B'} (f : A \226\134\146 A') 
 (g : B \226\134\146 B'): (Inj (=) (=) f \226\134\146 Inj (=) (=) g \226\134\146 Inj (=) (=) (prod_map f g)).
Time Proof.
Time
(intros ? ? [? ?] [? ?] ?; simpl in *; f_equal;
  [ apply (inj f) | apply (inj g) ]; congruence).
Time Qed.
Time
Definition prod_relation {A} {B} (R1 : relation A) 
  (R2 : relation B) : relation (A * B) := \206\187 x y, R1 x.1 y.1 \226\136\167 R2 x.2 y.2.
Time Section prod_relation.
Time Context `{R1 : relation A} `{R2 : relation B}.
Time #[global]
Instance prod_relation_refl :
 (Reflexive R1 \226\134\146 Reflexive R2 \226\134\146 Reflexive (prod_relation R1 R2)).
Time Proof.
Time firstorder  eauto.
Time Qed.
Time #[global]
Instance prod_relation_sym :
 (Symmetric R1 \226\134\146 Symmetric R2 \226\134\146 Symmetric (prod_relation R1 R2)).
Time Proof.
Time firstorder  eauto.
Time Qed.
Time #[global]
Instance prod_relation_trans :
 (Transitive R1 \226\134\146 Transitive R2 \226\134\146 Transitive (prod_relation R1 R2)).
Time Proof.
Time firstorder  eauto.
Time Qed.
Time #[global]
Instance prod_relation_equiv :
 (Equivalence R1 \226\134\146 Equivalence R2 \226\134\146 Equivalence (prod_relation R1 R2)).
Time Proof.
Time (split; apply _).
Time Qed.
Time #[global]
Instance pair_proper' : (Proper (R1 ==> R2 ==> prod_relation R1 R2) pair).
Time Proof.
Time firstorder  eauto.
Time Qed.
Time #[global]Instance pair_inj' : (Inj2 R1 R2 (prod_relation R1 R2) pair).
Time Proof.
Time (inversion_clear 1; eauto).
Time Qed.
Time #[global]
Instance fst_proper' : (Proper (prod_relation R1 R2 ==> R1) fst).
Time Proof.
Time firstorder  eauto.
Time Qed.
Time #[global]
Instance snd_proper' : (Proper (prod_relation R1 R2 ==> R2) snd).
Time Proof.
Time firstorder  eauto.
Time Qed.
Time End prod_relation.
Time
Instance prod_equiv  `{Equiv A} `{Equiv B}: (Equiv (A * B)) :=
 (prod_relation (\226\137\161) (\226\137\161)).
Time
Instance pair_proper  `{Equiv A} `{Equiv B}:
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@pair A B)) := _.
Time
Instance pair_equiv_inj  `{Equiv A} `{Equiv B}:
 (Inj2 (\226\137\161) (\226\137\161) (\226\137\161) (@pair A B)) := _.
Time
Instance fst_proper  `{Equiv A} `{Equiv B}: (Proper ((\226\137\161) ==> (\226\137\161)) (@fst A B))
 := _.
Time
Instance snd_proper  `{Equiv A} `{Equiv B}: (Proper ((\226\137\161) ==> (\226\137\161)) (@snd A B))
 := _.
Time Typeclasses Opaque prod_equiv.
Time
Instance prod_leibniz  `{LeibnizEquiv A} `{LeibnizEquiv B}:
 (LeibnizEquiv (A * B)).
Time Proof.
Time (intros [? ?] [? ?] [? ?]; f_equal; apply leibniz_equiv; auto).
Time Qed.
Time
Definition sum_map {A} {A'} {B} {B'} (f : A \226\134\146 A') 
  (g : B \226\134\146 B') (xy : A + B) : A' + B' :=
  match xy with
  | inl x => inl (f x)
  | inr y => inr (g y)
  end.
Time Arguments sum_map {_} {_} {_} {_} _ _ !_ / : assert.
Time
Instance sum_inhabited_l  {A} {B} (iA : Inhabited A): 
 (Inhabited (A + B)) := match iA with
                        | populate x => populate (inl x)
                        end.
Time
Instance sum_inhabited_r  {A} {B} (iB : Inhabited A): 
 (Inhabited (A + B)) := match iB with
                        | populate y => populate (inl y)
                        end.
Time Instance inl_inj : (Inj (=) (=) (@inl A B)).
Time Proof.
Time (injection 1; auto).
Time Qed.
Time Instance inr_inj : (Inj (=) (=) (@inr A B)).
Time Proof.
Time (injection 1; auto).
Time Qed.
Time
Instance sum_map_inj  {A} {A'} {B} {B'} (f : A \226\134\146 A') 
 (g : B \226\134\146 B'): (Inj (=) (=) f \226\134\146 Inj (=) (=) g \226\134\146 Inj (=) (=) (sum_map f g)).
Time Proof.
Time (intros ? ? [?| ?] [?| ?] [=]; f_equal; apply (inj _); auto).
Time Qed.
Time
Inductive sum_relation {A} {B} (R1 : relation A) (R2 : relation B) :
relation (A + B) :=
  | inl_related :
      forall x1 x2, R1 x1 x2 \226\134\146 sum_relation R1 R2 (inl x1) (inl x2)
  | inr_related :
      forall y1 y2, R2 y1 y2 \226\134\146 sum_relation R1 R2 (inr y1) (inr y2).
Time Section sum_relation.
Time Context `{R1 : relation A} `{R2 : relation B}.
Time #[global]
Instance sum_relation_refl :
 (Reflexive R1 \226\134\146 Reflexive R2 \226\134\146 Reflexive (sum_relation R1 R2)).
Time Proof.
Time (intros ? ? [?| ?]; constructor; reflexivity).
Time Qed.
Time #[global]
Instance sum_relation_sym :
 (Symmetric R1 \226\134\146 Symmetric R2 \226\134\146 Symmetric (sum_relation R1 R2)).
Time Proof.
Time (destruct 3; constructor; eauto).
Time Qed.
Time #[global]
Instance sum_relation_trans :
 (Transitive R1 \226\134\146 Transitive R2 \226\134\146 Transitive (sum_relation R1 R2)).
Time Proof.
Time (destruct 3; inversion_clear 1; constructor; eauto).
Time Qed.
Time #[global]
Instance sum_relation_equiv :
 (Equivalence R1 \226\134\146 Equivalence R2 \226\134\146 Equivalence (sum_relation R1 R2)).
Time Proof.
Time (split; apply _).
Time Qed.
Time #[global]
Instance inl_proper' : (Proper (R1 ==> sum_relation R1 R2) inl).
Time Proof.
Time (constructor; auto).
Time Qed.
Time #[global]
Instance inr_proper' : (Proper (R2 ==> sum_relation R1 R2) inr).
Time Proof.
Time (constructor; auto).
Time Qed.
Time #[global]Instance inl_inj' : (Inj R1 (sum_relation R1 R2) inl).
Time Proof.
Time (inversion_clear 1; auto).
Time Qed.
Time #[global]Instance inr_inj' : (Inj R2 (sum_relation R1 R2) inr).
Time Proof.
Time (inversion_clear 1; auto).
Time Qed.
Time End sum_relation.
Time
Instance sum_equiv  `{Equiv A} `{Equiv B}: (Equiv (A + B)) :=
 (sum_relation (\226\137\161) (\226\137\161)).
Time
Instance inl_proper  `{Equiv A} `{Equiv B}: (Proper ((\226\137\161) ==> (\226\137\161)) (@inl A B))
 := _.
Time
Instance inr_proper  `{Equiv A} `{Equiv B}: (Proper ((\226\137\161) ==> (\226\137\161)) (@inr A B))
 := _.
Time
Instance inl_equiv_inj  `{Equiv A} `{Equiv B}: (Inj (\226\137\161) (\226\137\161) (@inl A B)) := _.
Time
Instance inr_equiv_inj  `{Equiv A} `{Equiv B}: (Inj (\226\137\161) (\226\137\161) (@inr A B)) := _.
Time Typeclasses Opaque sum_equiv.
Time
Instance option_inhabited  {A}: (Inhabited (option A)) := (populate None).
Time Arguments existT {_} {_} _ _ : assert.
Time Arguments projT1 {_} {_} _ : assert.
Time Arguments projT2 {_} {_} _ : assert.
Time Arguments exist {_} _ _ _ : assert.
Time Arguments proj1_sig {_} {_} _ : assert.
Time Arguments proj2_sig {_} {_} _ : assert.
Time Notation "x \226\134\190 p" := (exist _ x p) (at level 20) : stdpp_scope.
Time
Notation "` x" := (proj1_sig x) (at level 10, format "` x") : stdpp_scope.
Time
Lemma proj1_sig_inj {A} (P : A \226\134\146 Prop) x (Px : P x) 
  y (Py : P y) : x \226\134\190 Px = y \226\134\190 Py \226\134\146 x = y.
Time Proof.
Time (injection 1; trivial).
Time Qed.
Time Section sig_map.
Time
Context `{P : A \226\134\146 Prop} `{Q : B \226\134\146 Prop} (f : A \226\134\146 B) (Hf : \226\136\128 x, P x \226\134\146 Q (f x)).
Time Definition sig_map (x : sig P) : sig Q := f (`x) \226\134\190 Hf _ (proj2_sig x).
Time #[global]
Instance sig_map_inj :
 ((\226\136\128 x, ProofIrrel (P x)) \226\134\146 Inj (=) (=) f \226\134\146 Inj (=) (=) sig_map).
Time Proof.
Time (intros ? ? [x Hx] [y Hy]).
Time injection 1.
Time (intros Hxy).
Time (apply (inj f) in Hxy; subst).
Time (rewrite (proof_irrel _ Hy)).
Time auto.
Time Qed.
Time End sig_map.
Time Arguments sig_map _ _ _ _ _ _ !_ / : assert.
Time
Definition proj1_ex {P : Prop} {Q : P \226\134\146 Prop} (p : \226\136\131 x, Q x) : P :=
  let 'ex_intro _ x _ := p in x.
Time
Definition proj2_ex {P : Prop} {Q : P \226\134\146 Prop} (p : \226\136\131 x, Q x) :
  Q (proj1_ex p) := let 'ex_intro _ x H := p in H.
Time Class Empty A :=
         empty : A.
Time Hint Mode Empty !: typeclass_instances.
Time Notation "\226\136\133" := empty (format "\226\136\133") : stdpp_scope.
Time Instance empty_inhabited  `(Empty A): (Inhabited A) := (populate \226\136\133).
Time Class Union A :=
         union : A \226\134\146 A \226\134\146 A.
Time Hint Mode Union !: typeclass_instances.
Time Instance: (Params (@union) 2) := { }.
Time Infix "\226\136\170" := union (at level 50, left associativity) : stdpp_scope.
Time Notation "(\226\136\170)" := union (only parsing) : stdpp_scope.
Time Notation "( x \226\136\170)" := (union x) (only parsing) : stdpp_scope.
Time Notation "(\226\136\170 x )" := (\206\187 y, union y x) (only parsing) : stdpp_scope.
Time
Infix "\226\136\170*" := (zip_with (\226\136\170)) (at level 50, left associativity) : stdpp_scope.
Time Notation "(\226\136\170*)" := (zip_with (\226\136\170)) (only parsing) : stdpp_scope.
Time
Infix "\226\136\170**" := (zip_with (zip_with (\226\136\170))) (at level 50, left associativity) :
stdpp_scope.
Time
Infix "\226\136\170*\226\136\170**" := (zip_with (prod_zip (\226\136\170) (\226\136\170*)))
(at level 50, left associativity) : stdpp_scope.
Time
Definition union_list `{Empty A} `{Union A} : list A \226\134\146 A := fold_right (\226\136\170) \226\136\133.
Time Arguments union_list _ _ _ !_ / : assert.
Time
Notation "\226\139\131 l" := (union_list l) (at level 20, format "\226\139\131  l") : stdpp_scope.
Time Class DisjUnion A :=
         disj_union : A \226\134\146 A \226\134\146 A.
Time Hint Mode DisjUnion !: typeclass_instances.
Time Instance: (Params (@disj_union) 2) := { }.
Time Infix "\226\138\142" := disj_union (at level 50, left associativity) : stdpp_scope.
Time Notation "(\226\138\142)" := disj_union (only parsing) : stdpp_scope.
Time Notation "( x \226\138\142)" := (disj_union x) (only parsing) : stdpp_scope.
Time Notation "(\226\138\142 x )" := (\206\187 y, disj_union y x) (only parsing) : stdpp_scope.
Time Class Intersection A :=
         intersection : A \226\134\146 A \226\134\146 A.
Time Hint Mode Intersection !: typeclass_instances.
Time Instance: (Params (@intersection) 2) := { }.
Time Infix "\226\136\169" := intersection (at level 40) : stdpp_scope.
Time Notation "(\226\136\169)" := intersection (only parsing) : stdpp_scope.
Time Notation "( x \226\136\169)" := (intersection x) (only parsing) : stdpp_scope.
Time
Notation "(\226\136\169 x )" := (\206\187 y, intersection y x) (only parsing) : stdpp_scope.
Time Class Difference A :=
         difference : A \226\134\146 A \226\134\146 A.
Time Hint Mode Difference !: typeclass_instances.
Time Instance: (Params (@difference) 2) := { }.
Time Infix "\226\136\150" := difference (at level 40, left associativity) : stdpp_scope.
Time Notation "(\226\136\150)" := difference (only parsing) : stdpp_scope.
Time Notation "( x \226\136\150)" := (difference x) (only parsing) : stdpp_scope.
Time Notation "(\226\136\150 x )" := (\206\187 y, difference y x) (only parsing) : stdpp_scope.
Time
Infix "\226\136\150*" := (zip_with (\226\136\150)) (at level 40, left associativity) : stdpp_scope.
Time Notation "(\226\136\150*)" := (zip_with (\226\136\150)) (only parsing) : stdpp_scope.
Time
Infix "\226\136\150**" := (zip_with (zip_with (\226\136\150))) (at level 40, left associativity) :
stdpp_scope.
Time
Infix "\226\136\150*\226\136\150**" := (zip_with (prod_zip (\226\136\150) (\226\136\150*)))
(at level 50, left associativity) : stdpp_scope.
Time Class Singleton A B :=
         singleton : A \226\134\146 B.
Time Hint Mode Singleton - !: typeclass_instances.
Time Instance: (Params (@singleton) 3) := { }.
Time Notation "{[ x ]}" := (singleton x) (at level 1) : stdpp_scope.
Time
Notation "{[ x ; y ; .. ; z ]}" :=
  (union .. (union (singleton x) (singleton y)) .. (singleton z))
  (at level 1) : stdpp_scope.
Time
Notation "{[ x , y ]}" := (singleton (x, y)) (at level 1, y  at next level) :
  stdpp_scope.
Time
Notation "{[ x , y , z ]}" := (singleton (x, y, z))
  (at level 1, y  at next level, z  at next level) : stdpp_scope.
Time Class SubsetEq A :=
         subseteq : relation A.
Time Hint Mode SubsetEq !: typeclass_instances.
Time Instance: (Params (@subseteq) 2) := { }.
Time Infix "\226\138\134" := subseteq (at level 70) : stdpp_scope.
Time Notation "(\226\138\134)" := subseteq (only parsing) : stdpp_scope.
Time Notation "( X \226\138\134)" := (subseteq X) (only parsing) : stdpp_scope.
Time Notation "(\226\138\134 X )" := (\206\187 Y, Y \226\138\134 X) (only parsing) : stdpp_scope.
Time Notation "X \226\138\136 Y" := (\194\172 X \226\138\134 Y) (at level 70) : stdpp_scope.
Time Notation "(\226\138\136)" := (\206\187 X Y, X \226\138\136 Y) (only parsing) : stdpp_scope.
Time Notation "( X \226\138\136)" := (\206\187 Y, X \226\138\136 Y) (only parsing) : stdpp_scope.
Time Notation "(\226\138\136 X )" := (\206\187 Y, Y \226\138\136 X) (only parsing) : stdpp_scope.
Time
Infix "\226\138\134@{ A }" := (@subseteq A _) (at level 70, only parsing) : stdpp_scope.
Time Notation "(\226\138\134@{ A } )" := (@subseteq A _) (only parsing) : stdpp_scope.
Time Infix "\226\138\134*" := (Forall2 (\226\138\134)) (at level 70) : stdpp_scope.
Time Notation "(\226\138\134*)" := (Forall2 (\226\138\134)) (only parsing) : stdpp_scope.
Time Infix "\226\138\134**" := (Forall2 (\226\138\134*)) (at level 70) : stdpp_scope.
Time Infix "\226\138\1341*" := (Forall2 (\206\187 p q, p.1 \226\138\134 q.1)) (at level 70) : stdpp_scope.
Time Infix "\226\138\1342*" := (Forall2 (\206\187 p q, p.2 \226\138\134 q.2)) (at level 70) : stdpp_scope.
Time
Infix "\226\138\1341**" := (Forall2 (\206\187 p q, p.1 \226\138\134* q.1)) (at level 70) : stdpp_scope.
Time
Infix "\226\138\1342**" := (Forall2 (\206\187 p q, p.2 \226\138\134* q.2)) (at level 70) : stdpp_scope.
Time Hint Extern 0 (_ \226\138\134 _) => reflexivity: core.
Time Hint Extern 0 (_ \226\138\134* _) => reflexivity: core.
Time Hint Extern 0 (_ \226\138\134** _) => reflexivity: core.
Time Infix "\226\138\130" := (strict (\226\138\134)) (at level 70) : stdpp_scope.
Time Notation "(\226\138\130)" := (strict (\226\138\134)) (only parsing) : stdpp_scope.
Time Notation "( X \226\138\130)" := (strict (\226\138\134) X) (only parsing) : stdpp_scope.
Time Notation "(\226\138\130 X )" := (\206\187 Y, Y \226\138\130 X) (only parsing) : stdpp_scope.
Time Notation "X \226\138\132 Y" := (\194\172 X \226\138\130 Y) (at level 70) : stdpp_scope.
Time Notation "(\226\138\132)" := (\206\187 X Y, X \226\138\132 Y) (only parsing) : stdpp_scope.
Time Notation "( X \226\138\132)" := (\206\187 Y, X \226\138\132 Y) (only parsing) : stdpp_scope.
Time Notation "(\226\138\132 X )" := (\206\187 Y, Y \226\138\132 X) (only parsing) : stdpp_scope.
Time
Infix "\226\138\130@{ A }" := (strict (\226\138\134@{A} )) (at level 70, only parsing) :
stdpp_scope.
Time Notation "(\226\138\130@{ A } )" := (strict (\226\138\134@{A} )) (only parsing) : stdpp_scope.
Time
Notation "X \226\138\134 Y \226\138\134 Z" := (X \226\138\134 Y \226\136\167 Y \226\138\134 Z) (at level 70, Y  at next level) :
  stdpp_scope.
Time
Notation "X \226\138\134 Y \226\138\130 Z" := (X \226\138\134 Y \226\136\167 Y \226\138\130 Z) (at level 70, Y  at next level) :
  stdpp_scope.
Time
Notation "X \226\138\130 Y \226\138\134 Z" := (X \226\138\130 Y \226\136\167 Y \226\138\134 Z) (at level 70, Y  at next level) :
  stdpp_scope.
Time
Notation "X \226\138\130 Y \226\138\130 Z" := (X \226\138\130 Y \226\136\167 Y \226\138\130 Z) (at level 70, Y  at next level) :
  stdpp_scope.
Time
Definition option_to_set `{Singleton A C} `{Empty C} 
  (mx : option A) : C := match mx with
                         | None => \226\136\133
                         | Some x => {[x]}
                         end.
Time
Fixpoint list_to_set `{Singleton A C} `{Empty C} `{Union C} 
(l : list A) : C :=
  match l with
  | [] => \226\136\133
  | x :: l => {[x]} \226\136\170 list_to_set l
  end.
Time
Fixpoint list_to_set_disj `{Singleton A C} `{Empty C} 
`{DisjUnion C} (l : list A) : C :=
  match l with
  | [] => \226\136\133
  | x :: l => {[x]} \226\138\142 list_to_set_disj l
  end.
Time Class Lexico A :=
         lexico : relation A.
Time Hint Mode Lexico !: typeclass_instances.
Time Class ElemOf A B :=
         elem_of : A \226\134\146 B \226\134\146 Prop.
Time Hint Mode ElemOf - !: typeclass_instances.
Time Instance: (Params (@elem_of) 3) := { }.
Time Infix "\226\136\136" := elem_of (at level 70) : stdpp_scope.
Time Notation "(\226\136\136)" := elem_of (only parsing) : stdpp_scope.
Time Notation "( x \226\136\136)" := (elem_of x) (only parsing) : stdpp_scope.
Time Notation "(\226\136\136 X )" := (\206\187 x, elem_of x X) (only parsing) : stdpp_scope.
Time Notation "x \226\136\137 X" := (\194\172 x \226\136\136 X) (at level 80) : stdpp_scope.
Time Notation "(\226\136\137)" := (\206\187 x X, x \226\136\137 X) (only parsing) : stdpp_scope.
Time Notation "( x \226\136\137)" := (\206\187 X, x \226\136\137 X) (only parsing) : stdpp_scope.
Time Notation "(\226\136\137 X )" := (\206\187 x, x \226\136\137 X) (only parsing) : stdpp_scope.
Time
Infix "\226\136\136@{ B }" := (@elem_of _ B _) (at level 70, only parsing) : stdpp_scope.
Time Notation "(\226\136\136@{ B } )" := (@elem_of _ B _) (only parsing) : stdpp_scope.
Time
Notation "x \226\136\137@{ B } X" := (\194\172 x \226\136\136@{ B} X) (at level 80, only parsing) :
  stdpp_scope.
Time
Notation "(\226\136\137@{ B } )" := (\206\187 x X, x \226\136\137@{ B} X) (only parsing) : stdpp_scope.
Time Class Disjoint A :=
         disjoint : A \226\134\146 A \226\134\146 Prop.
Time Hint Mode Disjoint !: typeclass_instances.
Time Instance: (Params (@disjoint) 2) := { }.
Time Infix "##" := disjoint (at level 70) : stdpp_scope.
Time Notation "(##)" := disjoint (only parsing) : stdpp_scope.
Time Notation "( X ##.)" := (disjoint X) (only parsing) : stdpp_scope.
Time Notation "(.## X )" := (\206\187 Y, Y ## X) (only parsing) : stdpp_scope.
Time
Infix "##@{ A }" := (@disjoint A _) (at level 70, only parsing) : stdpp_scope.
Time Notation "(##@{ A } )" := (@disjoint A _) (only parsing) : stdpp_scope.
Time Infix "##*" := (Forall2 (##)) (at level 70) : stdpp_scope.
Time Notation "(##*)" := (Forall2 (##)) (only parsing) : stdpp_scope.
Time Infix "##**" := (Forall2 (##*)) (at level 70) : stdpp_scope.
Time
Infix "##1*" := (Forall2 (\206\187 p q, p.1 ## q.1)) (at level 70) : stdpp_scope.
Time
Infix "##2*" := (Forall2 (\206\187 p q, p.2 ## q.2)) (at level 70) : stdpp_scope.
Time
Infix "##1**" := (Forall2 (\206\187 p q, p.1 ##* q.1)) (at level 70) : stdpp_scope.
Time
Infix "##2**" := (Forall2 (\206\187 p q, p.2 ##* q.2)) (at level 70) : stdpp_scope.
Time Hint Extern 0 (_ ## _) => (symmetry; eassumption): core.
Time Hint Extern 0 (_ ##* _) => (symmetry; eassumption): core.
Time Class DisjointE E A :=
         disjointE : E \226\134\146 A \226\134\146 A \226\134\146 Prop.
Time Hint Mode DisjointE - !: typeclass_instances.
Time Instance: (Params (@disjointE) 4) := { }.
Time
Notation "X ##{ \206\147 } Y" := (disjointE \206\147 X Y)
  (at level 70, format "X  ##{ \206\147 }  Y") : stdpp_scope.
Time
Notation "(##{ \206\147 } )" := (disjointE \206\147) (only parsing, \206\147  at level 1) :
  stdpp_scope.
Time
Notation "Xs ##{ \206\147 }* Ys" := (Forall2 (##{\206\147} ) Xs Ys)
  (at level 70, format "Xs  ##{ \206\147 }*  Ys") : stdpp_scope.
Time
Notation "(##{ \206\147 }* )" := (Forall2 (##{\206\147} )) (only parsing, \206\147  at level 1) :
  stdpp_scope.
Time
Notation "X ##{ \206\1471 , \206\1472 , .. , \206\1473 } Y" :=
  (disjoint (pair .. (\206\1471, \206\1472) .. \206\1473) X Y)
  (at level 70, format "X  ##{ \206\1471 , \206\1472 , .. , \206\1473 }  Y") : stdpp_scope.
Time
Notation "Xs ##{ \206\1471 , \206\1472 , .. , \206\1473 }* Ys" :=
  (Forall2 (disjoint (pair .. (\206\1471, \206\1472) .. \206\1473)) Xs Ys)
  (at level 70, format "Xs  ##{ \206\1471 ,  \206\1472 , .. , \206\1473 }*  Ys") : stdpp_scope.
Time Hint Extern 0 (_ ##{_} _) => (symmetry; eassumption): core.
Time Class DisjointList A :=
         disjoint_list : list A \226\134\146 Prop.
Time Hint Mode DisjointList !: typeclass_instances.
Time Instance: (Params (@disjoint_list) 2) := { }.
Time
Notation "## Xs" := (disjoint_list Xs) (at level 20, format "##  Xs") :
  stdpp_scope.
Time
Notation "##@{ A } Xs" := (@disjoint_list A _ Xs)
  (at level 20, only parsing) : stdpp_scope.
Time Section disjoint_list.
Time Context `{Disjoint A} `{Union A} `{Empty A}.
Time Implicit Type X : A.
Time
Inductive disjoint_list_default : DisjointList A :=
  | disjoint_nil_2 : ##@{ A} []
  | disjoint_cons_2 :
      forall (X : A) (Xs : list A), X ## \226\139\131 Xs \226\134\146 ## Xs \226\134\146 ## (X :: Xs).
Time #[global]Existing Instance disjoint_list_default.
Time Lemma disjoint_list_nil : ##@{ A} [] \226\134\148 True.
Time Proof.
Time (split; constructor).
Time Qed.
Time Lemma disjoint_list_cons X Xs : ## (X :: Xs) \226\134\148 X ## \226\139\131 Xs \226\136\167 ## Xs.
Time Proof.
Time split.
Time (inversion_clear 1; auto).
Time (intros [? ?]).
Time (constructor; auto).
Time Qed.
Time End disjoint_list.
Time
Class Filter A B :=
    filter : \226\136\128 (P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)}, B \226\134\146 B.
Time Hint Mode Filter - !: typeclass_instances.
Time Class UpClose A B :=
         up_close : A \226\134\146 B.
Time Hint Mode UpClose - !: typeclass_instances.
Time Notation "\226\134\145 x" := (up_close x) (at level 20, format "\226\134\145 x").
Time Class MRet (M : Type \226\134\146 Type) :=
         mret : \226\136\128 {A}, A \226\134\146 M A.
Time Arguments mret {_} {_} {_} _ : assert.
Time Instance: (Params (@mret) 3) := { }.
Time
Class MBind (M : Type \226\134\146 Type) :=
    mbind : \226\136\128 {A} {B}, (A \226\134\146 M B) \226\134\146 M A \226\134\146 M B.
Time Arguments mbind {_} {_} {_} {_} _ !_ / : assert.
Time Instance: (Params (@mbind) 4) := { }.
Time Class MJoin (M : Type \226\134\146 Type) :=
         mjoin : \226\136\128 {A}, M (M A) \226\134\146 M A.
Time Arguments mjoin {_} {_} {_} !_ / : assert.
Time Instance: (Params (@mjoin) 3) := { }.
Time Class FMap (M : Type \226\134\146 Type) :=
         fmap : \226\136\128 {A} {B}, (A \226\134\146 B) \226\134\146 M A \226\134\146 M B.
Time Arguments fmap {_} {_} {_} {_} _ !_ / : assert.
Time Instance: (Params (@fmap) 4) := { }.
Time
Class OMap (M : Type \226\134\146 Type) :=
    omap : \226\136\128 {A} {B}, (A \226\134\146 option B) \226\134\146 M A \226\134\146 M B.
Time Arguments omap {_} {_} {_} {_} _ !_ / : assert.
Time Instance: (Params (@omap) 4) := { }.
Time
Notation "m \226\137\171= f" := (mbind f m) (at level 60, right associativity) :
  stdpp_scope.
Time Notation "( m \226\137\171=)" := (\206\187 f, mbind f m) (only parsing) : stdpp_scope.
Time Notation "(\226\137\171= f )" := (mbind f) (only parsing) : stdpp_scope.
Time Notation "(\226\137\171=)" := (\206\187 m f, mbind f m) (only parsing) : stdpp_scope.
Time
Notation "x \226\134\144 y ; z" := (y \226\137\171= (\206\187 x, z))
  (at level 20, y  at level 100, z  at level 200, only parsing) : stdpp_scope.
Time
Notation "' x1 .. xn \226\134\144 y ; z" := (y \226\137\171= (\206\187 x1, .. (\206\187 xn, z) ..))
  (at level 20, x1 binder, xn binder, y  at level 100, z  at level 200,
   only parsing, right associativity) : stdpp_scope.
Time Infix "<$>" := fmap (at level 61, left associativity) : stdpp_scope.
Time
Notation "x ;; z" := (x \226\137\171= (\206\187 _, z))
  (at level 100, z  at level 200, only parsing, right associativity) :
  stdpp_scope.
Time
Notation "ps .*1" := (fmap (M:=list) fst ps)
  (at level 2, left associativity, format "ps .*1").
Time
Notation "ps .*2" := (fmap (M:=list) snd ps)
  (at level 2, left associativity, format "ps .*2").
Time
Class MGuard (M : Type \226\134\146 Type) :=
    mguard : \226\136\128 P {dec : Decision P} {A}, (P \226\134\146 M A) \226\134\146 M A.
Time Arguments mguard _ _ _ !_ _ _ / : assert.
Time
Notation "'guard' P ; z" := (mguard P (\206\187 _, z))
  (at level 20, z  at level 200, only parsing, right associativity) :
  stdpp_scope.
Time
Notation "'guard' P 'as' H ; z" := (mguard P (\206\187 H, z))
  (at level 20, z  at level 200, only parsing, right associativity) :
  stdpp_scope.
Time Class Lookup (K A M : Type) :=
         lookup : K \226\134\146 M \226\134\146 option A.
Time Hint Mode Lookup - - !: typeclass_instances.
Time Instance: (Params (@lookup) 4) := { }.
Time Notation "m !! i" := (lookup i m) (at level 20) : stdpp_scope.
Time Notation "(!!)" := lookup (only parsing) : stdpp_scope.
Time Notation "( m !!)" := (\206\187 i, m !! i) (only parsing) : stdpp_scope.
Time Notation "(!! i )" := (lookup i) (only parsing) : stdpp_scope.
Time Arguments lookup _ _ _ _ !_ !_ / : simpl nomatch,  assert.
Time Class SingletonM K A M :=
         singletonM : K \226\134\146 A \226\134\146 M.
Time Hint Mode SingletonM - - !: typeclass_instances.
Time Instance: (Params (@singletonM) 5) := { }.
Time Notation "{[ k := a ]}" := (singletonM k a) (at level 1) : stdpp_scope.
Time Class Insert (K A M : Type) :=
         insert : K \226\134\146 A \226\134\146 M \226\134\146 M.
Time Hint Mode Insert - - !: typeclass_instances.
Time Instance: (Params (@insert) 5) := { }.
Time
Notation "<[ k := a ]>" := (insert k a)
  (at level 5, right associativity, format "<[ k := a ]>") : stdpp_scope.
Time Arguments insert _ _ _ _ !_ _ !_ / : simpl nomatch,  assert.
Time Class Delete (K M : Type) :=
         delete : K \226\134\146 M \226\134\146 M.
Time Hint Mode Delete - !: typeclass_instances.
Time Instance: (Params (@delete) 4) := { }.
Time Arguments delete _ _ _ !_ !_ / : simpl nomatch,  assert.
Time Class Alter (K A M : Type) :=
         alter : (A \226\134\146 A) \226\134\146 K \226\134\146 M \226\134\146 M.
Time Hint Mode Alter - - !: typeclass_instances.
Time Instance: (Params (@alter) 5) := { }.
Time Arguments alter {_} {_} {_} {_} _ !_ !_ / : simpl nomatch,  assert.
Time
Class PartialAlter (K A M : Type) :=
    partial_alter : (option A \226\134\146 option A) \226\134\146 K \226\134\146 M \226\134\146 M.
Time Hint Mode PartialAlter - - !: typeclass_instances.
Time Instance: (Params (@partial_alter) 4) := { }.
Time Arguments partial_alter _ _ _ _ _ !_ !_ / : simpl nomatch,  assert.
Time Class Dom (M C : Type) :=
         dom : M \226\134\146 C.
Time Hint Mode Dom ! !: typeclass_instances.
Time Instance: (Params (@dom) 3) := { }.
Time Arguments dom : clear implicits.
Time Arguments dom {_} _ {_} !_ / : simpl nomatch,  assert.
Time
Class Merge (M : Type \226\134\146 Type) :=
    merge : \226\136\128 {A} {B} {C}, (option A \226\134\146 option B \226\134\146 option C) \226\134\146 M A \226\134\146 M B \226\134\146 M C.
Time Hint Mode Merge !: typeclass_instances.
Time Instance: (Params (@merge) 4) := { }.
Time Arguments merge _ _ _ _ _ _ !_ !_ / : simpl nomatch,  assert.
Time
Class UnionWith (A M : Type) :=
    union_with : (A \226\134\146 A \226\134\146 option A) \226\134\146 M \226\134\146 M \226\134\146 M.
Time Hint Mode UnionWith - !: typeclass_instances.
Time Instance: (Params (@union_with) 3) := { }.
Time Arguments union_with {_} {_} {_} _ !_ !_ / : simpl nomatch,  assert.
Time
Class IntersectionWith (A M : Type) :=
    intersection_with : (A \226\134\146 A \226\134\146 option A) \226\134\146 M \226\134\146 M \226\134\146 M.
Time Hint Mode IntersectionWith - !: typeclass_instances.
Time Instance: (Params (@intersection_with) 3) := { }.
Time
Arguments intersection_with {_} {_} {_} _ !_ !_ / : simpl nomatch,  assert.
Time
Class DifferenceWith (A M : Type) :=
    difference_with : (A \226\134\146 A \226\134\146 option A) \226\134\146 M \226\134\146 M \226\134\146 M.
Time Hint Mode DifferenceWith - !: typeclass_instances.
Time Instance: (Params (@difference_with) 3) := { }.
Time
Arguments difference_with {_} {_} {_} _ !_ !_ / : simpl nomatch,  assert.
Time
Definition intersection_with_list `{IntersectionWith A M}
  (f : A \226\134\146 A \226\134\146 option A) : M \226\134\146 list M \226\134\146 M := fold_right (intersection_with f).
Time Arguments intersection_with_list _ _ _ _ _ !_ / : assert.
Time Class LookupE (E K A M : Type) :=
         lookupE : E \226\134\146 K \226\134\146 M \226\134\146 option A.
Time Hint Mode LookupE - - - !: typeclass_instances.
Time Instance: (Params (@lookupE) 6) := { }.
Time
Notation "m !!{ \206\147 } i" := (lookupE \206\147 i m)
  (at level 20, format "m  !!{ \206\147 }  i") : stdpp_scope.
Time
Notation "(!!{ \206\147 } )" := (lookupE \206\147) (only parsing, \206\147  at level 1) :
  stdpp_scope.
Time Arguments lookupE _ _ _ _ _ _ !_ !_ / : simpl nomatch,  assert.
Time Class InsertE (E K A M : Type) :=
         insertE : E \226\134\146 K \226\134\146 A \226\134\146 M \226\134\146 M.
Time Hint Mode InsertE - - - !: typeclass_instances.
Time Instance: (Params (@insertE) 6) := { }.
Time
Notation "<[ k := a ]{ \206\147 }>" := (insertE \206\147 k a)
  (at level 5, right associativity, format "<[ k := a ]{ \206\147 }>") : stdpp_scope.
Time Arguments insertE _ _ _ _ _ _ !_ _ !_ / : simpl nomatch,  assert.
Time
Class SemiSet A C `{ElemOf A C} `{Empty C} `{Singleton A C} 
`{Union C} : Prop :={not_elem_of_empty : forall x : A, x \226\136\137@{ C} \226\136\133;
                     elem_of_singleton :
                      forall x y : A, x \226\136\136@{ C} {[y]} \226\134\148 x = y;
                     elem_of_union :
                      forall (X Y : C) (x : A), x \226\136\136 X \226\136\170 Y \226\134\148 x \226\136\136 X \226\136\168 x \226\136\136 Y}.
Time
Class Set_ A C `{ElemOf A C} `{Empty C} `{Singleton A C} 
`{Union C} `{Intersection C} `{Difference C} : Prop :={
 set_semi_set :>> SemiSet A C;
 elem_of_intersection : forall (X Y : C) (x : A), x \226\136\136 X \226\136\169 Y \226\134\148 x \226\136\136 X \226\136\167 x \226\136\136 Y;
 elem_of_difference : forall (X Y : C) (x : A), x \226\136\136 X \226\136\150 Y \226\134\148 x \226\136\136 X \226\136\167 x \226\136\137 Y}.
Time Class Elements A C :=
         elements : C \226\134\146 list A.
Time Hint Mode Elements - !: typeclass_instances.
Time Instance: (Params (@elements) 3) := { }.
Time
Inductive elem_of_list {A} : ElemOf A (list A) :=
  | elem_of_list_here : forall (x : A) l, x \226\136\136 x :: l
  | elem_of_list_further : forall (x y : A) l, x \226\136\136 l \226\134\146 x \226\136\136 y :: l.
Time Existing Instance elem_of_list.
Time Lemma elem_of_list_In {A} (l : list A) x : x \226\136\136 l \226\134\148 In x l.
Time Proof.
Time split.
Time -
Time (induction 1; simpl; auto).
Time -
Time (induction l; destruct 1; subst; constructor; auto).
Time Qed.
Time
Inductive NoDup {A} : list A \226\134\146 Prop :=
  | NoDup_nil_2 : NoDup []
  | NoDup_cons_2 : forall x l, x \226\136\137 l \226\134\146 NoDup l \226\134\146 NoDup (x :: l).
Time Lemma NoDup_ListNoDup {A} (l : list A) : NoDup l \226\134\148 List.NoDup l.
Time Proof.
Time split.
Time -
Time (induction 1; constructor; rewrite <- ?elem_of_list_In; auto).
Time -
Time (induction 1; constructor; rewrite ?elem_of_list_In; auto).
Time Qed.
Time
Class FinSet A C `{ElemOf A C} `{Empty C} `{Singleton A C} 
`{Union C} `{Intersection C} `{Difference C} `{Elements A C} 
`{EqDecision A} : Prop :={fin_set_set :>> Set_ A C;
                          elem_of_elements :
                           forall (X : C) x, x \226\136\136 elements X \226\134\148 x \226\136\136 X;
                          NoDup_elements : forall X : C, NoDup (elements X)}.
Time Class Size C :=
         size : C \226\134\146 nat.
Time Hint Mode Size !: typeclass_instances.
Time Arguments size {_} {_} !_ / : simpl nomatch,  assert.
Time Instance: (Params (@size) 2) := { }.
Time
Class MonadSet M `{\226\136\128 A, ElemOf A (M A)} `{\226\136\128 A, Empty (M A)}
`{\226\136\128 A, Singleton A (M A)} `{\226\136\128 A, Union (M A)} `{!MBind M} 
`{!MRet M} `{!FMap M} `{!MJoin M} : Prop :={monad_set_semi_set :>
                                             forall A, SemiSet A (M A);
                                            elem_of_bind :
                                             forall 
                                               {A} 
                                               {B} 
                                               (f : A \226\134\146 M B) 
                                               (X : M A) 
                                               (x : B),
                                             x \226\136\136 X \226\137\171= f
                                             \226\134\148 (\226\136\131 y, x \226\136\136 f y \226\136\167 y \226\136\136 X);
                                            elem_of_ret :
                                             forall {A} (x y : A),
                                             x \226\136\136@{ M A} mret y \226\134\148 x = y;
                                            elem_of_fmap :
                                             forall 
                                               {A} 
                                               {B} 
                                               (f : A \226\134\146 B) 
                                               (X : M A) 
                                               (x : B),
                                             x \226\136\136 f <$> X
                                             \226\134\148 (\226\136\131 y, x = f y \226\136\167 y \226\136\136 X);
                                            elem_of_join :
                                             forall {A} (X : M (M A)) (x : A),
                                             x \226\136\136 mjoin X
                                             \226\134\148 (\226\136\131 Y : M A, x \226\136\136 Y \226\136\167 Y \226\136\136 X)}.
Time Class Fresh A C :=
         fresh : C \226\134\146 A.
Time Hint Mode Fresh - !: typeclass_instances.
Time Instance: (Params (@fresh) 3) := { }.
Time Arguments fresh : simpl never.
Time
Class Infinite A :={infinite_fresh :> Fresh A (list A);
                    infinite_is_fresh : forall xs : list A, fresh xs \226\136\137 xs;
                    infinite_fresh_Permutation :>
                     Proper (@Permutation A ==> (=)) fresh}.
Time Arguments infinite_fresh : simpl never.
Time Class Half A :=
         half : A \226\134\146 A.
Time Hint Mode Half !: typeclass_instances.
Time Notation "\194\189" := half (format "\194\189") : stdpp_scope.
Time Notation "\194\189*" := (fmap (M:=list) half) : stdpp_scope.
Time Class SqSubsetEq A :=
         sqsubseteq : relation A.
Time Hint Mode SqSubsetEq !: typeclass_instances.
Time Instance: (Params (@sqsubseteq) 2) := { }.
Time Infix "\226\138\145" := sqsubseteq (at level 70) : stdpp_scope.
Time Notation "(\226\138\145)" := sqsubseteq (only parsing) : stdpp_scope.
Time Notation "( x \226\138\145)" := (sqsubseteq x) (only parsing) : stdpp_scope.
Time Notation "(\226\138\145 y )" := (\206\187 x, sqsubseteq x y) (only parsing) : stdpp_scope.
Time
Infix "\226\138\145@{ A }" := (@sqsubseteq A _) (at level 70, only parsing) :
stdpp_scope.
Time Notation "(\226\138\145@{ A } )" := (@sqsubseteq A _) (only parsing) : stdpp_scope.
Time
Instance sqsubseteq_rewrite  `{SqSubsetEq A}: (RewriteRelation (\226\138\145@{A} )) := {
 }.
Time Hint Extern 0 (_ \226\138\145 _) => reflexivity: core.
Time Class Meet A :=
         meet : A \226\134\146 A \226\134\146 A.
Time Hint Mode Meet !: typeclass_instances.
Time Instance: (Params (@meet) 2) := { }.
Time Infix "\226\138\147" := meet (at level 40) : stdpp_scope.
Time Notation "(\226\138\147)" := meet (only parsing) : stdpp_scope.
Time Notation "( x \226\138\147)" := (meet x) (only parsing) : stdpp_scope.
Time Notation "(\226\138\147 y )" := (\206\187 x, meet x y) (only parsing) : stdpp_scope.
Time Class Join A :=
         join : A \226\134\146 A \226\134\146 A.
Time Hint Mode Join !: typeclass_instances.
Time Instance: (Params (@join) 2) := { }.
Time Infix "\226\138\148" := join (at level 50) : stdpp_scope.
Time Notation "(\226\138\148)" := join (only parsing) : stdpp_scope.
Time Notation "( x \226\138\148)" := (join x) (only parsing) : stdpp_scope.
Time Notation "(\226\138\148 y )" := (\206\187 x, join x y) (only parsing) : stdpp_scope.
Time Class Top A :=
         top : A.
Time Hint Mode Top !: typeclass_instances.
Time Notation "\226\138\164" := top (format "\226\138\164") : stdpp_scope.
Time Class Bottom A :=
         bottom : A.
Time Hint Mode Bottom !: typeclass_instances.
Time Notation "\226\138\165" := bottom (format "\226\138\165") : stdpp_scope.
