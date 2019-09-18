Time Require Eqdep.
Time Require Import Tactical.Propositional.
Time
Ltac
 sigT_eq :=
  match goal with
  | H:existT ?P ?a _ = existT ?P ?a _
    |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.
Time Ltac induct H := induction H; repeat sigT_eq; propositional.
Time
Ltac invert H := inversion H; repeat sigT_eq; propositional; repeat sigT_eq.
Time Ltac inv_clear H := invert H; clear H.
Time From Coq Require Export RelationClasses.
Time From Classes Require Export EqualDec.
Time From Classes Require Export Default.
Time
Ltac
 RelInstance_t :=
  intros;
   (let refl := try (solve [ hnf; intros; reflexivity ]) in
    let symm := try (solve [ hnf; intros; try symmetry; eauto ]) in
    let trans := try (solve [ hnf; intros; etransitivity; eauto ]) in
    try
     match goal with
     | |- Reflexive _ => hnf; intros; refl
     | |- Symmetric _ => hnf; intros; symm
     | |- Transitive _ => hnf; intros; trans
     | |- PreOrder _ => constructor; hnf; intros; [ refl | trans ]
     | |- Equivalence _ => constructor; hnf; intros; [ refl | symm | trans ]
     end).
Time Notation RelInstance := _ (only parsing).
