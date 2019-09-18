Require Eqdep.
Require Import Tactical.Propositional.
Ltac
 sigT_eq :=
  match goal with
  | H:existT ?P ?a _ = existT ?P ?a _
    |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.
Ltac induct H := induction H; repeat sigT_eq; propositional.
Ltac invert H := inversion H; repeat sigT_eq; propositional; repeat sigT_eq.
Ltac inv_clear H := invert H; clear H.
