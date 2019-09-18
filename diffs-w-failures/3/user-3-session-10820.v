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
