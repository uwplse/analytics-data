Time Require Eqdep.
Time Ltac descend := repeat match goal with
                            | |- exists _, _ => eexists
                            end.
Time
Ltac
 especialize H :=
  match type of H with
  | forall x : ?T, _ =>
      let x := fresh x in
      evar ( x : T ); specialize (H x); subst x
  end.
Time #[local]
Ltac
 _especialize H :=
  lazymatch type of H with
  | forall x : ?T, _ =>
      let x := fresh x in
      lazymatch type of T with
      | Prop => unshelve (evar ( x : T ); specialize (H x); subst x)
      | _ => evar ( x : T ); specialize (H x); subst x
      end
  end.
Time
Ltac
 epose_proof H :=
  let H' := fresh in
  pose proof H as H'; repeat _especialize H'.
Time
Ltac
 eexists_t t :=
  match goal with
  | |- exists _ : ?T, _ => eexists (_ : T)
  | |- {_ : ?T | _} => eexists (_ : T)
  end.
Time Ltac exists_econstructor := eexists_t ltac:(econstructor); simpl.
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
