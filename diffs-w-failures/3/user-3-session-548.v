Time #[local]
Lemma abstract_away_helper {A} (P : A -> Prop) (x y : A) :
  P y -> y = x -> P x.
Time Proof.
Time (intros; subst; auto).
Time Qed.
Time
Ltac
 abstract_term t :=
  match goal with
  | |- ?g =>
        let p := eval pattern t in g in
        match p with
        | ?P ?x => eapply (abstract_away_helper P)
        end
  end.
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
