Ltac
 safe_intuition_then t :=
  repeat
   match goal with
   | H:_ /\ _ |- _ => destruct H
   | H:?P -> _
     |- _ => lazymatch type of P with
             | Prop => specialize (H _)
             | _ => fail
             end
   | _ => progress t
   end.
Tactic Notation "safe_intuition" := (safe_intuition_then ltac:(auto)).
Tactic Notation "safe_intuition" tactic(t) := (safe_intuition_then t).
#[local]
Lemma abstract_away_helper {A} (P : A -> Prop) (x y : A) :
  P y -> y = x -> P x.
Proof.
(intros; subst; auto).
Ltac
 propositional :=
  repeat
   match goal with
   | |- forall _, _ => intros
   | H:_ /\ _ |- _ => destruct H
   | H:_ <-> _ |- _ => destruct H
   | H:False |- _ => solve [ destruct H ]
   | H:True |- _ => clear H
   | H:?P -> _, H':?P
     |- _ => match type of P with
             | Prop => specialize (H H')
             end
   | H:forall x, x = _ -> _ |- _ => specialize (H _ eq_refl)
   | H:forall x, _ = x -> _ |- _ => specialize (H _ eq_refl)
   | H:exists varname, _
     |- _ => let newvar := fresh varname in
             destruct H as [newvar ?]
   | H:?P |- ?P => exact H
   | _ => progress subst
   end.
Ltac
 prove_hyps H :=
  match type of H with
  | ?P -> ?Q =>
      let HP := fresh in
      assert (HP : P); [  | specialize (H HP); clear HP; prove_hyps H ]
  | _ => idtac
  end.
Ltac destruct_ands := repeat match goal with
                             | H:_ /\ _ |- _ => destruct H
                             end.
Ltac
 deex :=
  match goal with
  | H:exists varname, _
    |- _ =>
        let newvar := fresh varname in
        destruct H as [newvar ?]; destruct_ands; subst
  end.
Qed.
Ltac
 abstract_term t :=
  match goal with
  | |- ?g =>
        let p := eval pattern t in g in
        match p with
        | ?P ?x => eapply (abstract_away_helper P)
        end
  end.
