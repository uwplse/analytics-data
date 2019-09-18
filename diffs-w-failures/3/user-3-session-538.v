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
Ltac subst_var := repeat match goal with
                         | v:=_:_ |- _ => subst v
                         end.
Create HintDb false.
Ltac solve_false := solve [ exfalso; eauto with false ].
Ltac
 rename_by_type type name :=
  match goal with
  | x:type |- _ => rename x into name
  end.
Ltac is_one_goal := let n := numgoals in
                    guard
                    n=1.
Ltac
 add_hypothesis pf :=
  let P := type of pf in
  lazymatch goal with
  | H:P |- _ => fail "already known"
  | _ => pose proof pf
  end.
Tactic Notation "gen" constr(X1) := generalize dependent X1.
Tactic Notation "gen" constr(X1) constr(X2) := (gen X2; gen X1).
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) :=
 (gen X3; gen X2; gen X1).
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) constr(X4) :=
 (gen X4; gen X3; gen X2; gen X1).
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5)
 := (gen X5; gen X4; gen X3; gen X2; gen X1).
Tactic Notation "pose" "unfolded" constr(pf) tactic(t) :=
 (let H := fresh in
  pose proof pf as H; t H;
   repeat match goal with
          | H:_ /\ _ |- _ => destruct H
          end).
