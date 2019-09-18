Class Default T :=
    default : T.
#[local]Ltac mkDefault := unfold Default; constructor; exact default.
Hint Extern 1 (Default _) => mkDefault: typeclass_instances.
#[local]Notation cache_default := _ (only parsing).
Instance unit_def : (Default unit) := cache_default.
Instance nat_def : (Default nat) := cache_default.
Instance list_def  A: (Default (list A)) := cache_default.
Instance option_def  A: (Default (option A)) := cache_default.
Instance pair_def  A B (defA : Default A) (defB : Default B):
 (Default (A * B)) := cache_default.
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
