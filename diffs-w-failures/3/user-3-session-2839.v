Time
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
Time Tactic Notation "safe_intuition" := (safe_intuition_then ltac:(auto)).
Time Ltac subst_var := repeat match goal with
                              | v:=_:_ |- _ => subst v
                              end.
Time Create HintDb false.
Time Ltac solve_false := solve [ exfalso; eauto with false ].
Time Tactic Notation "safe_intuition" tactic(t) := (safe_intuition_then t).
Time Reserved Notation "P \226\138\162 Q"
(at level 99, Q  at level 200, right associativity).
Time Reserved Notation "P '\226\138\162@{' PROP } Q"
(at level 99, Q  at level 200, right associativity).
Time Reserved Notation "('\226\138\162@{' PROP } )" (at level 99).
Time Reserved Notation "P \226\138\163\226\138\162 Q" (at level 95, no associativity).
Time Reserved Notation "P '\226\138\163\226\138\162@{' PROP } Q" (at level 95, no associativity).
Time Reserved Notation "('\226\138\163\226\138\162@{' PROP } )" (at level 95).
Time Reserved Notation "'emp'".
Time Reserved Notation "'\226\140\156' \207\134 '\226\140\157'"
(at level 1, \207\134  at level 200, format "\226\140\156 \207\134 \226\140\157").
Time Reserved Notation "P \226\136\151 Q" (at level 80, right associativity).
Time Reserved Notation "P -\226\136\151 Q"
(at level 99, Q  at level 200, right associativity,
 format "'[' P  '/' -\226\136\151  Q ']'").
Time Reserved Notation "\226\142\161 P \226\142\164".
Time Reserved Notation "'<pers>' P" (at level 20, right associativity).
Time Reserved Notation "'<pers>?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'<pers>?' p  P").
Time Reserved Notation "\226\150\183 P" (at level 20, right associativity).
Time Reserved Notation "\226\150\183? p P"
(at level 20, p  at level 9, P  at level 20, format "\226\150\183? p  P").
Time Reserved Notation "\226\150\183^ n P"
(at level 20, n  at level 9, P  at level 20, format "\226\150\183^ n  P").
Time Reserved Notation "x '\226\136\151-\226\136\151' y" (at level 95, no associativity).
Time Reserved Notation "'<affine>' P" (at level 20, right associativity).
Time Reserved Notation "'<affine>?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'<affine>?' p  P").
Time
Ltac
 rename_by_type type name :=
  match goal with
  | x:type |- _ => rename x into name
  end.
Time Ltac is_one_goal := let n := numgoals in
                         guard
                         n=1.
Time
Ltac
 add_hypothesis pf :=
  let P := type of pf in
  lazymatch goal with
  | H:P |- _ => fail "already known"
  | _ => pose proof pf
  end.
Time
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
Time
Ltac
 prove_hyps H :=
  match type of H with
  | ?P -> ?Q =>
      let HP := fresh in
      assert (HP : P); [  | specialize (H HP); clear HP; prove_hyps H ]
  | _ => idtac
  end.
Time
Ltac destruct_ands := repeat match goal with
                             | H:_ /\ _ |- _ => destruct H
                             end.
Time
Ltac
 deex :=
  match goal with
  | H:exists varname, _
    |- _ =>
        let newvar := fresh varname in
        destruct H as [newvar ?]; destruct_ands; subst
  end.
Time Tactic Notation "gen" constr(X1) := generalize dependent X1.
Time Tactic Notation "gen" constr(X1) constr(X2) := (gen X2; gen X1).
Time
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) :=
 (gen X3; gen X2; gen X1).
Time
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) constr(X4) :=
 (gen X4; gen X3; gen X2; gen X1).
Time
Tactic Notation "gen" constr(X1) constr(X2) constr(X3) constr(X4) constr(X5)
 := (gen X5; gen X4; gen X3; gen X2; gen X1).
Time
Tactic Notation "pose" "unfolded" constr(pf) tactic(t) :=
 (let H := fresh in
  pose proof pf as H; t H;
   repeat match goal with
          | H:_ /\ _ |- _ => destruct H
          end).
Time Reserved Notation "'<absorb>' P" (at level 20, right associativity).
Time Reserved Notation "'<absorb>?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'<absorb>?' p  P").
Time Reserved Notation "\226\150\161 P" (at level 20, right associativity).
Time Reserved Notation "'\226\150\161?' p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "'\226\150\161?' p  P").
Time Reserved Notation "\226\151\135 P" (at level 20, right associativity).
Time Reserved Notation "\226\150\160 P" (at level 20, right associativity).
Time Reserved Notation "\226\150\160? p P"
(at level 20, p  at level 9, P  at level 20, right associativity,
 format "\226\150\160? p  P").
Time Reserved Notation "'<obj>' P" (at level 20, right associativity).
Time Reserved Notation "'<subj>' P" (at level 20, right associativity).
Time Reserved Notation "|==> Q"
(at level 99, Q  at level 200, format "|==>  Q").
Time Reserved Notation "P ==\226\136\151 Q"
(at level 99, Q  at level 200, format "'[' P  '/' ==\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 }=> Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "|={ E1 , E2 }=>  Q").
Time Reserved Notation "P ={ E1 , E2 }=\226\136\151 Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E1 , E2 }=\226\136\151  Q ']'").
Time Reserved Notation "|={ E }=> Q"
(at level 99, E  at level 50, Q  at level 200, format "|={ E }=>  Q").
Time Reserved Notation "P ={ E }=\226\136\151 Q"
(at level 99, E  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E }=\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 , E3 }\226\150\183=> Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "|={ E1 , E2 , E3 }\226\150\183=>  Q").
Time Reserved Notation "P ={ E1 , E2 , E3 }\226\150\183=\226\136\151 Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E1 , E2 , E3 }\226\150\183=\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 }\226\150\183=> Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "|={ E1 , E2 }\226\150\183=>  Q").
Time Reserved Notation "P ={ E1 , E2 }\226\150\183=\226\136\151 Q"
(at level 99, E1, E2  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E1 , E2 }\226\150\183=\226\136\151  Q ']'").
Time Reserved Notation "|={ E }\226\150\183=> Q"
(at level 99, E  at level 50, Q  at level 200, format "|={ E }\226\150\183=>  Q").
Time Reserved Notation "P ={ E }\226\150\183=\226\136\151 Q"
(at level 99, E  at level 50, Q  at level 200,
 format "'[' P  '/' ={ E }\226\150\183=\226\136\151  Q ']'").
Time Reserved Notation "|={ E1 , E2 }\226\150\183=>^ n Q"
(at level 99, E1, E2  at level 50, n  at level 9, Q  at level 200,
 format "|={ E1 , E2 }\226\150\183=>^ n  Q").
Time Reserved Notation "P ={ E1 , E2 }\226\150\183=\226\136\151^ n Q"
(at level 99, E1, E2  at level 50, n  at level 9, Q  at level 200,
 format "P  ={ E1 , E2 }\226\150\183=\226\136\151^ n  Q").
Time Reserved Notation "'[\226\136\151' 'list]' k \226\134\166 x \226\136\136 l , P"
(at level 200, l  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\151  list]  k \226\134\166 x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\151' 'list]' x \226\136\136 l , P"
(at level 200, l  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  list]  x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\151' 'list]' k \226\134\166 x1 ; x2 \226\136\136 l1 ; l2 , P"
(at level 200, l1, l2  at level 10, k, x1, x2  at level 1,
 right associativity, format "[\226\136\151  list]  k \226\134\166 x1 ; x2  \226\136\136  l1 ; l2 ,  P").
Time Reserved Notation "'[\226\136\151' 'list]' x1 ; x2 \226\136\136 l1 ; l2 , P"
(at level 200, l1, l2  at level 10, x1, x2  at level 1, right associativity,
 format "[\226\136\151  list]  x1 ; x2  \226\136\136  l1 ; l2 ,  P").
Time Reserved Notation "'[\226\136\151]' Ps" (at level 20).
Time Reserved Notation "'[\226\136\167' 'list]' k \226\134\166 x \226\136\136 l , P"
(at level 200, l  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\167  list]  k \226\134\166 x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\167' 'list]' x \226\136\136 l , P"
(at level 200, l  at level 10, x  at level 1, right associativity,
 format "[\226\136\167  list]  x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\167]' Ps" (at level 20).
Time Reserved Notation "'[\226\136\168' 'list]' k \226\134\166 x \226\136\136 l , P"
(at level 200, l  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\168  list]  k \226\134\166 x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\168' 'list]' x \226\136\136 l , P"
(at level 200, l  at level 10, x  at level 1, right associativity,
 format "[\226\136\168  list]  x  \226\136\136  l ,  P").
Time Reserved Notation "'[\226\136\168]' Ps" (at level 20).
Time Reserved Notation "'[\226\136\151' 'map]' k \226\134\166 x \226\136\136 m , P"
(at level 200, m  at level 10, k, x  at level 1, right associativity,
 format "[\226\136\151  map]  k \226\134\166 x  \226\136\136  m ,  P").
Time Reserved Notation "'[\226\136\151' 'map]' x \226\136\136 m , P"
(at level 200, m  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  map]  x  \226\136\136  m ,  P").
Time Reserved Notation "'[\226\136\151' 'map]' k \226\134\166 x1 ; x2 \226\136\136 m1 ; m2 , P"
(at level 200, m1, m2  at level 10, k, x1, x2  at level 1,
 right associativity, format "[\226\136\151  map]  k \226\134\166 x1 ; x2  \226\136\136  m1 ; m2 ,  P").
Time Reserved Notation "'[\226\136\151' 'map]' x1 ; x2 \226\136\136 m1 ; m2 , P"
(at level 200, m1, m2  at level 10, x1, x2  at level 1, right associativity,
 format "[\226\136\151  map]  x1 ; x2  \226\136\136  m1 ; m2 ,  P").
Time Reserved Notation "'[\226\136\151' 'set]' x \226\136\136 X , P"
(at level 200, X  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  set]  x  \226\136\136  X ,  P").
Time Reserved Notation "'[\226\136\151' 'mset]' x \226\136\136 X , P"
(at level 200, X  at level 10, x  at level 1, right associativity,
 format "[\226\136\151  mset]  x  \226\136\136  X ,  P").
Time Delimit Scope bi_scope with I.
