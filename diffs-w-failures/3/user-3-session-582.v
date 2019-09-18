Time From Tactical Require Import Propositional.
Time From Transitions Require Import RelationDefs.
Time Import RelationNotations.
Time
Ltac
 rel_congruence :=
  let solver := try reflexivity in
  match goal with
  | |- rimpl (and_then _ ?rx) (and_then _ ?rx) =>
        apply and_then_monotonic_r; intros; solver
  | |- rimpl (and_then _ _) (and_then _ _) =>
        apply and_then_monotonic; intros; solver
  | |- rimpl (seq_star _) (seq_star _) => apply star_monotonic; solver
  | |- requiv (and_then _ ?rx) (and_then _ ?rx) =>
        apply and_then_cong_l; intros; solver
  | |- requiv (and_then ?p _) (and_then ?p _) =>
        apply and_then_cong_r; intros; solver
  | |- requiv (and_then _ _) (and_then _ _) =>
        apply and_then_equiv_cong; intros; solver
  | |- requiv (seq_star _) (seq_star _) => apply star_congruent; solver
  | |- requiv (bind_star _ ?v) (bind_star _ ?v) =>
        apply bind_star_congruent; intros
  end.
Time
Ltac
 setoid_norm_goal :=
  match goal with
  | |- context [ and_then (and_then _ _) _ ] => setoid_rewrite bind_assoc
  | |- context [ and_then (pure _) _ ] => setoid_rewrite bind_left_id
  | |- context [ @identity _ unit ] => setoid_rewrite unit_identity
  | |- context [ rel_or _ (rel_or _ _) ] => setoid_rewrite rel_or_assoc
  | |- context [ and_then none _ ] => setoid_rewrite none_absorb_l
  end.
Time
Ltac
 setoid_norm_hyp H :=
  match type of H with
  | context [ and_then (and_then _ _) _ ] => setoid_rewrite bind_assoc in
  H
  | context [ and_then (pure _) _ ] => setoid_rewrite bind_left_id in
  H
  | context [ @identity _ unit ] => setoid_rewrite unit_identity in
  H
  | context [ rel_or _ (rel_or _ _) ] => setoid_rewrite rel_or_assoc in H
  end.
Time
Ltac
 setoid_norm_hyps :=
  match goal with
  | H:context [ and_then (and_then _ _) _ ]
    |- _ => setoid_rewrite bind_assoc in H
  | H:context [ and_then (pure _) _ ]
    |- _ => setoid_rewrite bind_left_id in H
  | H:context [ @identity _ unit ] |- _ => setoid_rewrite unit_identity in H
  | H:context [ rel_or _ (rel_or _ _) ]
    |- _ => setoid_rewrite rel_or_assoc in H
  end.
Time Ltac norm_goal := repeat setoid_norm_goal.
Time Ltac norm_hyp H := repeat setoid_norm_hyp H.
Time Ltac norm_all := repeat setoid_norm_goal || setoid_norm_hyps.
Time Tactic Notation "norm" := (norm_goal; try reflexivity).
Time Tactic Notation "norm" "in" "*" := (norm_all; try reflexivity).
Time Tactic Notation "norm" "in" ident(H) := (norm_hyp H).
Time
Lemma rimpl_rx A B T (r1 r2 : relation A B T) :
  r1 ---> r2 ->
  forall C T2 (rx : T -> relation B C T2), and_then r1 rx ---> and_then r2 rx.
Time Proof.
Time (intros).
Time (rel_congruence; auto).
Time Qed.
Time Create HintDb relation_rewriting.
Time #[local]
Ltac
 with_hyp H tac :=
  let H' := fresh "Htmp" in
  pose proof H as H'; tac H'; clear H'.
Time
Ltac
 rel_hyp H tac :=
  with_hyp H ltac:(fun H => autounfold with relation_rewriting in H; tac H);
   norm.
Time Tactic Notation "rel" "with" constr(H) tactic(t) := (rel_hyp H t).
Time
Tactic Notation "rew" constr(pf) :=
 (rel_hyp pf ltac:(fun H => setoid_rewrite H)).
Time
Tactic Notation "rew<-" constr(pf) :=
 (rel_hyp pf ltac:(fun H => setoid_rewrite  <- H)).
Time
Tactic Notation "rew" "->" uconstr(pf) "in" ident(H) :=
 (rel_hyp pf ltac:(fun H' => setoid_rewrite H' in H at 1; norm_hyp H)).
Time
Tactic Notation "rew" "<-" uconstr(pf) "in" ident(H) :=
 (rel_hyp pf ltac:(fun H' => setoid_rewrite  <- H' in H at 1; norm_hyp H)).
Time
Ltac
 Split :=
  match goal with
  | |- _ + _ ---> _ => apply rel_or_elim; norm
  | |- and_then (_ + _) _ ---> _ => apply rel_or_elim_rx; norm
  | |- ?g ---> _ =>
        match g with
        | context [ _ + _ ] =>
            etransitivity;
             [ repeat
                setoid_rewrite bind_dist_l || setoid_rewrite bind_dist_r;
                apply rel_or_elim; norm_goal
             | reflexivity ]
        end
  end.
Time
Ltac
 Left :=
  match goal with
  | |- _ ---> ?g =>
        match g with
        | context [ _ + _ ] =>
            etransitivity; [  | rewrite <- rel_or_introl; norm_goal ];
             [ reflexivity |  ]; try reflexivity
        end
  end.
Time
Ltac
 Right :=
  match goal with
  | |- _ ---> ?g =>
        match g with
        | context [ _ + _ ] =>
            etransitivity; [  | rewrite <- rel_or_intror; norm_goal ];
             [ reflexivity |  ]; try reflexivity
        end
  end.
Time
Ltac
 left_associate H :=
  repeat setoid_rewrite  <- bind_assoc;
   try repeat setoid_rewrite  <- bind_assoc in H.
Time #[local]
Ltac
 left_assoc_rel_hyp H tac :=
  rel_hyp H ltac:(fun H => left_associate H; tac H).
Time
Tactic Notation "left_assoc" "with" constr(H) tactic(t) :=
 (left_assoc_rel_hyp H t).
Time
Tactic Notation "left_assoc" "rew" constr(H) :=
 (left_assoc_rel_hyp H ltac:(fun H => setoid_rewrite H)).
Time
Tactic Notation "left_assoc" "rew" "<-" constr(H) :=
 (left_assoc_rel_hyp H ltac:(fun H => setoid_rewrite  <- H)).
