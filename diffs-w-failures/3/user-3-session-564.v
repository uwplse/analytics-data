Require Import Tactical.Propositional.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationAlgebra.
Require Import List.
Import RelationNotations.
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
Ltac
 setoid_norm_goal :=
  match goal with
  | |- context [ and_then (and_then _ _) _ ] => setoid_rewrite bind_assoc
  | |- context [ and_then (pure _) _ ] => setoid_rewrite bind_left_id
  | |- context [ @identity _ unit ] => setoid_rewrite unit_identity
  | |- context [ rel_or _ (rel_or _ _) ] => setoid_rewrite rel_or_assoc
  end.
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
Ltac norm_goal := repeat setoid_norm_goal.
Ltac norm_hyp H := repeat setoid_norm_hyp H.
Ltac norm_all := repeat setoid_norm_goal || setoid_norm_hyps.
Tactic Notation "norm" := (norm_goal; try reflexivity).
Tactic Notation "norm" "in" "*" := (norm_all; try reflexivity).
Tactic Notation "norm" "in" ident(H) := (norm_hyp H).
Lemma rimpl_rx A B T (r1 r2 : relation A B T) :
  r1 ---> r2 ->
  forall C T2 (rx : T -> relation B C T2), and_then r1 rx ---> and_then r2 rx.
Proof.
(intros).
(rel_congruence; auto).
Qed.
Create HintDb relation_rewriting.
#[local]
Ltac
 with_hyp H tac :=
  let H' := fresh "Htmp" in
  pose proof H as H'; tac H'; clear H'.
Ltac
 rel_hyp H tac :=
  with_hyp H ltac:(fun H => autounfold with relation_rewriting in H; tac H);
   norm.
Tactic Notation "rel" "with" constr(H) tactic(t) := (rel_hyp H t).
Tactic Notation "rew" constr(pf) :=
 (rel_hyp pf ltac:(fun H => setoid_rewrite H)).
Tactic Notation "rew<-" constr(pf) :=
 (rel_hyp pf ltac:(fun H => setoid_rewrite  <- H)).
Tactic Notation "rew" "->" uconstr(pf) "in" ident(H) :=
 (rel_hyp pf ltac:(fun H' => setoid_rewrite H' in H at 1; norm_hyp H)).
Tactic Notation "rew" "<-" uconstr(pf) "in" ident(H) :=
 (rel_hyp pf ltac:(fun H' => setoid_rewrite  <- H' in H at 1; norm_hyp H)).
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
Ltac
 left_associate H :=
  repeat setoid_rewrite  <- bind_assoc;
   try repeat setoid_rewrite  <- bind_assoc in H.
#[local]
Ltac
 left_assoc_rel_hyp H tac :=
  rel_hyp H ltac:(fun H => left_associate H; tac H).
Tactic Notation "left_assoc" "with" constr(H) tactic(t) :=
 (left_assoc_rel_hyp H t).
Tactic Notation "left_assoc" "rew" constr(H) :=
 (left_assoc_rel_hyp H ltac:(fun H => setoid_rewrite H)).
Tactic Notation "left_assoc" "rew" "<-" constr(H) :=
 (left_assoc_rel_hyp H ltac:(fun H => setoid_rewrite  <- H)).
#[global]Set Implicit Arguments.
#[global]Generalizable Variables T R Op State.
#[global]Set Printing Projections.
Set Warnings "-undeclared-scope".
Import RelationNotations.
Inductive proc (Op : Type -> Type) (T : Type) : Type :=
  | Call : forall op : Op T, _
  | Ret : forall v : T, _
  | Bind : forall (T1 : Type) (p1 : proc Op T1) (p2 : T1 -> proc Op T), _.
Arguments Call {Op} {T}.
Arguments Ret {Op} {T} v.
Inductive proc_seq (Op : Type -> Type) (R : Type) : Type :=
  | Seq_Nil : _
  | Seq_Bind :
      forall (T : Type) (p : proc Op T) (rx : T + R -> proc_seq Op R), _.
Arguments Seq_Nil {Op} {R}.
Arguments Seq_Bind {Op} {R} {T}.
Definition OpSemantics Op State := forall T, Op T -> relation State State T.
Definition CrashSemantics State := relation State State unit.
Record Dynamics Op State :={step : OpSemantics Op State;
                            crash_step : CrashSemantics State}.
Section Dynamics.
Context `(sem : Dynamics Op State).
Notation proc := (proc Op).
Notation proc_seq := (proc_seq Op).
Notation step := sem.(step).
Notation crash_step := sem.(crash_step).
Fixpoint exec {T} (p : proc T) : relation State State T :=
  match p with
  | Ret v => pure v
  | Call op => step op
  | Bind p p' => v <- exec p; exec (p' v)
  end.
Fixpoint exec_crash {T} (p : proc T) : relation State State unit :=
  match p with
  | Ret v => crash_step
  | Call op => crash_step + (step op;; crash_step)
  | Bind p p' => exec_crash p + (v <- exec p; exec_crash (p' v))
  end.
Definition exec_recover {R} (rec : proc R) : relation State State R :=
  seq_star (exec_crash rec);; exec rec.
Definition exec_recover_unfold {R} (rec : proc R) :
  exec_recover rec = seq_star (exec_crash rec);; exec rec := eq_refl.
Definition rexec {T} {R} (p : proc T) (rec : proc R) :
  relation State State R := exec_crash p;; exec_recover rec.
Definition rexec_unfold {T} {R} (p : proc T) (rec : proc R) :
  rexec p rec = exec_crash p;; exec_recover rec := eq_refl.
Definition exec_or_rexec {T} {R} (p : proc T) (rec : proc R) :
  relation State State (T + R) :=
  (v <- exec p; pure (inl v)) + (v <- rexec p rec; pure (inr v)).
Fixpoint exec_seq {R} (p : proc_seq R) (rec : proc R) :
relation State State (list {X : Type & X}) :=
  match p with
  | Seq_Nil => pure nil
  | Seq_Bind p f => v <- exec_or_rexec p rec; l <- exec_seq (f v) rec;
      pure (existT _ _ v :: l)
  end.
Lemma exec_seq_unfold {R} (p : proc_seq R) (rec : proc R) :
  exec_seq p rec =
  match p with
  | Seq_Nil => pure nil
  | Seq_Bind p f => v <- exec_or_rexec p rec; l <- exec_seq (f v) rec;
      pure (existT _ _ v :: l)
  end.
Proof.
(destruct p; auto).
Qed.
End Dynamics.
Module ProcNotations.
Delimit Scope proc_scope with proc.
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 54, right associativity) : proc_scope.
End ProcNotations.
