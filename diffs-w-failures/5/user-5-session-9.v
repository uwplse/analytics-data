Require Import List.
Import ListNotations.
Require Import Definitions.WellTyped.
Require Import Definitions.Trusted.Semantics.
Require Import Impl.Programs.
Require Import Impl.EvaluationState.
Require Import Impl.Typecheck.
Require Import Proofs.Tactics.
Definition EnvWt (env : Environment) (tenv : TypeEnvironment) : Prop :=
  forall var val,
  Lookup env var val ->
  exists t, LookupVarType (vars tenv) var t /\ ValueWt val t.
Hint Unfold EnvWt.
Lemma LookupVarType_unique :
  forall tenv var t1 t2,
  LookupVarType tenv var t1 -> LookupVarType tenv var t2 -> t1 = t2.
Proof.
(intros).
(induction H; inversion_then auto; congruence).
Qed.
Lemma ExpReduce_preservation :
  forall env tenv e e' t,
  EnvWt env tenv -> ExpWt tenv e t -> ExpReduce env e e' -> ExpWt tenv e' t.
Proof.
(intros).
(match goal with
 | H:ExpReduce _ _ _ |- _ => inv H
 end).
-
constructor.
(eapply_in_hyp H).
break_exists.
(inv H0).
(erewrite LookupVarType_unique; eapply_hyp).
-
(inversion_then constructor).
constructor.
Qed.
Lemma StmReduce_preservation :
  forall tenv s s' t, StmWt tenv s t -> StmReduce s s' -> StmWt tenv s' t.
Proof.
(intros).
(match goal with
 | H:StmReduce _ _ |- _ => inv H
 end; match goal with
      | H:StmWt _ _ _ |- _ => inv H
      end; try assumption; repeat constructor; auto).
Qed.
