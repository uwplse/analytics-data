Time From iris.base_logic Require Export derived.
Time From iris.algebra Require Import proofmode_classes.
Time Import base_logic.bi.uPred.
Time Section class_instances.
Time Context {M : ucmraT}.
Time Implicit Types P Q R : uPred M.
Time #[global]
Instance into_pure_cmra_valid  `{!CmraDiscrete A} 
 (a : A): (@IntoPure (uPredI M) (\226\156\147 a) (\226\156\147 a)).
Time Proof.
Time by rewrite /IntoPure discrete_valid.
Time Qed.
Time #[global]
Instance from_pure_cmra_valid  {A : cmraT} (a : A):
 (@FromPure (uPredI M) false (\226\156\147 a) (\226\156\147 a)).
Time Proof.
Time rewrite /FromPure /=.
Time (<ssreflect_plugin::ssrtclintros@0> eapply bi.pure_elim =>// ?).
Time rewrite -uPred.cmra_valid_intro //.
Time Qed.
Time #[global]
Instance from_sep_ownM  (a b1 b2 : M):
 (IsOp a b1 b2 \226\134\146 FromSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2)).
Time Proof.
Time (intros).
Time by rewrite /FromSep -ownM_op -is_op.
Time Qed.
Time #[global]
Instance from_sep_ownM_core_id  (a b1 b2 : M):
 (IsOp a b1 b2
  \226\134\146 TCOr (CoreId b1) (CoreId b2)
    \226\134\146 FromAnd (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2)).
Time Proof.
Time (intros ? H).
Time rewrite /FromAnd (is_op a) ownM_op.
Time (destruct H; by rewrite bi.persistent_and_sep).
Time Qed.
Time #[global]
Instance into_and_ownM  p (a b1 b2 : M):
 (IsOp a b1 b2 \226\134\146 IntoAnd p (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2)).
Time Proof.
Time (intros).
Time (apply bi.intuitionistically_if_mono).
Time by rewrite (is_op a) ownM_op bi.sep_and.
Time Qed.
Time #[global]
Instance into_sep_ownM  (a b1 b2 : M):
 (IsOp a b1 b2 \226\134\146 IntoSep (uPred_ownM a) (uPred_ownM b1) (uPred_ownM b2)).
Time Proof.
Time (intros).
Time by rewrite /IntoSep (is_op a) ownM_op.
Time Qed.
Time End class_instances.
