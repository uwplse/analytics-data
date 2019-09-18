Time Require Export CSL.Refinement CSL.WeakestPre.
Time From iris.algebra Require Import auth gmap frac agree.
Time Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.ThreadReg.
Time From iris.algebra Require Export functions csum.
Time From iris.base_logic.lib Require Export invariants gen_heap.
Time From iris.proofmode Require Export tactics.
Time #[global]
Instance from_exist_left_sep  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist (\226\150\183 (\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \226\150\183 \206\166 a \226\136\151 Q)%I).
Time Proof.
Time rewrite /FromExist.
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&$)".
Time (iExists _; eauto).
Time Qed.
Time
Ltac
 iCancelPureRec P :=
  match P with
  | \226\140\156?P'\226\140\157%I =>
      let H := iFresh in
      iAssert \226\140\156P'\226\140\157%I as H; [ iPureIntro | iFrame H ]
  | (?P1 \226\136\151 ?P2)%I => first [ iCancelPureRec P1 | iCancelPureRec P2 ]
  end.
Time
Ltac
 iCancelPure :=
  match goal with
  | |- environments.envs_entails _ ?P => iCancelPureRec P
  end.
Time
Ltac
 iDestructPure :=
  repeat
   match goal with
   | |- context [ environments.Esnoc _ ?H \226\140\156_\226\140\157%I ] => iDestruct H as "%"
   end.
Time Section test.
Time Context {PROP : bi}.
Time Context {Hpos : BiPositive PROP}.
Time Context {Haffine : BiAffine PROP}.
Time Lemma cancel_pure1 (P : PROP) : P \226\138\162 \226\140\156(2 + 2 = 4)%nat\226\140\157 \226\136\151 P.
Time Proof.
Time iIntros "HP".
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  by lia).
Time auto.
Time Qed.
Time Lemma cancel_pure2 (P : PROP) : P \226\138\162 P \226\136\151 \226\140\156(2 + 2 = 4)%nat\226\140\157.
Time Proof.
Time iIntros "HP".
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  by lia).
Time auto.
Time Qed.
Time Lemma cancel_pure3 (P : PROP) : P \226\138\162 \226\140\1565 = 5\226\140\157%nat \226\136\151 \226\140\156(2 + 2 = 4)%nat\226\140\157.
Time Proof.
Time iIntros "HP".
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  by lia).
Time auto.
Time Qed.
Time Lemma destruct_pure1 (P : PROP) n : P \226\136\151 \226\140\156n > 100\226\140\157 \226\138\162 P \226\136\151 \226\140\156n > 99\226\140\157.
Time Proof.
Time iIntros "(?&?)".
Time iDestructPure.
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  lia).
Time auto.
Time Qed.
Time End test.
