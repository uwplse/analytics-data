Time From Coq.QArith Require Import Qcanon.
Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Notation frac := Qp (only parsing).
Time Section frac.
Time Canonical Structure fracO := leibnizO frac.
Time Instance frac_valid : (Valid frac) := (\206\187 x, (x \226\137\164 1)%Qc).
Time Instance frac_pcore : (PCore frac) := (\206\187 _, None).
Time Instance frac_op : (Op frac) := (\206\187 x y, (x + y)%Qp).
Time Lemma frac_included (x y : frac) : x \226\137\188 y \226\134\148 (x < y)%Qc.
Time Proof.
Time by rewrite Qp_lt_sum.
Time Qed.
Time Corollary frac_included_weak (x y : frac) : x \226\137\188 y \226\134\146 (x \226\137\164 y)%Qc.
Time Proof.
Time (intros ?%frac_included).
Time auto using Qclt_le_weak.
Time Qed.
Time Definition frac_ra_mixin : RAMixin frac.
Time Proof.
Time (split; try apply _; try done).
Time (unfold valid, op, frac_op, frac_valid).
Time (intros x y).
Time (<ssreflect_plugin::ssrtclseq@0> trans (x + y)%Qp ; last  done).
Time
(rewrite -{+1}(Qcplus_0_r x) -Qcplus_le_mono_l; auto using Qclt_le_weak).
Time Qed.
Time Canonical Structure fracR := discreteR frac frac_ra_mixin.
Time #[global]Instance frac_cmra_discrete : (CmraDiscrete fracR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time End frac.
Time #[global]Instance frac_full_exclusive : (Exclusive 1%Qp).
Time Proof.
Time move  {}=>y /Qcle_not_lt [] /=.
Time by rewrite -{+1}(Qcplus_0_r 1) -Qcplus_lt_mono_l.
Time Qed.
Time #[global]Instance frac_cancelable  (q : frac): (Cancelable q).
Time Proof.
Time (intros ? ? ? ? ?).
Time by apply Qp_eq, (inj (Qcplus q)), (Qp_eq (q + y) (q + z))%Qp.
Time Qed.
Time #[global]Instance frac_id_free  (q : frac): (IdFree q).
Time Proof.
Time (intros [q0 Hq0] ? EQ%Qp_eq).
Time rewrite -{+1}(Qcplus_0_r q) in  {} EQ.
Time (<ssreflect_plugin::ssrtclseq@0> eapply Qclt_not_eq ; first  done).
Time by apply (inj (Qcplus q)).
Time Qed.
Time Lemma frac_op' (q p : Qp) : p \226\139\133 q = (p + q)%Qp.
Time Proof.
Time done.
Time Qed.
Time Lemma frac_valid' (p : Qp) : \226\156\147 p \226\134\148 (p \226\137\164 1%Qp)%Qc.
Time Proof.
Time done.
Time Qed.
Time #[global]Instance is_op_frac  q: (IsOp' q (q / 2)%Qp (q / 2)%Qp).
Time Proof.
Time by rewrite /IsOp' /IsOp frac_op' Qp_div_2.
Time Qed.
