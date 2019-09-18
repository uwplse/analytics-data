Time From iris.algebra Require Import proofmode_classes.
Time From iris.base_logic Require Import base_logic.
Time Set Default Proof Using "Type".
Time Inductive counting :=
       | Count : forall z : Z, _
       | CountBot : _.
Time #[local]Open Scope Z.
Time
Instance counting_valid : (Valid counting) :=
 (\206\187 x, match x with
       | Count _ => True
       | CountBot => False
       end).
Time
Instance counting_validN : (ValidN counting) :=
 (\206\187 n x, match x with
         | Count _ => True
         | CountBot => False
         end).
Time Instance counting_pcore : (PCore counting) := (\206\187 x, None).
Time
Instance counting_op : (Op counting) :=
 (\206\187 x y,
    match x, y with
    | Count z1, Count z2 =>
        if decide (z1 >= 0 \226\136\167 z2 >= 0) then CountBot
        else if decide ((z1 >= 0 \226\136\168 z2 >= 0) \226\136\167 z1 + z2 < 0) then CountBot
             else Count (z1 + z2)
    | _, _ => CountBot
    end).
Time Canonical Structure countingC := leibnizO counting.
Time #[local]
Ltac
 by_cases :=
  repeat <ssreflect_plugin::ssrtclintros@0>
   match goal with
   | H:counting |- _ => destruct H
   end =>//=; repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=;
   try lia.
Time Lemma counting_ra_mixin : RAMixin counting.
Time Proof.
Time (split; try apply _; try done).
Time -
Time (intros x y z).
Time rewrite /op /counting_op.
Time by_cases.
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op.
Time by_cases.
Time f_equal.
Time lia.
Time -
Time (intros x y).
Time rewrite /op /counting_op /valid.
Time by_cases.
Time Qed.
Time Canonical Structure countingR := discreteR counting counting_ra_mixin.
Time #[global]Instance counting_cmra_discrete : (CmraDiscrete countingR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma counting_op' (x y : countingR) : x \226\139\133 y = counting_op x y.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_valid' (x : countingR) : \226\156\147 x \226\134\148 counting_valid x.
Time Proof.
Time done.
Time Qed.
Time Lemma counting_validN' n (x : countingR) : \226\156\147{n} x \226\134\148 counting_validN n x.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance is_op_counting  z:
 (z >= 0 \226\134\146 IsOp' (Count z) (Count (z + 1)) (Count (- 1))).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp counting_op' =>?).
Time rewrite //=.
Time by_cases.
Time f_equal.
Time lia.
Time Qed.
Time #[global]
Instance is_op_counting'  (n : nat):
 (IsOp' (Count n) (Count (S n)) (Count (- 1))).
Time Proof.
Time rewrite /IsOp' /IsOp counting_op' //=.
Time by_cases.
Time f_equal.
Time lia.
Time Qed.
Time #[global]Instance counting_id_free  (z : counting): (IdFree z).
Time Proof.
Time (intros y).
Time rewrite counting_op' counting_validN'.
Time by_cases.
Time (destruct y; by_cases; intros _; inversion 1).
Time lia.
Time Qed.
Time #[global]Instance counting_full_exclusive : (Exclusive (Count 0)).
Time Proof.
Time (intros y).
Time rewrite counting_validN' counting_op'.
Time (<ssreflect_plugin::ssrtclintros@0> destruct y =>//=; by_cases).
Time Qed.
