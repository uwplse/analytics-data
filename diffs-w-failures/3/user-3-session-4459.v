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
Time Canonical Structure countingC := leibnizC counting.
