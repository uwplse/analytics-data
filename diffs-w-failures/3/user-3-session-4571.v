Time From iris.proofmode Require Export classes.
Time From iris.algebra Require Export cmra.
Time Class IsOp {A : cmraT} (a b1 b2 : A) :=
         is_op : a \226\137\161 b1 \226\139\133 b2.
Time Arguments is_op {_} _ _ _ {_}.
Time Hint Mode IsOp + - - -: typeclass_instances.
Time Instance is_op_op  {A : cmraT} (a b : A): (IsOp (a \226\139\133 b) a b) |100.
Time Proof.
Time by rewrite /IsOp.
Time Qed.
Time Class IsOp' {A : cmraT} (a b1 b2 : A) :=
         is_op' :> IsOp a b1 b2.
Time Hint Mode IsOp' + ! - -: typeclass_instances.
Time Hint Mode IsOp' + - ! !: typeclass_instances.
Time Class IsOp'LR {A : cmraT} (a b1 b2 : A) :=
         is_op_lr : IsOp a b1 b2.
Time Existing Instance is_op_lr |0.
Time Hint Mode IsOp'LR + ! - -: typeclass_instances.
Time Instance is_op_lr_op  {A : cmraT} (a b : A): (IsOp'LR (a \226\139\133 b) a b) |0.
Time Proof.
Time by rewrite /IsOp'LR /IsOp.
Time Qed.
Time #[global]
Instance is_op_pair  {A B : cmraT} (a b1 b2 : A) (a' b1' b2' : B):
 (IsOp a b1 b2 \226\134\146 IsOp a' b1' b2' \226\134\146 IsOp' (a, a') (b1, b1') (b2, b2')).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]
Instance is_op_pair_core_id_l  {A B : cmraT} (a : A) 
 (a' b1' b2' : B):
 (CoreId a \226\134\146 IsOp a' b1' b2' \226\134\146 IsOp' (a, a') (a, b1') (a, b2')).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>//=).
Time by rewrite -core_id_dup.
Time Qed.
Time #[global]
Instance is_op_pair_core_id_r  {A B : cmraT} (a b1 b2 : A) 
 (a' : B): (CoreId a' \226\134\146 IsOp a b1 b2 \226\134\146 IsOp' (a, a') (b1, a') (b2, a')).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>//=).
Time by rewrite -core_id_dup.
Time Qed.
Time #[global]
Instance is_op_Some  {A : cmraT} (a : A) b1 b2:
 (IsOp a b1 b2 \226\134\146 IsOp' (Some a) (Some b1) (Some b2)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance is_op_plus  (n1 n2 : nat): (IsOp (n1 + n2) n1 n2).
Time Proof.
Time done.
Time Qed.
