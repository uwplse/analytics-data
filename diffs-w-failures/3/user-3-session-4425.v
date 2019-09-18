Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Import updates local_updates.
Time From stdpp Require Export sets coPset.
Time Set Default Proof Using "Type".
Time Section coPset.
Time Implicit Types X Y : coPset.
Time Canonical Structure coPsetO := discreteO coPset.
Time Instance coPset_valid : (Valid coPset) := (\206\187 _, True).
Time Instance coPset_unit : (Unit coPset) := (\226\136\133 : coPset).
Time Instance coPset_op : (Op coPset) := union.
Time Instance coPset_pcore : (PCore coPset) := Some.
Time Lemma coPset_op_union X Y : X \226\139\133 Y = X \226\136\170 Y.
Time Proof.
Time done.
Time Qed.
Time Lemma coPset_core_self X : core X = X.
Time Proof.
Time done.
Time Qed.
Time Lemma coPset_included X Y : X \226\137\188 Y \226\134\148 X \226\138\134 Y.
Time Proof.
Time split.
Time -
Time (intros [Z ->]).
Time rewrite coPset_op_union.
Time set_solver.
Time -
Time (intros (Z, (->, ?))%subseteq_disjoint_union_L).
Time by exists Z.
Time Qed.
Time Lemma coPset_ra_mixin : RAMixin coPset.
Time Proof.
Time (apply ra_total_mixin; eauto).
Time -
Time solve_proper.
Time -
Time solve_proper.
Time -
Time solve_proper.
Time -
Time (intros X1 X2 X3).
Time by rewrite !coPset_op_union assoc_L.
Time -
Time (intros X1 X2).
Time by rewrite !coPset_op_union comm_L.
Time -
Time (intros X).
Time by rewrite coPset_core_self idemp_L.
Time Qed.
Time Canonical Structure coPsetR := discreteR coPset coPset_ra_mixin.
Time #[global]Instance coPset_cmra_discrete : (CmraDiscrete coPsetR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma coPset_ucmra_mixin : UcmraMixin coPset.
Time Proof.
Time split.
Time done.
Time (intros X).
Time by rewrite coPset_op_union left_id_L.
Time done.
Time Qed.
Time Canonical Structure coPsetUR := UcmraT coPset coPset_ucmra_mixin.
Time Lemma coPset_opM X mY : X \226\139\133? mY = X \226\136\170 default \226\136\133 mY.
Time Proof.
Time (destruct mY; by rewrite /= ?right_id_L).
Time Qed.
Time Lemma coPset_update X Y : X ~~> Y.
Time Proof.
Time done.
Time Qed.
Time Lemma coPset_local_update X Y X' : X \226\138\134 X' \226\134\146 (X, Y) ~l~> (X', X').
Time Proof.
Time (intros (Z, (->, ?))%subseteq_disjoint_union_L).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite local_update_unital_discrete =>Z'
 _ /leibniz_equiv_iff {+}->).
Time split.
Time done.
Time rewrite coPset_op_union.
Time set_solver.
Time Qed.
Time End coPset.
Time
Inductive coPset_disj :=
  | CoPset : coPset \226\134\146 coPset_disj
  | CoPsetBot : coPset_disj.
Time Section coPset_disj.
Time Arguments op _ _ !_ !_ /.
Time Canonical Structure coPset_disjO := leibnizO coPset_disj.
Time
Instance coPset_disj_valid : (Valid coPset_disj) :=
 (\206\187 X, match X with
       | CoPset _ => True
       | CoPsetBot => False
       end).
Time Instance coPset_disj_unit : (Unit coPset_disj) := (CoPset \226\136\133).
Time
Instance coPset_disj_op : (Op coPset_disj) :=
 (\206\187 X Y,
    match X, Y with
    | CoPset X, CoPset Y =>
        if decide (X ## Y) then CoPset (X \226\136\170 Y) else CoPsetBot
    | _, _ => CoPsetBot
    end).
Time Instance coPset_disj_pcore : (PCore coPset_disj) := (\206\187 _, Some \206\181).
Time
Ltac
 coPset_disj_solve :=
  repeat simpl || case_decide; (first
   [ apply (f_equal CoPset) | done | exfalso ]); set_solver by eauto.
Time Lemma coPset_disj_included X Y : CoPset X \226\137\188 CoPset Y \226\134\148 X \226\138\134 Y.
Time Proof.
Time split.
Time -
Time (move  {}=>[[Z|]]; simpl; try case_decide; set_solver).
Time -
Time (intros (Z, (->, ?))%subseteq_disjoint_union_L).
Time exists (CoPset Z).
Time coPset_disj_solve.
Time Qed.
Time
Lemma coPset_disj_valid_inv_l X Y :
  \226\156\147 (CoPset X \226\139\133 Y) \226\134\146 \226\136\131 Y', Y = CoPset Y' \226\136\167 X ## Y'.
Time Proof.
Time (destruct Y; repeat simpl || case_decide; by eauto).
Time Qed.
Time
Lemma coPset_disj_union X Y : X ## Y \226\134\146 CoPset X \226\139\133 CoPset Y = CoPset (X \226\136\170 Y).
Time Proof.
Time (intros).
Time by rewrite /= decide_True.
Time Qed.
Time Lemma coPset_disj_valid_op X Y : \226\156\147 (CoPset X \226\139\133 CoPset Y) \226\134\148 X ## Y.
Time Proof.
Time (simpl).
Time (case_decide; by split).
Time Qed.
Time Lemma coPset_disj_ra_mixin : RAMixin coPset_disj.
Time Proof.
Time (apply ra_total_mixin; eauto).
Time -
Time (intros [?| ]; destruct 1; coPset_disj_solve).
Time -
Time by constructor.
Time -
Time by destruct 1.
Time -
Time (intros [X1| ] [X2| ] [X3| ]; coPset_disj_solve).
Time -
Time (intros [X1| ] [X2| ]; coPset_disj_solve).
Time -
Time (intros [X| ]; coPset_disj_solve).
Time -
Time (exists (CoPset \226\136\133); coPset_disj_solve).
Time -
Time (intros [X1| ] [X2| ]; coPset_disj_solve).
Time Qed.
Time
Canonical Structure coPset_disjR :=
  discreteR coPset_disj coPset_disj_ra_mixin.
Time #[global]
Instance coPset_disj_cmra_discrete : (CmraDiscrete coPset_disjR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma coPset_disj_ucmra_mixin : UcmraMixin coPset_disj.
Time Proof.
Time (split; try apply _ || done).
Time (intros [X| ]; coPset_disj_solve).
Time Qed.
Time
Canonical Structure coPset_disjUR :=
  UcmraT coPset_disj coPset_disj_ucmra_mixin.
Time End coPset_disj.
