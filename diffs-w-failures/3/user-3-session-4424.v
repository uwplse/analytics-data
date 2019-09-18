Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Import updates local_updates.
Time From stdpp Require Export sets gmap mapset.
Time Set Default Proof Using "Type".
Time Section gset.
Time Context `{Countable K}.
Time Implicit Types X Y : gset K.
Time Canonical Structure gsetO := discreteO (gset K).
Time Instance gset_valid : (Valid (gset K)) := (\206\187 _, True).
Time Instance gset_unit : (Unit (gset K)) := (\226\136\133 : gset K).
Time Instance gset_op : (Op (gset K)) := union.
Time Instance gset_pcore : (PCore (gset K)) := (\206\187 X, Some X).
Time Lemma gset_op_union X Y : X \226\139\133 Y = X \226\136\170 Y.
Time Proof.
Time done.
Time Qed.
Time Lemma gset_core_self X : core X = X.
Time Proof.
Time done.
Time Qed.
Time Lemma gset_included X Y : X \226\137\188 Y \226\134\148 X \226\138\134 Y.
Time Proof.
Time split.
Time -
Time (intros [Z ->]).
Time rewrite gset_op_union.
Time set_solver.
Time -
Time (intros (Z, (->, ?))%subseteq_disjoint_union_L).
Time by exists Z.
Time Qed.
Time Lemma gset_ra_mixin : RAMixin (gset K).
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
Time by rewrite !gset_op_union assoc_L.
Time -
Time (intros X1 X2).
Time by rewrite !gset_op_union comm_L.
Time -
Time (intros X).
Time by rewrite gset_core_self idemp_L.
Time Qed.
Time Canonical Structure gsetR := discreteR (gset K) gset_ra_mixin.
Time #[global]Instance gset_cmra_discrete : (CmraDiscrete gsetR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma gset_ucmra_mixin : UcmraMixin (gset K).
Time Proof.
Time split.
Time done.
Time (intros X).
Time by rewrite gset_op_union left_id_L.
Time done.
Time Qed.
Time Canonical Structure gsetUR := UcmraT (gset K) gset_ucmra_mixin.
Time Lemma gset_opM X mY : X \226\139\133? mY = X \226\136\170 default \226\136\133 mY.
Time Proof.
Time (destruct mY; by rewrite /= ?right_id_L).
Time Qed.
Time Lemma gset_update X Y : X ~~> Y.
Time Proof.
Time done.
Time Qed.
Time Lemma gset_local_update X Y X' : X \226\138\134 X' \226\134\146 (X, Y) ~l~> (X', X').
Time Proof.
Time (intros (Z, (->, ?))%subseteq_disjoint_union_L).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite local_update_unital_discrete =>Z'
 _ /leibniz_equiv_iff {+}->).
Time split.
Time done.
Time rewrite gset_op_union.
Time set_solver.
Time Qed.
Time #[global]Instance gset_core_id  X: (CoreId X).
Time Proof.
Time by apply core_id_total; rewrite gset_core_self.
Time Qed.
Time End gset.
Time Arguments gsetO _ {_} {_}.
Time Arguments gsetR _ {_} {_}.
Time Arguments gsetUR _ {_} {_}.
Time
Inductive gset_disj K `{Countable K} :=
  | GSet : gset K \226\134\146 gset_disj K
  | GSetBot : gset_disj K.
Time Arguments GSet {_} {_} {_} _.
Time Arguments GSetBot {_} {_} {_}.
Time Section gset_disj.
Time Context `{Countable K}.
Time Arguments op _ _ !_ !_ /.
Time Arguments cmra_op _ !_ !_ /.
Time Arguments ucmra_op _ !_ !_ /.
Time Canonical Structure gset_disjO := leibnizO (gset_disj K).
Time
Instance gset_disj_valid : (Valid (gset_disj K)) :=
 (\206\187 X, match X with
       | GSet _ => True
       | GSetBot => False
       end).
Time Instance gset_disj_unit : (Unit (gset_disj K)) := (GSet \226\136\133).
Time
Instance gset_disj_op : (Op (gset_disj K)) :=
 (\206\187 X Y,
    match X, Y with
    | GSet X, GSet Y => if decide (X ## Y) then GSet (X \226\136\170 Y) else GSetBot
    | _, _ => GSetBot
    end).
Time Instance gset_disj_pcore : (PCore (gset_disj K)) := (\206\187 _, Some \206\181).
Time
Ltac
 gset_disj_solve :=
  repeat simpl || case_decide; (first
   [ apply (f_equal GSet) | done | exfalso ]); set_solver by eauto.
Time Lemma gset_disj_included X Y : GSet X \226\137\188 GSet Y \226\134\148 X \226\138\134 Y.
Time Proof.
Time split.
Time -
Time (move  {}=>[[Z|]]; simpl; try case_decide; set_solver).
Time -
Time (intros (Z, (->, ?))%subseteq_disjoint_union_L).
Time exists (GSet Z).
Time gset_disj_solve.
Time Qed.
Time
Lemma gset_disj_valid_inv_l X Y :
  \226\156\147 (GSet X \226\139\133 Y) \226\134\146 \226\136\131 Y', Y = GSet Y' \226\136\167 X ## Y'.
Time Proof.
Time (destruct Y; repeat simpl || case_decide; by eauto).
Time Qed.
Time Lemma gset_disj_union X Y : X ## Y \226\134\146 GSet X \226\139\133 GSet Y = GSet (X \226\136\170 Y).
Time Proof.
Time (intros).
Time by rewrite /= decide_True.
Time Qed.
Time Lemma gset_disj_valid_op X Y : \226\156\147 (GSet X \226\139\133 GSet Y) \226\134\148 X ## Y.
Time Proof.
Time (simpl).
Time (case_decide; by split).
Time Qed.
Time Lemma gset_disj_ra_mixin : RAMixin (gset_disj K).
Time Proof.
Time (apply ra_total_mixin; eauto).
Time -
Time (intros [?| ]; destruct 1; gset_disj_solve).
Time -
Time by constructor.
Time -
Time by destruct 1.
Time -
Time (intros [X1| ] [X2| ] [X3| ]; gset_disj_solve).
Time -
Time (intros [X1| ] [X2| ]; gset_disj_solve).
Time -
Time (intros [X| ]; gset_disj_solve).
Time -
Time (exists (GSet \226\136\133); gset_disj_solve).
Time -
Time (intros [X1| ] [X2| ]; gset_disj_solve).
Time Qed.
Time
Canonical Structure gset_disjR := discreteR (gset_disj K) gset_disj_ra_mixin.
Time #[global]Instance gset_disj_cmra_discrete : (CmraDiscrete gset_disjR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma gset_disj_ucmra_mixin : UcmraMixin (gset_disj K).
Time Proof.
Time (split; try apply _ || done).
Time (intros [X| ]; gset_disj_solve).
Time Qed.
Time
Canonical Structure gset_disjUR := UcmraT (gset_disj K) gset_disj_ucmra_mixin.
Time Arguments op _ _ _ _ : simpl never.
Time
Lemma gset_disj_alloc_updateP_strong P (Q : gset_disj K \226\134\146 Prop) 
  X :
  (\226\136\128 Y, X \226\138\134 Y \226\134\146 \226\136\131 j, (j \226\136\137 Y) \226\136\167 P j)
  \226\134\146 (\226\136\128 i, i \226\136\137 X \226\134\146 P i \226\134\146 Q (GSet ({[i]} \226\136\170 X))) \226\134\146 GSet X ~~>: Q.
Time Proof.
Time (intros Hfresh HQ).
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_discrete_updateP =>?
 /gset_disj_valid_inv_l [Y [{+}-> ?]]).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (Hfresh (X \226\136\170 Y)) as (i, (?, ?)) ;
 first  set_solver).
Time (exists (GSet ({[i]} \226\136\170 X)); split).
Time -
Time (apply HQ; set_solver by eauto).
Time -
Time (apply gset_disj_valid_op).
Time set_solver by eauto.
Time Qed.
Time
Lemma gset_disj_alloc_updateP_strong' P X :
  (\226\136\128 Y, X \226\138\134 Y \226\134\146 \226\136\131 j, (j \226\136\137 Y) \226\136\167 P j)
  \226\134\146 GSet X ~~>: (\206\187 Y, \226\136\131 i, Y = GSet ({[i]} \226\136\170 X) \226\136\167 (i \226\136\137 X) \226\136\167 P i).
Time Proof.
Time eauto using gset_disj_alloc_updateP_strong.
Time Qed.
Time
Lemma gset_disj_alloc_empty_updateP_strong P (Q : gset_disj K \226\134\146 Prop) :
  (\226\136\128 Y : gset K, \226\136\131 j, (j \226\136\137 Y) \226\136\167 P j)
  \226\134\146 (\226\136\128 i, P i \226\134\146 Q (GSet {[i]})) \226\134\146 GSet \226\136\133 ~~>: Q.
Time Proof.
Time (intros).
Time (apply (gset_disj_alloc_updateP_strong P); eauto).
Time (intros i; rewrite right_id_L; auto).
Time Qed.
Time
Lemma gset_disj_alloc_empty_updateP_strong' P :
  (\226\136\128 Y : gset K, \226\136\131 j, (j \226\136\137 Y) \226\136\167 P j)
  \226\134\146 GSet \226\136\133 ~~>: (\206\187 Y, \226\136\131 i, Y = GSet {[i]} \226\136\167 P i).
Time Proof.
Time eauto using gset_disj_alloc_empty_updateP_strong.
Time Qed.
Time Section fresh_updates.
Time #[local]Set Default Proof Using "Type*".
Time Context `{!Infinite K}.
Time
Lemma gset_disj_alloc_updateP (Q : gset_disj K \226\134\146 Prop) 
  X : (\226\136\128 i, i \226\136\137 X \226\134\146 Q (GSet ({[i]} \226\136\170 X))) \226\134\146 GSet X ~~>: Q.
Time Proof.
Time (intro; eapply gset_disj_alloc_updateP_strong with (\206\187 _, True); eauto).
Time (intros Y ?; exists (fresh Y)).
Time split.
Time (apply is_fresh).
Time done.
Time Qed.
Time
Lemma gset_disj_alloc_updateP' X :
  GSet X ~~>: (\206\187 Y, \226\136\131 i, Y = GSet ({[i]} \226\136\170 X) \226\136\167 i \226\136\137 X).
Time Proof.
Time eauto using gset_disj_alloc_updateP.
Time Qed.
Time
Lemma gset_disj_alloc_empty_updateP (Q : gset_disj K \226\134\146 Prop) :
  (\226\136\128 i, Q (GSet {[i]})) \226\134\146 GSet \226\136\133 ~~>: Q.
Time Proof.
Time intro.
Time (apply gset_disj_alloc_updateP).
Time (intros i; rewrite right_id_L; auto).
Time Qed.
Time
Lemma gset_disj_alloc_empty_updateP' : GSet \226\136\133 ~~>: (\206\187 Y, \226\136\131 i, Y = GSet {[i]}).
Time Proof.
Time eauto using gset_disj_alloc_empty_updateP.
Time Qed.
Time End fresh_updates.
Time
Lemma gset_disj_dealloc_local_update X Y :
  (GSet X, GSet Y) ~l~> (GSet (X \226\136\150 Y), GSet \226\136\133).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_total_valid =>_ _
 /gset_disj_included HYX).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite local_update_unital_discrete =>-
 [Xf|] _ /leibniz_equiv_iff //=).
Time rewrite {+1}/op /=.
Time (destruct (decide _) as [HXf| ]; [ intros [=->] | done ]).
Time
by rewrite difference_union_distr_l_L difference_diag_L !left_id_L
 difference_disjoint_L.
Time Qed.
Time
Lemma gset_disj_dealloc_empty_local_update X Z :
  (GSet Z \226\139\133 GSet X, GSet Z) ~l~> (GSet X, GSet \226\136\133).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_total_valid
 =>/gset_disj_valid_op HZX _ _).
Time (assert (HX : X = (Z \226\136\170 X) \226\136\150 Z) by set_solver).
Time rewrite gset_disj_union // {+2}HX.
Time (apply gset_disj_dealloc_local_update).
Time Qed.
Time
Lemma gset_disj_dealloc_op_local_update X Y Z :
  (GSet Z \226\139\133 GSet X, GSet Z \226\139\133 GSet Y) ~l~> (GSet X, GSet Y).
Time Proof.
Time rewrite -{+2}(left_id \206\181 _ (GSet Y)).
Time (apply op_local_update_frame, gset_disj_dealloc_empty_local_update).
Time Qed.
Time
Lemma gset_disj_alloc_op_local_update X Y Z :
  Z ## X \226\134\146 (GSet X, GSet Y) ~l~> (GSet Z \226\139\133 GSet X, GSet Z \226\139\133 GSet Y).
Time Proof.
Time (intros).
Time (apply op_local_update_discrete).
Time by rewrite gset_disj_valid_op.
Time Qed.
Time
Lemma gset_disj_alloc_local_update X Y Z :
  Z ## X \226\134\146 (GSet X, GSet Y) ~l~> (GSet (Z \226\136\170 X), GSet (Z \226\136\170 Y)).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_total_valid =>_ _
 /gset_disj_included ?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -!gset_disj_union // ; last 
 set_solver).
Time auto using gset_disj_alloc_op_local_update.
Time Qed.
Time
Lemma gset_disj_alloc_empty_local_update X Z :
  Z ## X \226\134\146 (GSet X, GSet \226\136\133) ~l~> (GSet (Z \226\136\170 X), GSet Z).
Time Proof.
Time (intros).
Time rewrite -{+2}(right_id_L _ union Z).
Time (apply gset_disj_alloc_local_update; set_solver).
Time Qed.
Time End gset_disj.
Time Arguments gset_disjO _ {_} {_}.
Time Arguments gset_disjR _ {_} {_}.
Time Arguments gset_disjUR _ {_} {_}.
