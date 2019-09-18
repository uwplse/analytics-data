Time From iris.algebra Require Export cmra.
Time Set Default Proof Using "Type".
Time
Definition cmra_updateP {A : cmraT} (x : A) (P : A \226\134\146 Prop) :=
  \226\136\128 n mz, \226\156\147{n} (x \226\139\133? mz) \226\134\146 \226\136\131 y, P y \226\136\167 \226\156\147{n} (y \226\139\133? mz).
Time Instance: (Params (@cmra_updateP) 1) := { }.
Time Infix "~~>:" := cmra_updateP (at level 70).
Time
Definition cmra_update {A : cmraT} (x y : A) :=
  \226\136\128 n mz, \226\156\147{n} (x \226\139\133? mz) \226\134\146 \226\156\147{n} (y \226\139\133? mz).
Time Infix "~~>" := cmra_update (at level 70).
Time Instance: (Params (@cmra_update) 1) := { }.
Time Section updates.
Time Context {A : cmraT}.
Time Implicit Types x y : A.
Time #[global]
Instance cmra_updateP_proper :
 (Proper ((\226\137\161) ==> pointwise_relation _ iff ==> iff) (@cmra_updateP A)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /pointwise_relation /cmra_updateP
  =>x x' Hx P P' HP; <ssreflect_plugin::ssrtclintros@0> split =>? n mz;
  setoid_subst; naive_solver).
Time Qed.
Time #[global]
Instance cmra_update_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> iff) (@cmra_update A)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /cmra_update =>x x' Hx y y' Hy;
  <ssreflect_plugin::ssrtclintros@0> split =>? n mz ?; setoid_subst; auto).
Time Qed.
Time Lemma cmra_update_updateP x y : x ~~> y \226\134\148 x ~~>: (y =).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> split =>Hup n z ?; eauto).
Time (destruct (Hup n z) as (?, (<-, ?)); auto).
Time Qed.
Time Lemma cmra_updateP_id (P : A \226\134\146 Prop) x : P x \226\134\146 x ~~>: P.
Time Proof.
Time (intros ? n mz ?; eauto).
Time Qed.
Time
Lemma cmra_updateP_compose (P Q : A \226\134\146 Prop) x :
  x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 y ~~>: Q) \226\134\146 x ~~>: Q.
Time Proof.
Time (intros Hx Hy n mz ?).
Time (destruct (Hx n mz) as (y, (?, ?)); naive_solver).
Time Qed.
Time
Lemma cmra_updateP_compose_l (Q : A \226\134\146 Prop) x y :
  x ~~> y \226\134\146 y ~~>: Q \226\134\146 x ~~>: Q.
Time Proof.
Time rewrite cmra_update_updateP.
Time (intros; apply cmra_updateP_compose with (y =); naive_solver).
Time Qed.
Time
Lemma cmra_updateP_weaken (P Q : A \226\134\146 Prop) x :
  x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q y) \226\134\146 x ~~>: Q.
Time Proof.
Time eauto using cmra_updateP_compose, cmra_updateP_id.
Time Qed.
Time #[global]Instance cmra_update_preorder : (PreOrder (@cmra_update A)).
Time Proof.
Time split.
Time -
Time (intros x).
Time by apply cmra_update_updateP, cmra_updateP_id.
Time -
Time (intros x y z).
Time rewrite !cmra_update_updateP.
Time eauto using cmra_updateP_compose with subst.
Time Qed.
Time Lemma cmra_update_exclusive `{!Exclusive x} y : \226\156\147 y \226\134\146 x ~~> y.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>? ? 
 [z|] =>[/exclusiveN_l []|_]).
Time by apply cmra_valid_validN.
Time Qed.
Time
Lemma cmra_updateP_op (P1 P2 Q : A \226\134\146 Prop) x1 x2 :
  x1 ~~>: P1
  \226\134\146 x2 ~~>: P2 \226\134\146 (\226\136\128 y1 y2, P1 y1 \226\134\146 P2 y2 \226\134\146 Q (y1 \226\139\133 y2)) \226\134\146 x1 \226\139\133 x2 ~~>: Q.
Time Proof.
Time (intros Hx1 Hx2 Hy n mz ?).
Time (destruct (Hx1 n (Some (x2 \226\139\133? mz))) as (y1, (?, ?))).
Time {
Time by rewrite /= -cmra_op_opM_assoc.
Time }
Time (destruct (Hx2 n (Some (y1 \226\139\133? mz))) as (y2, (?, ?))).
Time {
Time by rewrite /= -cmra_op_opM_assoc (comm _ x2) cmra_op_opM_assoc.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (y1 \226\139\133 y2); split ; last  rewrite
  (comm _ y1) cmra_op_opM_assoc; auto).
Time Qed.
Time
Lemma cmra_updateP_op' (P1 P2 : A \226\134\146 Prop) x1 x2 :
  x1 ~~>: P1
  \226\134\146 x2 ~~>: P2 \226\134\146 x1 \226\139\133 x2 ~~>: (\206\187 y, \226\136\131 y1 y2, y = y1 \226\139\133 y2 \226\136\167 P1 y1 \226\136\167 P2 y2).
Time Proof.
Time eauto  10 using cmra_updateP_op.
Time Qed.
Time
Lemma cmra_update_op x1 x2 y1 y2 :
  x1 ~~> y1 \226\134\146 x2 ~~> y2 \226\134\146 x1 \226\139\133 x2 ~~> y1 \226\139\133 y2.
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto using cmra_updateP_op with congruence).
Time Qed.
Time Lemma cmra_update_op_l x y : x \226\139\133 y ~~> x.
Time Proof.
Time (intros n mz).
Time rewrite comm cmra_op_opM_assoc.
Time (apply cmra_validN_op_r).
Time Qed.
Time Lemma cmra_update_op_r x y : x \226\139\133 y ~~> y.
Time Proof.
Time rewrite comm.
Time (apply cmra_update_op_l).
Time Qed.
Time Lemma cmra_update_valid0 x y : (\226\156\147{0} x \226\134\146 x ~~> y) \226\134\146 x ~~> y.
Time Proof.
Time (intros H n mz Hmz).
Time (apply H, Hmz).
Time (<ssreflect_plugin::ssrtclseq@0> apply (cmra_validN_le n) ; last  lia).
Time (destruct mz).
Time (eapply cmra_validN_op_l, Hmz).
Time (apply Hmz).
Time Qed.
Time Section total_updates.
Time #[local]Set Default Proof Using "Type*".
Time Context `{CmraTotal A}.
Time
Lemma cmra_total_updateP x (P : A \226\134\146 Prop) :
  x ~~>: P \226\134\148 (\226\136\128 n z, \226\156\147{n} (x \226\139\133 z) \226\134\146 \226\136\131 y, P y \226\136\167 \226\156\147{n} (y \226\139\133 z)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> split =>Hup;
  [ intros n z; apply (Hup n (Some z)) |  ]).
Time (intros n [z| ] ?; simpl; [ by apply Hup |  ]).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (Hup n (core x)) as (y, (?, ?)) ;
 first  by rewrite cmra_core_r).
Time eauto using cmra_validN_op_l.
Time Qed.
Time
Lemma cmra_total_update x y : x ~~> y \226\134\148 (\226\136\128 n z, \226\156\147{n} (x \226\139\133 z) \226\134\146 \226\156\147{n} (y \226\139\133 z)).
Time Proof.
Time rewrite cmra_update_updateP cmra_total_updateP.
Time naive_solver.
Time Qed.
Time Context `{CmraDiscrete A}.
Time
Lemma cmra_discrete_updateP (x : A) (P : A \226\134\146 Prop) :
  x ~~>: P \226\134\148 (\226\136\128 z, \226\156\147 (x \226\139\133 z) \226\134\146 \226\136\131 y, P y \226\136\167 \226\156\147 (y \226\139\133 z)).
Time Proof.
Time
(rewrite cmra_total_updateP; setoid_rewrite  <- cmra_discrete_valid_iff).
Time naive_solver eauto using 0.
Time Qed.
Time
Lemma cmra_discrete_update (x y : A) : x ~~> y \226\134\148 (\226\136\128 z, \226\156\147 (x \226\139\133 z) \226\134\146 \226\156\147 (y \226\139\133 z)).
Time Proof.
Time (rewrite cmra_total_update; setoid_rewrite  <- cmra_discrete_valid_iff).
Time naive_solver eauto using 0.
Time Qed.
Time End total_updates.
Time End updates.
Time Section cmra_transport.
Time Context {A B : cmraT} (H : A = B).
Time Notation T := (cmra_transport H).
Time
Lemma cmra_transport_updateP (P : A \226\134\146 Prop) (Q : B \226\134\146 Prop) 
  x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q (T y)) \226\134\146 T x ~~>: Q.
Time Proof.
Time (destruct H; eauto using cmra_updateP_weaken).
Time Qed.
Time
Lemma cmra_transport_updateP' (P : A \226\134\146 Prop) x :
  x ~~>: P \226\134\146 T x ~~>: (\206\187 y, \226\136\131 y', y = cmra_transport H y' \226\136\167 P y').
Time Proof.
Time eauto using cmra_transport_updateP.
Time Qed.
Time End cmra_transport.
Time Section prod.
Time Context {A B : cmraT}.
Time Implicit Type x : A * B.
Time
Lemma prod_updateP P1 P2 (Q : A * B \226\134\146 Prop) x :
  x.1 ~~>: P1 \226\134\146 x.2 ~~>: P2 \226\134\146 (\226\136\128 a b, P1 a \226\134\146 P2 b \226\134\146 Q (a, b)) \226\134\146 x ~~>: Q.
Time Proof.
Time (intros Hx1 Hx2 HP n mz [? ?]; simpl in *).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (Hx1 n (fst <$> mz)) as (a, (?, ?))
 ; first  by destruct mz).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (Hx2 n (snd <$> mz)) as (b, (?, ?))
 ; first  by destruct mz).
Time (exists (a, b); repeat split; destruct mz; auto).
Time Qed.
Time
Lemma prod_updateP' P1 P2 x :
  x.1 ~~>: P1 \226\134\146 x.2 ~~>: P2 \226\134\146 x ~~>: (\206\187 y, P1 y.1 \226\136\167 P2 y.2).
Time Proof.
Time eauto using prod_updateP.
Time Qed.
Time Lemma prod_update x y : x.1 ~~> y.1 \226\134\146 x.2 ~~> y.2 \226\134\146 x ~~> y.
Time Proof.
Time rewrite !cmra_update_updateP.
Time (destruct x, y; eauto using prod_updateP with subst).
Time Qed.
Time End prod.
Time Section option.
Time Context {A : cmraT}.
Time Implicit Types x y : A.
Time
Lemma option_updateP (P : A \226\134\146 Prop) (Q : option A \226\134\146 Prop) 
  x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q (Some y)) \226\134\146 Some x ~~>: Q.
Time Proof.
Time
(intros Hx Hy; <ssreflect_plugin::ssrtclintros@0> 
  apply cmra_total_updateP =>n [y|] ?).
Time {
Time (destruct (Hx n (Some y)) as (y', (?, ?)); auto).
Time (exists (Some y'); auto).
Time }
Time (destruct (Hx n None) as (y', (?, ?)); rewrite ?cmra_core_r; auto).
Time by exists (Some y'); auto.
Time Qed.
Time
Lemma option_updateP' (P : A \226\134\146 Prop) x :
  x ~~>: P \226\134\146 Some x ~~>: from_option P False.
Time Proof.
Time eauto using option_updateP.
Time Qed.
Time Lemma option_update x y : x ~~> y \226\134\146 Some x ~~> Some y.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using option_updateP with subst).
Time Qed.
Time End option.
