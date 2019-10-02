Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.MatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt_scope.
Open Scope btjm_scope.
Open Scope btjnf_scope.
Open Scope btjd_scope.
Lemma sub_d__inv_depth_le : forall t t' : ty, |- t << t' -> | t | <= | t' |.
Proof.
(intros t t' Hsub).
(induction Hsub).
-
constructor.
-
(apply Nat.le_trans with (| t2 |); assumption).
-
(simpl).
(apply Nat.max_le_compat; assumption).
-
(simpl).
(apply Nat.max_lub; assumption).
-
(simpl).
(apply Nat.le_max_l).
-
(simpl).
(apply Nat.le_max_r).
-
(simpl).
(rewrite max_baca_eq_bca).
constructor.
-
(simpl).
(rewrite max_abac_eq_abc).
constructor.
-
(simpl).
(apply le_n_S).
assumption.
Qed.
Lemma sub_d_eq__inv_depth_eq : forall t t' : ty, |- t << t' -> |- t' << t -> | t | = | t' |.
Proof.
(intros t t' Hsub1 Hsub2).
(apply Nat.le_antisymm; apply sub_d__inv_depth_le; assumption).
Qed.
Lemma unite_pairs__preserves_sub_d_l : forall t1 t2 t1' t2' : ty, |- t1 << t1' -> |- t2 << t2' -> |- unite_pairs t1 t2 << TPair t1' t2'.
Proof.
(intros ta; induction ta; intros tb;
  try (solve
   [ induction tb; intros ta' tb' Hsub1 Hsub2; try (solve [ simpl; constructor; assumption ]);
      destruct (sub_d_union_l__inv _ _ _ Hsub2) as [Hsub21 Hsub22]; rewrite unite_pairs_t_union; try resolve_not_union; constructor;
      [ apply IHtb1 | apply IHtb2 ]; assumption ])).
-
(intros ta' tb' Hsub1 Hsub2).
(apply sub_d_union_l__inv in Hsub1).
(destruct Hsub1 as [Hsub11 Hsub12]).
(rewrite unite_pairs_union_t).
(constructor; [ apply IHta1 | apply IHta2 ]; assumption).
Qed.
Lemma unite_pairs__preserves_sub_d_r : forall t1' t2' t1 t2 : ty, |- t1 << t1' -> |- t2 << t2' -> |- TPair t1 t2 << unite_pairs t1' t2'.
Proof.
(intros ta'; induction ta'; intros tb';
  try (solve
   [ induction tb'; intros ta tb Hsub1 Hsub2; try (solve [ simpl; constructor; assumption ]); rewrite unite_pairs_t_union; try resolve_not_union;
      apply SD_Trans with (TPair ta (TUnion tb'1 tb'2));
      [ constructor; constructor || assumption
      | apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)); apply SD_Distr2 || apply SD_UnionL;
         [ apply union_right_1; apply IHtb'1 | apply union_right_2; apply IHtb'2 ]; assumption || constructor ] ])).
-
(intros ta tb Hsub1 Hsub2).
(rewrite unite_pairs_union_t).
(apply SD_Trans with (TPair (TUnion ta'1 ta'2) tb)).
+
(constructor; constructor || assumption).
+
(apply SD_Trans with (TUnion (TPair ta'1 tb) (TPair ta'2 tb))).
(apply SD_Distr1).
(apply SD_UnionL).
(apply union_right_1; apply IHta'1; assumption || constructor).
(apply union_right_2; apply IHta'2; assumption || constructor).
Qed.
Theorem mk_nf__sub_d_eq : forall t : ty, |- MkNF( t) << t /\ |- t << MkNF( t).
Proof.
(induction t).
-
(split; simpl; constructor).
-
(destruct IHt1; destruct IHt2).
(split; simpl).
(apply unite_pairs__preserves_sub_d_l; assumption).
(apply unite_pairs__preserves_sub_d_r; assumption).
-
(destruct IHt1; destruct IHt2).
(split; simpl; constructor; (apply union_right_1; assumption) || (apply union_right_2; assumption)).
-
(simpl).
(destruct IHt).
(split; constructor; assumption).
Qed.
Lemma mk_nf__sub_d_l : forall t : ty, |- MkNF( t) << t.
Proof.
(apply mk_nf__sub_d_eq).
Qed.
Lemma mk_nf__sub_d_r : forall t : ty, |- t << MkNF( t).
Proof.
(apply mk_nf__sub_d_eq).
Qed.
Proof.
(intros k c Hdep t2).
(assert (Hva : value_type (TCName c)) by constructor).
