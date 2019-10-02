Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250b.BaseDefs.
Require Import BetaJulia.Sub0250b.BaseProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt_scope.
Open Scope btjnf_scope.
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
Lemma unite_pairs__preserves_sub_d2 : forall t1' t2' t1 t2 : ty, |- t1 << t1' -> |- t2 << t2' -> |- TPair t1 t2 << unite_pairs t1' t2'.
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
(apply unite_pairs__preserves_sub_d1; assumption).
(apply unite_pairs__preserves_sub_d2; assumption).
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
(intros t).
(pose proof (mk_nf__sub_d_eq t) as H; tauto).
Qed.
Lemma mk_nf__sub_d_r : forall t : ty, |- t << MkNF( t).
Proof.
(intros t).
(pose proof (mk_nf__sub_d_eq t) as H; tauto).
Qed.
