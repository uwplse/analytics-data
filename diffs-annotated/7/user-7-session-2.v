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
Close Scope btj_scope.
Open Scope btjnf_scope.
Open Scope btjr_scope.
Lemma unite_pairs_of_nf__preserves_sub_r1 :
  forall t1 t2 t1' t2' : ty, InNF( t1) -> |- t1 << t1' -> InNF( t2) -> |- t2 << t2' -> |- unite_pairs t1 t2 << TPair t1' t2'.
Proof.
(intros ta; induction ta; intros tb; induction tb; intros ta' tb' Hnf1 Hsub1 Hnf2 Hsub2;
  try (solve
   [ simpl; constructor; assumption
   | match goal with
     | Hnf1:InNF( ?t), Hnf2:InNF( TUnion ?t1 ?t2), Hsub:|- TUnion ?t1 ?t2 << _
       |- |- unite_pairs ?t (TUnion ?t1 ?t2) << TPair _ _ =>
           destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfb1 Hnfb2];
            destruct (sub_r_nf_union_l__inv _ _ _ Hsub Hnf2) as [Hsubb1 Hsubb2]; rewrite unite_pairs_atom_union;
            try (solve [ constructor | inversion Hnf1; subst; assumption ]); constructor; [ apply IHtb1 | apply IHtb2 ]; assumption
     | Hnf1:InNF( ?t), Hnf2:InNF( TUnion ?t1 ?t2), Hsub:|- TUnion ?t1 ?t2 << _
       |- |- unite_pairs (TUnion ?t1 ?t2) ?t << TPair ?tx ?ty =>
           change_no_check (|- TUnion (unite_pairs t1 t) (unite_pairs t2 t) << TPair tx ty);
            destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfb1 Hnfb2];
            destruct (sub_r_nf_union_l__inv _ _ _ Hsub Hnf2) as [Hsubb1 Hsubb2]; constructor; [ apply IHta1 | apply IHta2 ];
            assumption
     end ])).
Qed.
Lemma mk_nf__sub_r_eq : forall t : ty, |- MkNF( t) << t /\ |- t << MkNF( t).
Proof.
(induction t).
-
(split; simpl; constructor).
-
(destruct IHt1; destruct IHt2).
(split; simpl).
+
(apply unite_pairs_of_nf__preserves_sub_r1; assumption || apply mk_nf__in_nf).
+
(apply SR_NormalForm).
(simpl).
(apply sub_r__rflxv).
-
(destruct IHt1; destruct IHt2).
(split; simpl; constructor; (apply SR_UnionR1; assumption) || (apply SR_UnionR2; assumption)).
-
(simpl).
(destruct IHt).
(split; constructor; assumption).
Qed.
Lemma mk_nf__sub_r1 : forall t : ty, |- MkNF( t) << t.
Proof.
(intros t).
(pose proof (mk_nf__sub_r_eq t) as H; tauto).
Qed.
Lemma mk_nf__sub_r2 : forall t : ty, |- t << MkNF( t).
Proof.
(intros t).
(pose proof (mk_nf__sub_r_eq t) as H; tauto).
Qed.
Lemma sub_r__reflexive : forall t : ty, |- t << t.
Proof.
(apply sub_r__rflxv).
Qed.
Lemma sub_r__transitive : forall t1 t2 t3 : ty, |- t1 << t2 -> |- t2 << t3 -> |- t1 << t3.
Proof.
(intros t1 t2 t3 Hsub1).
generalize dependent t3.
(induction Hsub1; intros t3 Hsub2).
-
assumption.
-
(remember (TPair t1' t2') as tm eqn:Heq ).
(induction Hsub2; try (solve [ inversion Heq | constructor ])).
+
(inversion Heq; subst).
(constructor; auto with DBBetaJulia).
+
(apply SR_UnionR1; tauto).
+
(apply SR_UnionR2; tauto).
+
subst.
clear IHHsub2.
(assert (Hsub1 : |- TPair t1 t2 << TPair t1' t2') by (constructor; assumption)).
(apply SR_NormalForm).
(* Failed. *)
