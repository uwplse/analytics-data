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
Lemma atom_sub_r_union__sub_r_component : forall t t1' t2' : ty, |- t << TUnion t1' t2' -> atom_type t -> |- t << t1' \/ |- t << t2'.
Proof.
(intros t t1' t2' Hsub).
(remember (TUnion t1' t2') as t' eqn:Heq ).
(induction Hsub; intros Hat; try (solve [ inversion Heq | inversion Hat ])).
-
(inversion Heq; subst).
(left; assumption).
-
(inversion Heq; subst).
(right; assumption).
-
subst.
(assert (Hnf : InNF( t)) by (constructor; assumption)).
(rewrite (mk_nf_nf__equal t Hnf) in IHHsub).
tauto.
Qed.
Lemma unite_pairs_of_nf__preserves_sub_r :
  forall t1 t1' t2 t2' : ty,
  InNF( t1) -> InNF( t1') -> InNF( t2) -> InNF( t2') -> |- t1 << t1' -> |- t2 << t2' -> |- unite_pairs t1 t2 << unite_pairs t1' t2'.
Proof.
(intros t1 t1' t2 t2' Hnf1).
(induction Hnf1).
-
(intros Hnf1'; induction Hnf1').
+
(intros Hnf2; induction Hnf2).
*
(intros Hnf2'; induction Hnf2'; intros Hsub1 Hsub2).
{
(rewrite (unite_pairs_of_atomtys _ _ H H1)).
(rewrite (unite_pairs_of_atomtys _ _ H0 H2)).
(constructor; assumption).
}
{
(rewrite unite_pairs_atom_union; try assumption).
(destruct (atom_sub_r_union__sub_r_component _ _ _ Hsub2 H1) as [Hsub21| Hsub22]; [ apply SR_UnionR1 | apply SR_UnionR2 ]; tauto).
}
*
(intros Hnf2'; intros Hsub1 Hsub2).
(rewrite unite_pairs_atom_union; try assumption).
(apply sub_r_nf_union_l__inv in Hsub2; try assumption).
(inversion Hsub2).
(constructor; [ apply IHHnf2_1 | apply IHHnf2_2 ]; assumption).
(constructor; assumption).
+
(intros Hnf2; intros Hnf2'; intros Hsub1 Hsub2).
(rewrite (unite_pairs_union_t t1 t0 t2')).
(destruct (atom_sub_r_union__sub_r_component _ _ _ Hsub1 H) as [Hsub11| Hsub12]; [ apply SR_UnionR1 | apply SR_UnionR2 ]; tauto).
-
(intros Hnf1' Hnf2 Hn2' Hsub1 Hsub2).
(rewrite (unite_pairs_union_t t1 t0 t2)).
(assert (Hnf : InNF( TUnion t1 t0)) by (constructor; assumption)).
(destruct (sub_r_nf_union_l__inv _ _ _ Hsub1 Hnf) as [Hsub11 Hsub12]).
(constructor; tauto).
Qed.
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
Lemma sub_r_unite_pairs_nf_l__inv :
  forall t1 t2 t1' t2' : ty, |- unite_pairs t1 t2 << TPair t1' t2' -> InNF( t1) -> InNF( t2) -> |- t1 << t1' /\ |- t2 << t2'.
Proof.
(intros t1; induction t1; intros t2; induction t2; intros t1' t2' Hsub; intros Hnf1 Hnf2;
  try (solve
   [ match goal with
     | Hsub:|- ?t1 << ?t2
       |- _ =>
           remember t1 as tx eqn:Heqx ; remember t2 as ty eqn:Heqy ;
            assert (Hnf : InNF( t1)) by (subst; apply unite_pairs__preserves_nf; assumption); induction Hsub; 
            inversion Heqx; inversion Heqy; subst; tauto || (rewrite (mk_nf_nf__equal _ Hnf) in IHHsub; tauto)
     end ])).
-
(rewrite unite_pairs_t_union in Hsub; try resolve_not_union).
(destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnf21 Hnf22]).
(apply sub_r_nf_union_l__inv in Hsub).
(destruct Hsub as [Hsub1 Hsub2]).
specialize (IHt2_1 _ _ Hsub1 Hnf1 Hnf21).
specialize (IHt2_2 _ _ Hsub2 Hnf1 Hnf22).
(split; tauto || constructor; tauto).
(apply NF_Union; apply unite_pairs__preserves_nf; assumption).
-
(rewrite unite_pairs_t_union in Hsub; try resolve_not_union).
(destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnf21 Hnf22]).
(apply sub_r_nf_union_l__inv in Hsub).
(destruct Hsub as [Hsub1 Hsub2]).
specialize (IHt2_1 _ _ Hsub1 Hnf1 Hnf21).
specialize (IHt2_2 _ _ Hsub2 Hnf1 Hnf22).
(split; tauto || constructor; tauto).
(apply NF_Union; apply unite_pairs__preserves_nf; assumption).
-
(rewrite unite_pairs_union_t in Hsub).
(destruct (union_in_nf__components_in_nf _ _ Hnf1) as [Hnf11 Hnf12]).
(apply sub_r_nf_union_l__inv in Hsub).
(destruct Hsub as [Hsub1 Hsub2]).
specialize (IHt1_1 _ _ _ Hsub1 Hnf11 Hnf2).
specialize (IHt1_2 _ _ _ Hsub2 Hnf12 Hnf2).
(split; tauto || constructor; tauto).
(apply NF_Union; apply unite_pairs__preserves_nf; assumption).
-
(rewrite unite_pairs_union_t in Hsub).
(destruct (union_in_nf__components_in_nf _ _ Hnf1) as [Hnf11 Hnf12]).
(apply sub_r_nf_union_l__inv in Hsub).
(destruct Hsub as [Hsub1 Hsub2]).
specialize (IHt1_1 _ _ _ Hsub1 Hnf11 Hnf2).
specialize (IHt1_2 _ _ _ Hsub2 Hnf12 Hnf2).
(split; tauto || constructor; tauto).
(apply NF_Union; apply unite_pairs__preserves_nf; assumption).
-
(rewrite unite_pairs_union_t in Hsub).
(destruct (union_in_nf__components_in_nf _ _ Hnf1) as [Hnf11 Hnf12]).
(apply sub_r_nf_union_l__inv in Hsub).
(destruct Hsub as [Hsub1 Hsub2]).
specialize (IHt1_1 _ _ _ Hsub1 Hnf11 Hnf2).
specialize (IHt1_2 _ _ _ Hsub2 Hnf12 Hnf2).
(split; tauto || constructor; tauto).
(apply NF_Union; apply unite_pairs__preserves_nf; assumption).
-
(rewrite unite_pairs_union_t in Hsub).
(destruct (union_in_nf__components_in_nf _ _ Hnf1) as [Hnf11 Hnf12]).
(apply sub_r_nf_union_l__inv in Hsub).
(destruct Hsub as [Hsub1 Hsub2]).
specialize (IHt1_1 _ _ _ Hsub1 Hnf11 Hnf2).
specialize (IHt1_2 _ _ _ Hsub2 Hnf12 Hnf2).
(split; tauto || constructor; tauto).
(apply NF_Union; apply unite_pairs__preserves_nf; assumption).
-
(rewrite unite_pairs_t_union in Hsub; try resolve_not_union).
(destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnf21 Hnf22]).
(apply sub_r_nf_union_l__inv in Hsub).
(destruct Hsub as [Hsub1 Hsub2]).
specialize (IHt2_1 _ _ Hsub1 Hnf1 Hnf21).
specialize (IHt2_2 _ _ Hsub2 Hnf1 Hnf22).
(split; tauto || constructor; tauto).
(apply NF_Union; apply unite_pairs__preserves_nf; assumption).
Qed.
Lemma sub_r_pair__inv : forall t1 t2 t1' t2' : ty, |- TPair t1 t2 << TPair t1' t2' -> |- t1 << t1' /\ |- t2 << t2'.
Proof.
(intros t1 t2 t1' t2' Hsub).
(remember (TPair t1 t2) as tx eqn:Heqx ).
(remember (TPair t1' t2') as ty eqn:Heqy ).
(induction Hsub; inversion Heqx; inversion Heqy; subst).
-
(split; assumption).
-
(simpl in Hsub).
(apply sub_r_unite_pairs_nf_l__inv in Hsub; try apply mk_nf__in_nf).
(destruct Hsub; split; apply SR_NormalForm; assumption).
Qed.
Lemma eq_r_trans :
  forall t1 t2 : ty, |- t1 << t2 -> |- t2 << t1 -> forall t3 : ty, |- t2 << t3 -> |- t3 << t2 -> |- t1 << t3 /\ |- t3 << t1.
Proof.
(intros t1 t2 Hsub11).
(induction Hsub11).
-
(intros Hsub12 t3 Hsub21).
(induction Hsub21; try (solve [ intros; split; [ constructor; assumption | assumption ] ])).
-
(intros Hsub12 t3 Hsub21).
(apply sub_r_pair__inv in Hsub12; destruct Hsub12 as [Hsub121 Hsub122]).
(remember (TPair t1' t2') as tx eqn:Heqx ).
(induction Hsub21; inversion Heqx; subst).
+
clear Heqx IHHsub21_1 IHHsub21_2.
(intros Hsub22).
(apply sub_r_pair__inv in Hsub22; destruct Hsub22 as [Hsub221 Hsub222]).
specialize (IHHsub11_1 Hsub121 _ Hsub21_1 Hsub221).
specialize (IHHsub11_2 Hsub122 _ Hsub21_2 Hsub222).
(split; constructor; tauto).
+
(intros Hsub22).
(apply sub_r_union_l__inv in Hsub22).
split.
(apply SR_UnionR1; tauto).
Abort.
Lemma sub_r_nf__transitive : forall t1 t2 t3 : ty, |- t1 << t2 -> InNF( t1) -> InNF( t2) -> |- t2 << t3 -> |- t1 << t3.
Proof.
(intros t1 t2 t3 Hsub1).
generalize dependent t3.
(induction Hsub1; intros t3 Hnf1 Hnf2 Hsub2; try (solve [ assumption ])).
-
(inversion Hnf1; subst).
(inversion Hnf2; subst).
(inversion H; inversion H0; subst).
(remember (TPair t1' t2') as tx eqn:Heqx ; induction Hsub2; inversion Heqx; subst).
+
(constructor; [ apply IHHsub1_1 | apply IHHsub1_2 ]; try assumption || constructor; assumption).
+
(apply SR_UnionR1; auto).
+
(apply SR_UnionR2; auto).
+
(apply IHHsub2).
(apply mk_nf_nf__equal; assumption).
(apply mk_nf__in_nf).
(rewrite mk_nf_nf__equal; assumption).
-
(destruct (union_in_nf__components_in_nf _ _ Hnf1) as [Hnfa1 Hnfa2]).
(constructor; [ apply IHHsub1_1 | apply IHHsub1_2 ]; assumption).
-
(destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfa1 Hnfa2]).
(apply IHHsub1; try assumption).
(pose proof (sub_r_nf_union_l__inv _ _ _ Hsub2 Hnf2); tauto).
-
(destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfa1 Hnfa2]).
(apply IHHsub1; try assumption).
(pose proof (sub_r_nf_union_l__inv _ _ _ Hsub2 Hnf2); tauto).
-
(remember (TRef t') as tx eqn:Heqx ).
(inversion Hnf1; subst).
(inversion Hnf2; subst).
(inversion H; subst).
(inversion H0; subst).
(remember (TRef t') as tx eqn:Heqx ).
(induction Hsub2; inversion Heqx; subst).
+
(apply SR_UnionR1; tauto).
+
(apply SR_UnionR2; tauto).
+
Abort.
Lemma weird_trans : forall t1 t2 : ty, |- t1 << t2 -> forall t3 : ty, |- t2 << t3 -> |- t3 << t2 -> |- t1 << t3.
Proof.
(intros t1 t2 Hsub1).
(induction Hsub1).
-
tauto.
-
(intros t3 Hsub21).
(remember (TPair t1' t2') as tx eqn:Heqx ).
(* Auto-generated comment: Failed. *)

