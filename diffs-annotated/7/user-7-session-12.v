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
Lemma atom_sub_r_union__inv : forall t t1' t2' : ty, |- t << TUnion t1' t2' -> atom_type t -> |- t << t1' \/ |- t << t2'.
Proof.
(intros t t1' t2' Hsub).
(remember (TUnion t1' t2') as t' eqn:Heq ).
(induction Hsub; intros Hat; try (solve [ inversion Heq | inversion Hat ]); inversion Heq; subst).
-
(left; assumption).
-
(right; assumption).
-
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
(destruct (atom_sub_r_union__inv _ _ _ Hsub2 H1) as [Hsub21| Hsub22]; [ apply SR_UnionR1 | apply SR_UnionR2 ]; tauto).
}
*
(intros Hnf2'; intros Hsub1 Hsub2).
(rewrite unite_pairs_atom_union; try assumption).
(apply sub_r_union_l__inv in Hsub2; try assumption).
(inversion Hsub2).
(constructor; [ apply IHHnf2_1 | apply IHHnf2_2 ]; assumption).
+
(intros Hnf2; intros Hnf2'; intros Hsub1 Hsub2).
(rewrite (unite_pairs_union_t t1 t0 t2')).
(destruct (atom_sub_r_union__inv _ _ _ Hsub1 H) as [Hsub11| Hsub12]; [ apply SR_UnionR1 | apply SR_UnionR2 ]; tauto).
-
(intros Hnf1' Hnf2 Hn2' Hsub1 Hsub2).
(rewrite (unite_pairs_union_t t1 t0 t2)).
(destruct (sub_r_union_l__inv _ _ _ Hsub1) as [Hsub11 Hsub12]).
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
           destruct (in_nf_union__inv _ _ Hnf2) as [Hnfb1 Hnfb2]; destruct (sub_r_union_l__inv _ _ _ Hsub) as [Hsubb1 Hsubb2];
            rewrite unite_pairs_atom_union; try (solve [ constructor | inversion Hnf1; subst; assumption ]); constructor;
            [ apply IHtb1 | apply IHtb2 ]; assumption
     | Hnf1:InNF( ?t), Hnf2:InNF( TUnion ?t1 ?t2), Hsub:|- TUnion ?t1 ?t2 << _
       |- |- unite_pairs (TUnion ?t1 ?t2) ?t << TPair ?tx ?ty =>
           change_no_check (|- TUnion (unite_pairs t1 t) (unite_pairs t2 t) << TPair tx ty); destruct (in_nf_union__inv _ _ Hnf2) as [Hnfb1 Hnfb2];
            destruct (sub_r_union_l__inv _ _ _ Hsub) as [Hsubb1 Hsubb2]; constructor; [ apply IHta1 | apply IHta2 ]; assumption
     end ])).
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
            assert (Hnf : InNF( t1)) by (subst; apply unite_pairs__preserves_nf; assumption); induction Hsub; inversion Heqx; 
            inversion Heqy; subst; tauto || (rewrite (mk_nf_nf__equal _ Hnf) in IHHsub; tauto)
     | Hsub:|- unite_pairs _ (TUnion _ _) << TPair _ _
       |- _ =>
           rewrite unite_pairs_t_union in Hsub; try resolve_not_union; destruct (in_nf_union__inv _ _ Hnf2) as [Hnf21 Hnf22];
            apply sub_r_union_l__inv in Hsub; destruct Hsub as [Hsub1 Hsub2]; specialize (IHt2_1 _ _ Hsub1 Hnf1 Hnf21); specialize
            (IHt2_2 _ _ Hsub2 Hnf1 Hnf22); split; tauto || constructor; tauto
     | Hsub:|- unite_pairs (TUnion _ _) _ << TPair _ _
       |- _ =>
           rewrite unite_pairs_union_t in Hsub; destruct (in_nf_union__inv _ _ Hnf1) as [Hnf11 Hnf12]; apply sub_r_union_l__inv in Hsub;
            destruct Hsub as [Hsub1 Hsub2]; specialize (IHt1_1 _ _ _ Hsub1 Hnf11 Hnf2); specialize (IHt1_2 _ _ _ Hsub2 Hnf12 Hnf2); split;
            tauto || constructor; tauto
     end ])).
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
Lemma sub_r__mk_nf_sub_r : forall t t' : ty, |- t << t' -> |- MkNF( t) << MkNF( t').
Proof.
(intros t t' Hsub; induction Hsub; try (solve [ simpl; constructor ])).
-
(simpl).
(apply unite_pairs_of_nf__preserves_sub_r; assumption || apply mk_nf__in_nf).
-
(simpl).
(constructor; assumption).
-
(apply SR_UnionR1; assumption).
-
(apply SR_UnionR2; assumption).
-
(simpl).
(constructor; assumption).
-
(rewrite <- mk_nf__idempotent).
assumption.
Qed.
Lemma sub_r_nf__trans2 :
  forall tm1 tm2 : ty,
  |- tm1 << tm2 -> InNF( tm1) -> InNF( tm2) -> (forall tl : ty, |- tl << tm1 -> |- tl << tm2) /\ (forall tr : ty, |- tm2 << tr -> |- tm1 << tr).
Proof.
(intros tm1 tm2 Hsub).
(induction Hsub; intros Hnfm1 Hnfm2).
-
tauto.
-
(destruct (in_nf_pair__inv _ _ Hnfm1) as [Hnfm11 Hnfm12]).
(destruct (in_nf_pair__inv _ _ Hnfm2) as [Hnfm21 Hnfm22]).
(destruct IHHsub1 as [IHHsub11 IHHsub12]; try assumption).
(destruct IHHsub2 as [IHHsub21 IHHsub22]; try assumption).
(split; intros tx Hsub'; [ remember (TPair t1 t2) as ty eqn:Heqy  | remember (TPair t1' t2') as ty eqn:Heqy  ]; induction Hsub'; inversion Heqy;
  subst; try (solve [ constructor; auto ])).
+
(apply IHHsub').
(apply mk_nf_nf__equal; assumption).
(apply mk_nf__in_nf).
-
(destruct (in_nf_union__inv _ _ Hnfm1) as [Hnfm11 Hnfm12]).
(destruct IHHsub1 as [IHHsub11 IHHsub12]; try assumption).
(destruct IHHsub2 as [IHHsub21 IHHsub22]; try assumption).
(split; intros tx Hsub'; try (solve [ constructor; auto ])).
+
(remember (TUnion t1 t2) as ty eqn:Heqy ).
(induction Hsub'; inversion Heqy; subst; try (solve [ (constructor; tauto) || auto ])).
-
(destruct (in_nf_union__inv _ _ Hnfm2) as [Hnfm21 Hnfm22]).
(destruct IHHsub as [IHHsub1 IHHsub2]; try assumption).
(split; intros tx Hsub'; try (solve [ constructor; auto ])).
+
(apply sub_r_union_l__inv in Hsub').
(destruct Hsub'; auto).
-
(destruct (in_nf_union__inv _ _ Hnfm2) as [Hnfm21 Hnfm22]).
(destruct IHHsub as [IHHsub1 IHHsub2]; try assumption).
(split; intros tx Hsub'; try (solve [ constructor; auto ])).
+
(apply sub_r_union_l__inv in Hsub').
(destruct Hsub'; auto).
-
(pose proof (in_nf_ref__inv _ Hnfm1) as Hnf1).
(pose proof (in_nf_ref__inv _ Hnfm2) as Hnf2).
(destruct IHHsub1 as [IHHsub11 IHHsub12]; try assumption).
(destruct IHHsub2 as [IHHsub21 IHHsub22]; try assumption).
(split; intros tx Hsub'; [ remember (TRef t) as ty eqn:Heqy  | remember (TRef t') as ty eqn:Heqy  ]; induction Hsub'; inversion Heqy; subst;
  try (solve [ constructor; auto ])).
+
(apply IHHsub').
(apply mk_nf_nf__equal; assumption).
(apply mk_nf__in_nf).
-
(split; intros tx Hsub'; apply SR_NormalForm; apply IHHsub; try tauto || apply mk_nf__in_nf).
(apply sub_r__mk_nf_sub_r; assumption).
Qed.
Lemma sub_r__trans2 :
  forall tm1 tm2 : ty, |- tm1 << tm2 -> (forall tl : ty, |- tl << tm1 -> |- tl << tm2) /\ (forall tr : ty, |- tm2 << tr -> |- tm1 << tr).
Proof.
(intros tm1 tm2 Hsub).
(induction Hsub).
-
tauto.
-
(destruct IHHsub1 as [IHHsub11 IHHsub12]).
(destruct IHHsub2 as [IHHsub21 IHHsub22]).
(split; intros tx Hsub'; [ remember (TPair t1 t2) as ty eqn:Heqy  | remember (TPair t1' t2') as ty eqn:Heqy  ]; induction Hsub'; inversion Heqy;
  subst; try (solve [ constructor; auto ])).
+
(apply SR_NormalForm).
(assert (Hsub : |- TPair t1 t2 << TPair t1' t2') by (constructor; assumption)).
(apply sub_r__mk_nf_sub_r in Hsub).
(apply sub_r_nf__trans2 with (MkNF( TPair t1' t2')); assumption || apply mk_nf__in_nf).
-
(destruct IHHsub1 as [IHHsub11 IHHsub12]).
(destruct IHHsub2 as [IHHsub21 IHHsub22]).
(split; intros tx Hsub'; try (solve [ constructor; auto ])).
+
(remember (TUnion t1 t2) as ty eqn:Heqy ).
(induction Hsub'; inversion Heqy; subst; try (solve [ (constructor; tauto) || auto ])).
-
(destruct IHHsub as [IHHsub1 IHHsub2]).
(split; intros tx Hsub'; try (solve [ constructor; auto ])).
+
(apply sub_r_union_l__inv in Hsub').
(destruct Hsub'; auto).
-
(destruct IHHsub as [IHHsub1 IHHsub2]; try assumption).
(split; intros tx Hsub'; try (solve [ constructor; auto ])).
+
(apply sub_r_union_l__inv in Hsub').
(destruct Hsub'; auto).
-
(destruct IHHsub1 as [IHHsub11 IHHsub12]).
(destruct IHHsub2 as [IHHsub21 IHHsub22]).
(split; intros tx Hsub'; [ remember (TRef t) as ty eqn:Heqy  | remember (TRef t') as ty eqn:Heqy  ]; induction Hsub'; inversion Heqy; subst;
  try (solve [ constructor; auto ])).
+
(apply SR_NormalForm).
(assert (Hsub : |- TRef t << TRef t') by (constructor; assumption)).
(apply sub_r__mk_nf_sub_r in Hsub).
(apply sub_r_nf__trans2 with (MkNF( TRef t')); assumption || apply mk_nf__in_nf).
-
(split; intros tx Hsub'; apply SR_NormalForm; apply IHHsub; try tauto || apply mk_nf__in_nf).
(apply sub_r__mk_nf_sub_r; assumption).
Qed.
Lemma sub_r__reflexive : forall t : ty, |- t << t.
Proof.
(apply sub_r__rflxv).
Qed.
Lemma sub_r__transitive : forall t1 t2 t3 : ty, |- t1 << t2 -> |- t2 << t3 -> |- t1 << t3.
Proof.
(intros t1 t2 t3 Hsub1 Hsub2).
(destruct (sub_r__trans2 _ _ Hsub1) as [_ H]).
auto.
Qed.
Lemma unite_pairs__distr21 :
  forall t1 t21 t22 : ty, InNF( t1) -> |- unite_pairs t1 (TUnion t21 t22) << TUnion (unite_pairs t1 t21) (unite_pairs t1 t22).
Proof.
(intros t1 t21 t22 Hnf1).
generalize dependent t22.
generalize dependent t21.
(induction Hnf1; intros t21 t22).
-
(rewrite unite_pairs_atom_union; try assumption).
(* Failed. *)
