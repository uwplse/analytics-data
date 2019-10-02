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
(apply sub_r_nf_union_l__inv in Hsub2; try assumption).
Check unite_pairs_union_t.
Check sub_r_nf_union_l__inv.
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
constructor.
auto.
-
