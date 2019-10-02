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
(* Failed. *)
