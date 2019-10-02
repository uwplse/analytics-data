Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250b.BaseDefs.
Require Import BetaJulia.Sub0250b.BaseProps.
Require Import BetaJulia.Sub0250b.DeclSubProps.
Require Import BetaJulia.Sub0250b.RedSubProps.
Require Import BetaJulia.BasicTactics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Close Scope btj_scope.
Open Scope btjr_scope.
Theorem sub_r__sound : forall t1 t2 : ty, |- t1 << t2 -> (|- t1 << t2)%btj.
Proof.
(intros t1 t2 Hsub; induction Hsub; try (solve [ constructor; assumption ])).
-
(apply union_right_1; assumption).
-
(apply union_right_2; assumption).
-
(apply SD_Trans with (MkNF( t))).
(apply mk_nf__sub_d2).
assumption.
Qed.
Theorem sub_r__complete : forall t1 t2 : ty, (|- t1 << t2)%btj -> |- t1 << t2.
Proof.
(intros t1 t2 Hsub; induction Hsub; try (solve [ constructor; assumption ])).
-
(apply sub_r__reflexive).
-
(apply sub_r__transitive with t2; assumption).
-
(apply SR_UnionR1; apply sub_r__reflexive).
-
(apply SR_UnionR2; apply sub_r__reflexive).
-
(apply mk_nf_sub_r__sub_r).
(apply mk_nf__distr11).
-
(apply mk_nf_sub_r__sub_r).
(apply mk_nf__distr21).
Qed.
Theorem sub_r__decidable : forall t1 t2 : ty, Decidable.decidable (|- t1 << t2).
Proof.
(intros t1 t2).
(assert (Hnf1 : InNF( MkNF( t1))) by apply mk_nf__in_nf).
(assert (Hnf2 : InNF( MkNF( t2))) by apply mk_nf__in_nf).
specialize (Hdec _ Hnf2).
(destruct Hdec as [Hdec| Hdec]).
-
(left; apply mk_nf_sub_r__sub_r; assumption).
-
(right; intros Hcontra).
(apply mk_nf_sub_r__sub_r in Hcontra).
(* Failed. *)
