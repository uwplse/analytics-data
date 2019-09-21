Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Set Printing Width 148.
Theorem sub_r__sound : forall t1 t2 : ty, (|- t1 << t2)%btjr -> (|- t1 << t2)%btjd.
Set Silent.
Proof.
(intros t1 t2 Hsub; induction Hsub; try (solve [ constructor; assumption ])).
-
(apply union_right_1; assumption).
-
(apply union_right_2; assumption).
-
(apply SD_Trans with (MkNF( t))).
(apply mk_nf__sub_d_r).
assumption.
Qed.
Unset Silent.
Theorem sub_r__complete : forall t1 t2 : ty, (|- t1 << t2)%btjd -> (|- t1 << t2)%btjr.
Set Silent.
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
Unset Silent.
Qed.
