Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Unset Silent.
Require Import BetaJulia.Sub0250a.MatchProps.
Set Silent.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt_scope.
Open Scope btjm_scope.
Open Scope btjnf_scope.
Open Scope btjd_scope.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
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
Unset Silent.
(apply Nat.le_max_r).
Set Silent.
-
(simpl).
Unset Silent.
(rewrite max_baca_eq_bca).
constructor.
Set Silent.
-
(simpl).
(rewrite max_abac_eq_abc).
Unset Silent.
constructor.
Set Silent.
-
(simpl).
(apply le_n_S).
assumption.
Unset Silent.
Qed.
Set Silent.
Lemma sub_d_eq__inv_depth_eq : forall t t' : ty, |- t << t' -> |- t' << t -> | t | = | t' |.
Unset Silent.
Proof.
(intros t t' Hsub1 Hsub2).
Set Printing Width 148.
Set Printing Width 148.
(apply Nat.le_antisymm; apply sub_d__inv_depth_le; assumption).
Qed.
