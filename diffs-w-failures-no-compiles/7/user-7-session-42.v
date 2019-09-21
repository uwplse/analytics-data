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
Set Silent.
Lemma sub_d__inv_depth_le : forall t t' : ty, |- t << t' -> | t | <= | t' |.
Proof.
(intros t t' Hsub).
(induction Hsub).
-
Unset Silent.
constructor.
Set Silent.
-
Unset Silent.
Show.
(apply Nat.le_trans with (| t2 |); assumption).
Set Silent.
-
Unset Silent.
Show.
(simpl).
(apply Nat.max_le_compat; assumption).
-
