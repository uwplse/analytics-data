Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseProps.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import BetaJulia.Sub0280a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
(induction t; intros Hfresh; intros w1; exists w1; intros v Hm; destruct w1; try (solve [ apply match_ty_exist__0_inv in Hm; contradiction ])).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
