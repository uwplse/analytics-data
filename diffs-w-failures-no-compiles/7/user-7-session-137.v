Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Set Printing Width 148.
(induction t; intros Hfresh; intros w1; exists w1; intros v Hm; destruct w1; try (solve [ apply match_ty_exist__0_inv in Hm; contradiction ])).
Show.
Set Silent.
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(eapply match_ty__ge_w).
eassumption.
Unset Silent.
(repeat constructor).
Set Silent.
-
Unset Silent.
Show.
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
