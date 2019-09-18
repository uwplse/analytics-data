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
Close Scope btjd_scope.
Unset Silent.
Open Scope btjr_scope.
Set Silent.
Unset Silent.
Theorem sub_r__sound : forall t1 t2 : ty, |- t1 << t2 -> (|- t1 << t2)%btjd.
Set Silent.
Proof.
(intros t1 t2 Hsub; induction Hsub; try (solve [ constructor; assumption ])).
-
(apply union_right_1; assumption).
-
(apply union_right_2; assumption).
-
Unset Silent.
(apply SD_Trans with (MkNF( t))).
(apply mk_nf__sub_d2).
