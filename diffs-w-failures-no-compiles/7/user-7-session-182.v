Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import BetaJulia.Sub0281a.BaseProps.
Require Import BetaJulia.Sub0281a.BaseMatchProps.
Require Import BetaJulia.Sub0281a.BaseSemSubProps.
Unset Silent.
Require Import Coq.Lists.List.
Set Silent.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma subst_nested :
  forall (X Y : id) (tX tY : ty), X <> Y -> fresh_in_ty Y tX -> forall t : ty, [X := tX] ([Y := tY] t) = [Y := [X := tX] tY] ([X := tX] t).
Proof.
(intros X Y tX tY Hneq HYfresh t).
(induction t; try reflexivity).
-
(repeat rewrite subst_pair).
(rewrite IHt1, IHt2).
reflexivity.
-
(repeat rewrite subst_union).
(rewrite IHt1, IHt2).
reflexivity.
-
(destruct (beq_idP Y i) as [HY| HY]).
+
subst.
(destruct (beq_idP X i) as [HX| HX]).
*
subst.
contradiction.
*
Unset Silent.
(rewrite subst_exist_eq).
(rewrite subst_id).
