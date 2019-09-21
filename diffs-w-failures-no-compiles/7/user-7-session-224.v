Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0282a.BaseDefs.
Require Import BetaJulia.Sub0282a.BaseProps.
Require Import BetaJulia.Sub0282a.BaseMatchProps.
Require Import BetaJulia.Sub0282a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Set Printing Width 148.
Lemma build_v_full :
  forall (X X' : id) (tx : ty) (w : nat) (t v : ty),
  wf_ty tx ->
  b_free_in_ty X t ->
  |-[ w] v <$ [BX := tx] t ->
  exists v' : ty,
    |-[ w] v' <$ [BX := TFVar X'] t /\
    (forall (w' : nat) (t' : ty),
     |-[ w'] v' <$ t' -> (not_f_free_in_ty X' t' -> |-[ w'] v <$ t') /\ (f_free_in_ty X' t' -> exists w2, |-[ w2] v <$ [FX' := tx] t')).
Set Printing Width 148.
(induction w; induction t; intros v Hwftx HX Hm;
  try (solve [ unfold b_free_in_ty, free in HX; simpl in HX; rewrite IdSetFacts.empty_iff in HX; contradiction ])).
Show.
Set Silent.
Set Printing Width 148.
admit.
Show.
-
Show.
admit.
Show.
Set Silent.
-
Unset Silent.
Show.
(destruct (beq_idP X i)).
+
subst.
Show.
Set Printing Width 148.
(rewrite b_subst_exist_eq in Hm).
(apply match_ty_exist__0_inv in Hm).
contradiction.
+
Set Printing Width 148.
Set Silent.
subst.
(rewrite b_subst_exist_neq in Hm; try assumption).
(apply match_ty_exist__0_inv in Hm).
Unset Silent.
contradiction.
-
(destruct (beq_idP X i)).
+
subst.
(rewrite b_subst_bvar_eq in *).
exists (TEV X').
split.
reflexivity.
(induction w'; induction t'; intros Hm'; try (solve [ destruct v; contradiction || tauto ])).
Set Silent.
*
Unset Silent.
Set Silent.
(rewrite f_subst_union).
(apply match_ty_union__inv in Hm'; destruct Hm' as [Hm'| Hm']; [ pose proof IHt'1 as IHt' | pose proof IHt'2 as IHt' ]; specialize (IHt' Hm');
  destruct IHt' as [IHt'a IHt'b]; split; intros HX').
{
(destruct (not_f_free_in_ty_union__inv _ _ _ HX') as [HX'1 HX'2]).
(apply match_ty_union_1; auto).
}
{
(destruct (f_free_in_ty__dec X' t'1) as [HXt'1| HXt'1]).
{
(apply match_ty_union_1; auto).
