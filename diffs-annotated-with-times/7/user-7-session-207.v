Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
Lemma build_v_full :
  forall (X X' : id) (tx : ty) (w : nat) (t v : ty),
  |-[ w] v <$ [BX := tx] t ->
  exists v' : ty,
    |-[ w] v' <$ [BX := TFVar X'] t /\
    (forall (w' : nat) (t' : ty),
     |-[ w'] v' <$ t' -> (not_f_free_in_ty X' t' -> |-[ w'] v <$ t') /\ (f_free_in_ty X' t' -> |-[ w'] v <$ [FX' := tx] t')).
Proof.
(intros X X' tx).
(induction w; induction t; intros v Hm).
-
(rewrite b_subst_cname in *).
exists v.
split.
assumption.
(apply match_ty_cname__inv in Hm; subst).
(induction w'; induction t'; intros Hm'; try (solve [ contradiction || tauto ])).
+
(rewrite f_subst_union).
(apply match_ty_union__inv in Hm'; destruct Hm' as [Hm'| Hm']; [ pose proof IHt'1 as IHt' | pose proof IHt'2 as IHt' ]; specialize (IHt' Hm');
  destruct IHt' as [IHt'a IHt'b]; split; intros HX').
*
(destruct (not_f_free_in_ty_union__inv _ _ _ HX') as [HX'1 HX'2]).
(apply match_ty_union_1; auto).
*
(destruct (f_free_in_ty__dec X' t'1) as [HXt'1| HXt'1]).
{
(apply match_ty_union_1; auto).
}
{
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-09-04 08:58:44.870000.*)
