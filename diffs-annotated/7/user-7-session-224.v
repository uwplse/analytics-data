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
  wf_ty tx ->
  b_free_in_ty X t ->
  |-[ w] v <$ [BX := tx] t ->
  exists v' : ty,
    |-[ w] v' <$ [BX := TFVar X'] t /\
    (forall (w' : nat) (t' : ty),
     |-[ w'] v' <$ t' -> (not_f_free_in_ty X' t' -> |-[ w'] v <$ t') /\ (f_free_in_ty X' t' -> exists w2, |-[ w2] v <$ [FX' := tx] t')).
exists 0.
exists (S w').
(apply match_ty_union_1).
(rewrite f_subst_not_b_free_in_ty; auto).
}
}
{
(destruct (not_f_free_in_ty_union__inv _ _ _ HX') as [HX'1 HX'2]).
(apply match_ty_union_2; auto).
}
{
(destruct (f_free_in_ty__dec X' t'2) as [HXt'2| HXt'2]).
{
specialize (IHt'b HXt'2).
(destruct IHt'b as [w2 IHt'b]).
exists w2.
(apply match_ty_union_2; auto).
}
{
exists 0.
(* Failed. *)
