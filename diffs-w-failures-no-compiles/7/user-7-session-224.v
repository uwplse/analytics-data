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
subst.
(rewrite b_subst_exist_neq in Hm; try assumption).
(apply match_ty_exist__0_inv in Hm).
contradiction.
