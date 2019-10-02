Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import BetaJulia.Sub0281a.BaseProps.
Require Import BetaJulia.Sub0281a.BaseMatchProps.
Require Import BetaJulia.Sub0281a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma build_v_full :
  forall (X X' : id) (tx : ty) (w : nat) (t v : ty),
  |-[ w] v <$ [X := tx] t ->
  exists v' : ty,
    |-[ w] v' <$ [X := TVar X'] t /\
    (forall (w' : nat) (t' : ty), |-[ w'] v' <$ t' -> (fresh_in_ty X' t' -> |-[ w'] v <$ t') /\ (free_in_ty X' t' -> |-[ w'] v <$ [X' := tx] t')).
Proof.
(intros X X' tx).
(induction w; induction t; intros v Hm).
-
(rewrite subst_cname in *).
exists v.
split.
assumption.
(induction w'; induction t'; intros Hm'; try (solve [ destruct v; contradiction || tauto ])).
+
(apply match_ty_union__inv in Hm'; destruct Hm' as [Hm'| Hm']; [ pose proof IHt'1 as IHt' | pose proof IHt'2 as IHt' ]; specialize (IHt' Hm');
  destruct IHt' as [IHt'a IHt'b]; split; intros HX').
*
(destruct (fresh_in_ty_union__inv _ _ _ HX') as [HX'1 HX'2]).
(apply match_ty_union_1; auto).
*
(destruct (free_in_ty_union__inv _ _ _ HX') as [HX'| HX']).
(* Auto-generated comment: Failed. *)
