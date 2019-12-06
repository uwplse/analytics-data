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
Lemma match_ty_subst_fresh : forall (X : id) (s : ty) (w : nat) (t v : ty), fresh_in_ty X t -> |-[ w] v <$ t -> |-[ w] v <$ [X := s] t.
Proof.
(intros X s; induction w; induction t; intros v HX Hm; try (solve [ rewrite subst_cname in *; assumption | rewrite subst_ev in *; assumption ])).
-
(rewrite subst_pair).
(destruct (fresh_in_ty_pair__inv _ _ _ HX) as [HX1 HX2]).
(apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [heq [Hm1 Hm2]]]]; subst; apply match_ty_pair; tauto).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-09-02 09:08:20.010000.*)

