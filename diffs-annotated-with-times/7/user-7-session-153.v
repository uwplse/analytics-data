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
Lemma build_v : forall (X X' : id) (w : nat) (tx t v : ty), |-[ w] v <$ [X := tx] t -> exists v' : ty, |-[ w] v' <$ [X := TVar X'] t.
Proof.
(intros X X' w tx t).
(induction t; intros v Hm).
-
exists (TCName c).
(apply match_ty_cname).
-
(simpl in *).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(destruct (IHt1 _ Hm1) as [v1' Hm1']).
(destruct (IHt2 _ Hm2) as [v2' Hm2']).
exists (TPair v1' v2').
(apply match_ty_pair; assumption).
-
(simpl in *).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ destruct (IHt1 _ Hm) as [v' Hm'] | destruct (IHt2 _ Hm) as [v' Hm'] ]; exists v';
  [ apply match_ty_union_1 | apply match_ty_union_2 ]; assumption).
-
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-29 08:54:40.280000.*)

