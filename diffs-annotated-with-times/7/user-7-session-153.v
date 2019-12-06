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
Lemma build_v : forall (X X' : id) (w : nat) (tx v t : ty), |-[ w] v <$ [X := tx] t -> exists v' : ty, |-[ w] v' <$ [X := TVar X'] t.
Proof.
(intros X X' w tx v t).
(induction t; intros Hm).
-
(apply match_ty_cname__inv in Hm; subst).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-29 08:50:35.300000.*)

