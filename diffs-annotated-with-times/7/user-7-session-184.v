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
  forall (X X' : id) (w : nat) (t v : ty) (tx : ty),
  |-[ w] v <$ [X := tx] t ->
  exists v' : ty,
    |-[ w] v' <$ [X := TVar X'] t /\
    (forall (w' : nat) (t' : ty), |-[ w'] v' <$ t' -> (fresh_in_ty X' t' -> |-[ w'] v <$ t') /\ (free_in_ty X' t' -> |-[ w'] v <$ [X' := tx] t')).
Proof.
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-09-02 08:17:08.050000.*)

