Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseProps.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import BetaJulia.Sub0280a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma sem_sub_k_exist_fresh_l : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][TExist X t]<= [t].
Proof.
(intros k X t).
(induction t; intros Hfresh).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-27 08:45:34.700000.*)

