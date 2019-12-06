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
Lemma sem_sub_exist_fresh : forall (X : id) (t : ty), fresh_in_ty X t -> ||- [TExist X t]= [t].
Proof.
(intros X t).
(induction t; intros Hfresh).
-
(intros k).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-27 08:39:12.990000.*)

