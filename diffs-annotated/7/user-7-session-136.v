Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma sem_sub__sem_eq : forall t t' : ty, ||- [t]<= [t'] -> ||- [t']<= [t] -> ||- [t]= [t'].
Proof.
(intros t t' Hsem1 Hsem2 k).
(unfold sem_eq_k).
(* Failed. *)
