Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Unset Silent.
Lemma sem_sub__sem_eq : forall t t' : ty, ||- [t]<= [t'] -> ||- [t']<= [t] -> ||- [t]= [t'].
Proof.
(intros t t' Hsem1 Hsem2 k).
Show.
Set Printing Width 148.
Set Printing Width 148.
(unfold sem_eq_k).
auto.
Show.
Qed.
