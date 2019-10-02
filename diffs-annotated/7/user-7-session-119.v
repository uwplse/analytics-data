Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseProps.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Theorem sub_d__semantic_sound : forall t1 t2 : ty, |- t1 << t2 -> ||- [t1]<= [t2].
Proof.
(intros t1 t2 Hsub).
(induction Hsub).
-
(apply sem_sub__refl).
-
(apply sem_sub__trans).
(* Failed. *)
