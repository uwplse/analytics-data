Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Unset Silent.
Set Printing Width 148.
Open Scope btjm.
Set Printing Width 148.
Theorem sub_d__semantic_sound : forall t1 t2 : ty, |- t1 << t2 -> ||- [t1]<= [t2].
Set Silent.
Proof.
Unset Silent.
(intros t1 t2 Hsub).
(unfold sem_sub).
(induction Hsub; intros k v Hm).
Set Silent.
-
Unset Silent.
assumption.
Set Silent.
-
Unset Silent.
Show.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
(unfold sem_sub_k in *).
Unset Silent.
auto.
Set Silent.
-
Unset Silent.
Show.
(apply match_ty_pair__inv in Hm).
