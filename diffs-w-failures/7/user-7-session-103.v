Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Set Printing Width 148.
Set Silent.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (k w : nat), |-[ k, w] v1 <$ t1 -> |-[ k, w] v2 <$ t2 -> |-[ k, w] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k w Hm1 Hm2).
(destruct k, w; split; assumption).
Unset Silent.
Set Printing Width 148.
Set Silent.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t1 -> |-[ k, w] v <$ TUnion t1 t2.
Proof.
Unset Silent.
(intros v t1 t2 k w Hm).
Set Printing Width 148.
Set Printing Width 148.
(destruct k, w; destruct v; left; assumption).
