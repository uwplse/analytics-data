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
Set Printing Width 148.
Set Silent.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (k w : nat), |-[ k, w] v1 <$ t1 -> |-[ k, w] v2 <$ t2 -> |-[ k, w] TPair v1 v2 <$ TPair t1 t2.
Proof.
Unset Silent.
(intros v1 v2 t1 t2 k w Hm1 Hm2).
(destruct k, w; split; assumption).
Set Silent.
Qed.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t1 -> |-[ k, w] v <$ TUnion t1 t2.
Unset Silent.
Proof.
(intros v t1 t2 k w Hm).
Show.
(destruct k, w).
Set Printing Width 148.
(destruct v).
(left; assumption).
