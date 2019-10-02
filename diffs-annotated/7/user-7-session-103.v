Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0270a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (k w : nat), |-[ k, w] v1 <$ t1 -> |-[ k, w] v2 <$ t2 -> |-[ k, w] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k w Hm1 Hm2).
(destruct k, w; split; assumption).
(* Auto-generated comment: Failed. *)
