Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0260a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma match_ty_exist__0_inv : forall (v : ty) (X : id) (t : ty), |-[ 0] v <$ TExist X t -> |-[ 0] v <$ t.
Proof.
(intros v; induction v; intros X t Hm).
(simpl in Hm).
(* Failed. *)
