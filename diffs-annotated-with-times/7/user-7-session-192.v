Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import BetaJulia.Sub0281a.BaseProps.
Require Import BetaJulia.Sub0281a.BaseMatchProps.
Require Import BetaJulia.Sub0281a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma fresh_in_ty_var__neq : forall X Y : id, fresh_in_ty X (TVar Y) -> X <> Y.
Proof.
(intros X Y H).
(unfold fresh_in_ty, fresh in H).
(simpl in H).
(destruct (beq_idP X Y)).
-
Check IdSetFacts.singleton_2.
(pose proof (IdSetFacts.singleton_2 e)).
contradiction.
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-09-02 09:14:21.840000.*)

