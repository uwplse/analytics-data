Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Set Printing Width 148.
Set Printing Width 148.
Lemma fresh_in_ty_var__neq : forall X Y : id, fresh_in_ty X (TVar Y) -> X <> Y.
Proof.
Set Silent.
(intros X Y H).
Unset Silent.
(unfold fresh_in_ty, fresh in H).
(simpl in H).
(destruct (beq_idP X Y)).
-
Show.
Set Printing Width 148.
Check IdSetFacts.singleton_2.
Set Printing Width 148.
Set Silent.
(pose proof (IdSetFacts.singleton_2 e)).
Unset Silent.
Show.
