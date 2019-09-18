Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
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
Set Silent.
Lemma sem_sub_fresh_var__sem_sub_exist :
  forall (X X' : id) (t t' : ty), IdSet.In X (FV t) -> fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> ||- [TExist X t]<= [t'].
Unset Silent.
Proof.
Set Silent.
(intros X X' t t').
Unset Silent.
generalize dependent t.
(induction t').
Set Silent.
-
Unset Silent.
Show.
admit.
-
admit.
-
admit.
-
