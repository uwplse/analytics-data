Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma sem_sub_k_pair : forall (k : nat) (t1 t2 t1' t2' : ty), ||-[ k][t1]<= [t1'] -> ||-[ k][t2]<= [t2'] -> ||-[ k][TPair t1 t2]<= [TPair t1' t2'].
Proof.
(intros k t1 t2 t1' t2' Hsem1 Hsem2).
(intros w1).
(specialize (Hsem1 w1); specialize (Hsem2 w1)).
exists (Nat.max w21 w22).
specialize (Hsem1 _ Hm1).
(* Failed. *)
