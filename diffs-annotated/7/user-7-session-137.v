Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseProps.
Require Import BetaJulia.Sub0280a.BaseMatchProps.
Require Import BetaJulia.Sub0280a.BaseSemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Lemma sem_sub_fresh_var__sem_sub_exist :
  forall (X : id) (t t' : ty) (X' : id), fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> ||- [TExist X t]<= [t'].
Lemma sem_eq_k_exist_fresh : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][TExist X t]= [t].
Proof.
(intros k X t).
(induction t; intros Hfresh).
-
(intros w1).
(* Failed. *)
