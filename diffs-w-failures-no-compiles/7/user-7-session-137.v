Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Lemma sem_sub_k_exist_fresh_l : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][TExist X t]<= [t].
Proof.
(intros k X t).
Unset Silent.
(induction t; intros Hfresh).
Set Silent.
-
Unset Silent.
(intros w1).
exists w1.
(intros v Hm).
Set Printing Width 148.
Set Silent.
(destruct w1).
Unset Silent.
(apply match_ty_exist__0_inv in Hm; contradiction).
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(apply match_ty__ge_w; assumption).
