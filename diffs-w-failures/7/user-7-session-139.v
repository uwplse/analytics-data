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
Lemma sem_sub_k_exist_fresh_l : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][TExist X t]<= [t].
Proof.
Set Printing Width 148.
(intros k X t Hfresh).
Show.
(intros w1).
exists w1.
Show.
(intros v Hm).
(destruct w1).
Show.
(apply match_ty_exist__0_inv in Hm; contradiction).
Show.
(apply match_ty_exist__inv in Hm).
Set Silent.
(destruct Hm as [tx Hm]).
Unset Silent.
(simpl in Hm).
(rewrite subs_fresh_in_ty in Hm).
