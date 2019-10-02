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
Lemma sem_sub_k_exist_fresh_l : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][TExist X t]<= [t].
Proof.
(intros k X t).
(induction t; intros Hfresh; intros w1; exists w1; intros v Hm; destruct w1; try (solve [ apply match_ty_exist__0_inv in Hm; contradiction ])).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
-
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(destruct (fresh_in_ty_pair__inv X t1 t2 Hfresh) as [Hfresh1 Hfresh2]).
(rewrite (subs_fresh_in_ty _ _ Hfresh1) in Hm).
(rewrite (subs_fresh_in_ty _ _ Hfresh2) in Hm).
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(apply fresh_in_ty_ref__inv in Hfresh).
(rewrite (subs_fresh_in_ty _ _ Hfresh) in Hm).
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(* Failed. *)
