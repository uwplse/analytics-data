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
(intros k X t Hfresh).
(intros w1).
exists w1.
(intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(rewrite subs_fresh_in_ty in Hm; try assumption).
(eapply match_ty__ge_w).
eassumption.
(repeat constructor).
Qed.
Lemma sem_sub_k_exist_fresh_r : forall (k : nat) (X : id) (t : ty), fresh_in_ty X t -> ||-[ k][t]<= [TExist X t].
Proof.
(intros k X t Hfresh).
(intros w1).
exists (S w1).
(intros v Hm).
(apply match_ty_exist).
exists (TEV X).
(rewrite subs_fresh_in_ty; assumption).
Qed.
Lemma sem_sub_exist_fresh_l : forall (X : id) (t : ty), fresh_in_ty X t -> ||- [TExist X t]<= [t].
Proof.
(intros X t Hfresh k).
(apply sem_sub_k_exist_fresh_l).
assumption.
Qed.
Lemma sem_sub_k_fresh_var__sem_sub_exist :
  forall (X : id) (t t' : ty) (X' : id), fresh_in_ty X' t' -> ||- [[X := TVar X'] t]<= [t'] -> ||- [TExist X t]<= [t'].
Proof.
(intros X t).
(induction t).
-
(intros t' X' Hfresh Hsem).
(simpl in *).
(apply sem_sub__trans with (TCName c); try assumption).
(apply sem_sub_exist_fresh_l).
(unfold fresh_in_ty, fresh).
(simpl).
Search -IdSet.empty.
Check IdSetFacts.empty_iff.
(pose proof (IdSetFacts.empty_iff X) as H).
tauto.
-
(intros t' X' Hfresh Hsem).
(simpl in *).
(induction t').
+
(intros k w1).
specialize (Hsem k w1).
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-27 09:04:24.230000.*)

