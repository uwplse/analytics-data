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
Lemma sem_sub_k_exist_pair : forall (k : nat) (X : id) (t1 t2 : ty), ||-[ k][TExist X (TPair t1 t2)]<= [TPair (TExist X t1) (TExist X t2)].
Proof.
(intros k X t1 t2 w1).
exists w1.
(intros v Hm).
(destruct w1).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
(simpl in Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(apply match_ty_pair; apply match_ty_exist; exists tx; assumption).
Qed.
Lemma sem_sub_exist_pair : forall (X : id) (t1 t2 : ty), ||- [TExist X (TPair t1 t2)]<= [TPair (TExist X t1) (TExist X t2)].
Proof.
(intros X t1 t2 k).
(apply sem_sub_k_exist_pair).
Qed.
Lemma match_ty_ev__match_ty_any :
  forall (k w : nat) (X : id) (t : ty), fresh_in_ty X t -> |-[ k, w] TEV X <$ t -> forall v : ty, value_type v -> |-[ k, w] v <$ t.
Proof.
(intros k w X t HX Hm v Hv).
(induction t).
-
(apply match_ty_cname__inv in Hm).
(inversion Hm).
-
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq _]]]).
(inversion Heq).
-
(apply match_ty_union__inv in Hm).
(destruct (fresh_in_ty_union__inv _ _ _ HX) as [HX1 HX2]).
(destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
-
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]).
(inversion Heq).
-
(destruct w).
+
(apply match_ty_exist__0_inv in Hm; contradiction).
+
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hm]).
