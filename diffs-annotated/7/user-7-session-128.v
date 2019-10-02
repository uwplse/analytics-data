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
(destruct Hsem1 as [w21 Hsem1]; destruct Hsem2 as [w22 Hsem2]).
exists (Nat.max w21 w22).
(intros v Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(specialize (Hsem1 _ Hm1); specialize (Hsem2 _ Hm2)).
(apply match_ty_pair; eapply match_ty__ge_w; try eassumption).
(apply Nat.le_max_l).
(apply Nat.le_max_r).
Qed.
Lemma sem_sub_pair : forall t1 t2 t1' t2' : ty, ||- [t1]<= [t1'] -> ||- [t2]<= [t2'] -> ||- [TPair t1 t2]<= [TPair t1' t2'].
Proof.
(intros t1 t2 t1' t2' Hsem1 Hsem2 k).
(apply sem_sub_k_pair; auto).
Qed.
Lemma sem_sub_k_union : forall (k : nat) (t1 t2 t' : ty), ||-[ k][t1]<= [t'] -> ||-[ k][t2]<= [t'] -> ||-[ k][TUnion t1 t2]<= [t'].
Proof.
(intros k t1 t2 t' Hsem1 Hsem2).
(intros w1).
(specialize (Hsem1 w1); specialize (Hsem2 w1)).
(destruct Hsem1 as [w21 Hsem1]; destruct Hsem2 as [w22 Hsem2]).
exists (Nat.max w21 w22).
(intros v Hm).
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ specialize (Hsem1 _ Hm) | specialize (Hsem2 _ Hm) ]; eapply match_ty__ge_w; try eassumption).
(apply Nat.le_max_l).
(apply Nat.le_max_r).
Qed.
Lemma sem_sub_k_union_1 : forall (k : nat) (t t1' t2' : ty), ||-[ k][t]<= [t1'] -> ||-[ k][t]<= [TUnion t1' t2'].
Proof.
(intros k t t1' t2' Hsem).
(intros w1).
specialize (Hsem w1).
(destruct Hsem as [w2 Hsem]).
exists w2.
(intros v Hm).
(apply match_ty_union_1).
(apply Hsem; assumption).
Qed.
Lemma sem_sub_k_union_2 : forall (k : nat) (t t1' t2' : ty), ||-[ k][t]<= [t2'] -> ||-[ k][t]<= [TUnion t1' t2'].
Proof.
(intros k t t1' t2' Hsem).
(intros w1).
specialize (Hsem w1).
(destruct Hsem as [w2 Hsem]).
exists w2.
(intros v Hm).
(apply match_ty_union_2).
(apply Hsem; assumption).
Qed.
Lemma sem_sub_union : forall t1 t2 t' : ty, ||- [t1]<= [t'] -> ||- [t2]<= [t'] -> ||- [TUnion t1 t2]<= [t'].
Proof.
(intros t1 t2 t' Hsem1 Hsem2 k).
(apply sem_sub_k_union; auto).
Qed.
Lemma sem_sub_union_1 : forall t t1' t2' : ty, ||- [t]<= [t1'] -> ||- [t]<= [TUnion t1' t2'].
Proof.
(intros t t1' t2' Hsem k).
(apply sem_sub_k_union_1; auto).
Qed.
Lemma sem_sub_union_2 : forall t t1' t2' : ty, ||- [t]<= [t2'] -> ||- [t]<= [TUnion t1' t2'].
Proof.
(intros t t1' t2' Hsem k).
(apply sem_sub_k_union_2; auto).
Qed.
Lemma sem_sub_k_pair__inv :
  forall (k : nat) (t1 t2 t1' t2' : ty), ||-[ k][TPair t1 t2]<= [TPair t1' t2'] -> ||-[ k][t1]<= [t1'] /\ ||-[ k][t2]<= [t2'].
Proof.
(intros k t1 t2 t1' t2' Hsem).
(split; intros w1; specialize (Hsem w1); destruct Hsem as [w2 Hsem]; destruct (match_ty__exists_w_v t1 k) as [w21 [v1 Hm1]];
  destruct (match_ty__exists_w_v t2 k) as [w22 [v2 Hm2]]; [ exists (Nat.max w2 w22) | exists (Nat.max w2 w21) ]; intros v Hm).
-
(* Failed. *)
