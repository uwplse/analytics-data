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
Lemma sem_sub__sem_eq : forall t t' : ty, ||- [t]<= [t'] -> ||- [t']<= [t] -> ||- [t]= [t'].
Proof.
(intros t t' Hsem1 Hsem2 k).
(unfold sem_eq_k).
auto.
Qed.
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
Lemma match_ty_ref : forall (k w : nat) (t t' : ty), ||-[ k][t]= [t'] -> |-[ S k, w] TRef t <$ TRef t'.
Proof.
(intros k w t t' Hsem).
(destruct Hsem as [Hsem1 Hsem2]).
(destruct w; simpl; tauto).
Qed.
Lemma sem_sub_k_ref : forall (k : nat) (t t' : ty), ||-[ k][t]= [t'] -> ||-[ S k][TRef t]<= [TRef t'].
Proof.
(intros k t t' Hsem).
(intros w1).
exists w1.
(intros v Hm).
(apply match_ty_ref__inv in Hm).
(destruct Hm as [tx [Heq Href]]; subst).
(apply match_ty_ref).
(apply sem_eq_k__trans with t; assumption).
Qed.
Lemma sem_sub_ref : forall t t' : ty, ||- [t]= [t'] -> ||- [TRef t]<= [TRef t'].
Proof.
(intros t t' Hsem k).
(destruct k).
-
(intros w1).
exists w1.
(intros v Hm).
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [tx Heq]; subst).
(destruct w1; simpl; tauto).
-
(apply sem_sub_k_ref; auto).
Qed.
Lemma sem_sub_k_pair__inv :
  forall (k : nat) (t1 t2 t1' t2' : ty), ||-[ k][TPair t1 t2]<= [TPair t1' t2'] -> ||-[ k][t1]<= [t1'] /\ ||-[ k][t2]<= [t2'].
Proof.
(intros k t1 t2 t1' t2' Hsem).
(split; intros w1; destruct (match_ty__exists_w_v t1 k) as [w11 [v1 Hm1]]; destruct (match_ty__exists_w_v t2 k) as [w12 [v2 Hm2]];
  [ specialize (Hsem (Nat.max w1 w12)) | specialize (Hsem (Nat.max w1 w11)) ]; destruct Hsem as [w2 Hsem]; exists w2; intros v Hm;
  [ remember (Nat.max w1 w12) as w1' eqn:Heqw1'  | remember (Nat.max w1 w11) as w1' eqn:Heqw1'  ]).
-
(assert (Hmp : |-[ k, w1'] TPair v v2 <$ TPair t1 t2)).
{
(apply match_ty_pair; eapply match_ty__ge_w; try eassumption; subst; [ apply Nat.le_max_l | apply Nat.le_max_r ]).
}
specialize (Hsem _ Hmp).
(apply match_ty_pair_pair__inv in Hsem).
tauto.
-
(assert (Hmp : |-[ k, w1'] TPair v1 v <$ TPair t1 t2)).
{
(apply match_ty_pair; eapply match_ty__ge_w; try eassumption; subst; [ apply Nat.le_max_r | apply Nat.le_max_l ]).
}
specialize (Hsem _ Hmp).
(apply match_ty_pair_pair__inv in Hsem).
tauto.
Qed.
Lemma sem_sub_pair__inv : forall t1 t2 t1' t2' : ty, ||- [TPair t1 t2]<= [TPair t1' t2'] -> ||- [t1]<= [t1'] /\ ||- [t2]<= [t2'].
Proof.
(intros t1 t2 t1' t2' Hsem).
(split; intros k; specialize (Hsem k); pose proof (sem_sub_k_pair__inv _ _ _ _ _ Hsem); tauto).
Qed.
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
