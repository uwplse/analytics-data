Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import BetaJulia.BasicTactics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Close Scope btjm.
Open Scope btjmi.
Lemma match_ty_i_pair : forall (v1 v2 t1 t2 : ty) (k : nat), |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k Hm1 Hm2).
(destruct k; split; assumption).
Qed.
Lemma match_ty_i_union_1 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t1 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; left; assumption).
Qed.
Lemma match_ty_i_union_2 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t2 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; right; assumption).
Qed.
Lemma match_ty_i_cname__inv : forall (v : ty) (c : cname) (k : nat), |-[ k] v <$ TCName c -> v = TCName c.
Proof.
(intros v; induction v; try (solve [ intros c k Hm; destruct k; contradiction ])).
(intros c0 k Hm).
(destruct k; simpl in Hm; subst; reflexivity).
Qed.
Lemma match_ty_i_pair__inv :
  forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k] v1 <$ t1 /\ |-[ k] v2 <$ t2.
Proof.
(intros v; induction v; try (solve [ intros t1 t2 k Hm; destruct k; contradiction ])).
(intros t1 t2 k Hm).
exists v1,v2.
(split; try reflexivity).
(destruct k; simpl in Hm; assumption).
Qed.
Lemma match_ty_i_union__inv : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ TUnion t1 t2 -> |-[ k] v <$ t1 \/ |-[ k] v <$ t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; assumption).
Qed.
Lemma match_ty_i_ref__weak_inv : forall (v t : ty) (k : nat), |-[ k] v <$ TRef t -> exists t' : ty, v = TRef t'.
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; contradiction ])).
clear IHv.
(intros t k).
(intros Hm).
exists v.
reflexivity.
Qed.
Lemma match_ty_i_ref__inv : forall (v t : ty) (k : nat), |-[ S k] v <$ TRef t -> exists t' : ty, v = TRef t' /\ ||-[ k][t']= [t].
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; contradiction ])).
clear IHv.
(intros t k Hm).
(simpl in Hm).
exists v.
auto.
Qed.
Theorem match_ty_i__value_type_l : forall (v t : ty) (k : nat), |-[ k] v <$ t -> value_type v.
Proof.
(intros v t).
generalize dependent v.
(induction t; intros k v Hm).
-
(apply match_ty_i_cname__inv in Hm; subst).
constructor.
-
(apply match_ty_i_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(constructor; [ eapply IHt1 | eapply IHt2 ]; eauto).
-
(apply match_ty_i_union__inv in Hm; destruct Hm as [Hm1| Hm2]; [ eapply IHt1 | eapply IHt2 ]; eauto).
-
(apply match_ty_i_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
constructor.
Qed.
Lemma sem_sub_k_i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t3] -> ||-[ k][t1]<= [t3].
Proof.
auto with DBBetaJulia.
Qed.
Lemma sem_sub_k_i__sem_eq_k_i : forall (k : nat) (t1 t2 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t1] -> ||-[ k][t1]= [t2].
Proof.
(intros k t1 t2 Hsem1 Hsem2).
(split; auto).
Qed.
Lemma sem_eq_k_i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]= [t2] -> ||-[ k][t2]= [t3] -> ||-[ k][t1]= [t3].
Proof.
(intros k t1 t2 t3 Hsem1 Hsem2).
(unfold sem_eq_k in *).
(intros v).
specialize (Hsem1 v).
specialize (Hsem2 v).
tauto.
Qed.
Theorem nf_sem_sub_i__sub_d : forall t : ty, InNF( t) -> forall t' : ty, ||- [t]<= [t'] -> |- t << t'.
Proof.
(intros t Hnf t' Hsem).
(* Auto-generated comment: Failed. *)
