Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0260a.BaseDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma cname_eq__decidable : forall n1 n2 : cname, Decidable.decidable (n1 = n2).
Proof.
(intros n1 n2; destruct n1; destruct n2; (left; reflexivity) || (right; intros H; inversion H)).
Qed.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (k : nat), |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k Hm1 Hm2).
(destruct k; split; assumption).
Qed.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t1 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; left; assumption).
Qed.
Lemma match_ty_union_2 : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ t2 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; right; assumption).
Qed.
Lemma match_ty_exist : forall (v : ty) (X : id) (t : ty) (k : nat), (exists tx : ty, |-[ k] v <$ [X := tx] t) -> |-[ S k] v <$ TExist X t.
Proof.
(intros v X t k Hex).
(destruct v; assumption).
Qed.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (k : nat), |-[ k] v <$ TCName c -> v = TCName c.
Proof.
(intros v; induction v; try (solve [ intros c k Hm; destruct k; contradiction ])).
(intros c0 k Hm).
(destruct k; simpl in Hm; subst; reflexivity).
Qed.
Lemma match_ty_pair__inv :
  forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k] v1 <$ t1 /\ |-[ k] v2 <$ t2.
Proof.
(intros v; induction v; try (solve [ intros t1 t2 k Hm; destruct k; contradiction ])).
(intros t1 t2 k Hm).
exists v1,v2.
(split; try reflexivity).
(destruct k; simpl in Hm; assumption).
Qed.
Lemma match_ty_union__inv : forall (v t1 t2 : ty) (k : nat), |-[ k] v <$ TUnion t1 t2 -> |-[ k] v <$ t1 \/ |-[ k] v <$ t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; assumption).
Qed.
Lemma match_ty_ref__weak_inv : forall (v t : ty) (k : nat), |-[ k] v <$ TRef t -> exists t' : ty, v = TRef t'.
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; contradiction ])).
clear IHv.
(intros t k).
(intros Hm).
exists v.
reflexivity.
Qed.
Lemma match_ty_ref__inv : forall (v t : ty) (k : nat), |-[ S k] v <$ TRef t -> exists t' : ty, v = TRef t' /\ ||-[ k][t']= [t].
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; contradiction ])).
clear IHv.
Lemma not_sem_sub__refeXrefX_eYrefrefY : ~ ||- [TRef (TExist vX (TRef tX))]<= [TExist vY (TRef (TRef tY))].
(intros X t1 t2 k v Hm).
(destruct k).
-
(apply match_ty_exist__0_inv in Hm).
(destruct Hm as [Hv [tx Heqx]]; subst).
(simpl in Hv).
contradiction.
(* Failed. *)
