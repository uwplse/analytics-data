Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm_scope.
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
Lemma match_ty_ref__inv :
  forall (v t : ty) (k : nat),
  |-[ S k] v <$ TRef t -> exists t' : ty, v = TRef t' /\ (inv_depth t <= k /\ inv_depth t' = inv_depth t) /\ ||-[ k][t']= [t].
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; contradiction ])).
clear IHv.
(intros t k Hm).
(simpl in Hm).
(exists v; auto).
Qed.
Lemma match_ty__value_type_l : forall (v t : ty) (k : nat), |-[ k] v <$ t -> value_type v.
Proof.
(intros v t).
generalize dependent v.
(induction t; intros v k Hm).
-
(apply match_ty_cname__inv in Hm; subst).
constructor.
-
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
(constructor; eauto).
-
(apply match_ty_union__inv in Hm).
(destruct Hm; eauto).
-
(destruct k).
(destruct v; contradiction).
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq _]]; subst).
constructor.
Qed.
Lemma match_ty__inv_depth_l : forall (v t : ty) (k : nat), |-[ k] v <$ t -> | v | <= k /\ | v | <= | t |.
Proof.
(intros v; induction v).
-
(intros t k Hm).
(simpl).
(split; apply Nat.le_0_l).
-
(intros t; induction t; intros k Hm; try (solve [ destruct k; contradiction ])).
+
clear IHt1 IHt2.
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1' [v2' [Heq [Hm1 Hm2]]]]).
(inversion Heq; subst).
(simpl).
(specialize (IHv1 _ _ Hm1); specialize (IHv2 _ _ Hm2)).
split.
(apply Nat.max_lub; tauto).
(apply Nat.max_le_compat; tauto).
+
clear IHv1 IHv2.
(apply match_ty_union__inv in Hm).
(destruct Hm as [Hm| Hm]; [ specialize (IHt1 _ Hm) | specialize (IHt2 _ Hm) ]; split; try tauto; rewrite inv_depth_union;
  [ apply Nat.le_trans with (| t1 |) | apply Nat.le_trans with (| t2 |) ]; try tauto; apply Max.le_max_l || apply Max.le_max_r).
-
(intros t k Hm).
(apply match_ty__value_type_l in Hm).
(* Auto-generated comment: Failed. *)

