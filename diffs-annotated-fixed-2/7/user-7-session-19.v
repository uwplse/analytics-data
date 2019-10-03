Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.AltMatchDefs.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjmi_scope.
Lemma match_ty_i_pair : forall v1 v2 t1 t2 : ty, forall k : nat, |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k Hm1 Hm2).
(destruct k; split; assumption).
Qed.
Lemma match_ty_i_union_1 : forall v t1 t2 : ty, forall k : nat, |-[ k] v <$ t1 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; left; assumption).
Qed.
Lemma match_ty_i_union_2 : forall v t1 t2 : ty, forall k : nat, |-[ k] v <$ t2 -> |-[ k] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; right; assumption).
Qed.
Lemma match_ty_i_cname__inv : forall (v : ty) (c : cname), forall k : nat, |-[ k] v <$ TCName c -> v = TCName c.
Proof.
(intros v; induction v; try (solve [ intros c k Hm; destruct k; simpl in Hm; contradiction ])).
(intros c0 k Hm).
(destruct k; simpl in Hm; subst; reflexivity).
Qed.
Lemma match_ty_i_pair__inv :
  forall v t1 t2 : ty, forall k : nat, |-[ k] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k] v1 <$ t1 /\ |-[ k] v2 <$ t2.
Proof.
(intros v; induction v; try (solve [ intros t1 t2 k Hm; destruct k; simpl in Hm; contradiction ])).
(intros t1 t2 k Hm).
exists v1,v2.
(split; try reflexivity).
(destruct k; simpl in Hm; assumption).
Qed.
Lemma match_ty_i_union__inv : forall v t1 t2 : ty, forall k : nat, |-[ k] v <$ TUnion t1 t2 -> |-[ k] v <$ t1 \/ |-[ k] v <$ t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; assumption).
Qed.
Lemma match_ty_i_ref__inv :
  forall v t : ty,
  forall k : nat, |-[ S k] v <$ TRef t -> exists t' : ty, v = TRef t' /\ (forall v' : ty, value_type v' -> |-[ k] v' <$ t' <-> |-[ k] v' <$ t).
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; simpl in Hm; contradiction ])).
clear IHv.
(intros t k).
(intros Hm).
(pose proof Hm as Href).
(simpl in Href).
exists v.
split.
reflexivity.
(intros v' Hv').
specialize (Href v' Hv').
(destruct Href; split; assumption).
Qed.
Lemma match_ty_i_t_le_k__v_ke_t : forall (k : nat) (t : ty), | t | <= k -> forall v : ty, |-[ k] v <$ t -> | v | <= | t |.
Proof.
(induction k; induction t; intros Htk v Hm;
  try
   match goal with
   | Hm:|-[ ?k'] ?v <$ TCName _ |- _ => apply match_ty_i_cname__inv in Hm; subst; constructor
   | H:|-[ ?k'] ?v <$ TPair _ _
     |- _ =>
         destruct (max_inv_depth_le__components_le _ _ _ Htk) as [Htk1 Htk2]; apply match_ty_i_pair__inv in Hm;
          destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; apply Nat.max_le_compat; auto
   | H:|-[ ?k'] ?v <$ TUnion _ _
     |- _ =>
         destruct (max_inv_depth_le__components_le _ _ _ Htk) as [Htk1 Htk2]; apply match_ty_i_union__inv in Hm; destruct Hm as [Hm1| Hm2];
          [ apply Nat.le_trans with (| t1 |) | apply Nat.le_trans with (| t2 |) ]; auto; apply Max.le_max_l || apply Max.le_max_r
   end).
-
(destruct v; try contradiction).
(inversion Htk).
-
clear IHt.
(simpl in Htk).
(apply le_S_n in Htk).
(apply match_ty_i_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
Abort.
Lemma match_ty_i_eq__inv_depth_eq : forall t t' : ty, (forall (k : nat) (v : ty), |-[ k] v <$ t <-> |-[ k] v <$ t') -> | t | = | t' |.
Proof.
(induction t; induction t'; intros H).
reflexivity.
15: {
idtac.
clear IHt'.
(simpl).
(apply f_equal).
(apply IHt).
(intros k v).
(assert (Hmt : |-[ S k] TRef t <$ TRef t) by (simpl; tauto)).
specialize (H (S k) (TRef t)).
(destruct H as [H _]).
specialize (H Hmt).
(apply match_ty_i_ref__inv in H).
(destruct H as [tx [Heq Href]]).
(inversion Heq; subst).
auto.
(* Auto-generated comment: Failed. *)

