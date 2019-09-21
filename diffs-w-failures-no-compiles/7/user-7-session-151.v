Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0281a.BaseDefs.
Require Import BetaJulia.Sub0281a.BaseProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma match_ty_cname : forall (c : cname) (w : nat), |-[ w] TCName c <$ TCName c.
Proof.
(intros c w).
(destruct w; reflexivity).
Qed.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (w : nat), |-[ w] v1 <$ t1 -> |-[ w] v2 <$ t2 -> |-[ w] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 w Hm1 Hm2).
(destruct w; split; assumption).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ t1 -> |-[ w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 w Hm).
Unset Silent.
(destruct w, v; left; assumption).
Qed.
Set Silent.
Lemma match_ty_union_2 : forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ t2 -> |-[ w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 w Hm).
(destruct w, v; right; assumption).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_exist : forall (v : ty) (X : id) (t : ty) (w : nat), (exists tx : ty, |-[ w] v <$ [X := tx] t) -> |-[ S w] v <$ TExist X t.
Unset Silent.
Proof.
Set Silent.
(intros v X t w Hex).
Unset Silent.
(destruct v; assumption).
Qed.
Set Silent.
Lemma match_ty_var : forall (X : id) (w : nat), |-[ w] TEV X <$ TVar X.
Proof.
(intros X w).
(destruct w; reflexivity).
Qed.
Lemma match_ty_ev : forall (X : id) (w : nat), |-[ w] TEV X <$ TEV X.
Proof.
(intros X w).
(destruct w; reflexivity).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (w : nat), |-[ w] v <$ TCName c -> v = TCName c.
Proof.
(intros v c w Hm).
(destruct w, v; simpl in Hm; subst; reflexivity || contradiction).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_pair__inv :
  forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ w] v1 <$ t1 /\ |-[ w] v2 <$ t2.
Proof.
(intros v t1 t2 w Hm).
(destruct w, v; simpl in Hm; contradiction || (exists v1,v2; split; [ reflexivity | tauto ])).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_pair_pair__inv : forall (v1 v2 t1 t2 : ty) (w : nat), |-[ w] TPair v1 v2 <$ TPair t1 t2 -> |-[ w] v1 <$ t1 /\ |-[ w] v2 <$ t2.
Proof.
(intros v1 v2 t1 t2 w Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1' [v2' [Heq [Hm1 Hm2]]]]).
(inversion Heq; subst).
tauto.
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_union__inv : forall (v t1 t2 : ty) (w : nat), |-[ w] v <$ TUnion t1 t2 -> |-[ w] v <$ t1 \/ |-[ w] v <$ t2.
Proof.
(intros v t1 t2 w Hm).
Unset Silent.
(destruct w, v; assumption).
Qed.
Set Silent.
Lemma match_ty_exist__0_inv : forall (v : ty) (X : id) (t : ty), |-[ 0] v <$ TExist X t -> False.
Proof.
(intros v X t Hm).
(destruct v; simpl in Hm; contradiction).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_exist__inv : forall (v : ty) (X : id) (t : ty) (w : nat), |-[ S w] v <$ TExist X t -> exists tx : ty, |-[ w] v <$ [X := tx] t.
Proof.
(intros v X t w Hm).
(destruct v; assumption).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_var__inv : forall (v : ty) (X : id) (w : nat), |-[ w] v <$ TVar X -> v = TEV X.
Proof.
(intros v X w Hm).
Unset Silent.
(destruct w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Set Silent.
Lemma match_ty_ev__inv : forall (v : ty) (X : id) (w : nat), |-[ w] v <$ TEV X -> v = TEV X.
Proof.
(intros v X w Hm).
(destruct w, v; simpl in Hm; subst; reflexivity || contradiction).
Unset Silent.
Qed.
Set Silent.
Theorem match_ty__value_type_l : forall (w : nat) (v t : ty), |-[ w] v <$ t -> value_type v.
Proof.
(intros w; generalize dependent k; induction w; intros v t; generalize dependent v; induction t; intros v Hm;
  try (solve
   [ apply match_ty_cname__inv in Hm; subst; constructor
   | apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; constructor; [ eapply IHt1 | eapply IHt2 ]; eauto
   | apply match_ty_union__inv in Hm; destruct Hm as [Hm1| Hm2]; [ eapply IHt1 | eapply IHt2 ]; eauto
   | apply match_ty_ref__weak_inv in Hm; destruct Hm as [t' Heq]; subst; constructor
   | apply match_ty_var__inv in Hm; subst; constructor
   | apply match_ty_ev__inv in Hm; subst; constructor
   | apply match_ty_exist__0_inv in Hm; contradiction
   | apply match_ty_exist__inv in Hm; destruct Hm as [tx Hmx]; eapply IHw; eassumption ])).
