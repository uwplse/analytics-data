Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0280a.BaseDefs.
Require Import BetaJulia.Sub0280a.BaseProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjm.
Lemma match_ty_cname : forall (c : cname) (k w : nat), |-[ k, w] TCName c <$ TCName c.
Proof.
(intros c k w).
(destruct k, w; reflexivity).
Qed.
Lemma match_ty_pair : forall (v1 v2 t1 t2 : ty) (k w : nat), |-[ k, w] v1 <$ t1 -> |-[ k, w] v2 <$ t2 -> |-[ k, w] TPair v1 v2 <$ TPair t1 t2.
Proof.
(intros v1 v2 t1 t2 k w Hm1 Hm2).
(destruct k, w; split; assumption).
Qed.
Lemma match_ty_union_1 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t1 -> |-[ k, w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k w Hm).
(destruct k, w, v; left; assumption).
Qed.
Lemma match_ty_union_2 : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ t2 -> |-[ k, w] v <$ TUnion t1 t2.
Proof.
(intros v t1 t2 k w Hm).
(destruct k, w, v; right; assumption).
Qed.
Lemma match_ty_exist : forall (v : ty) (X : id) (t : ty) (k w : nat), (exists tx : ty, |-[ k, w] v <$ [X := tx] t) -> |-[ k, S w] v <$ TExist X t.
Proof.
(intros v X t k w Hex).
(destruct k, v; assumption).
Qed.
Lemma match_ty_var : forall (X : id) (k w : nat), |-[ k, w] TEV X <$ TVar X.
Proof.
(intros X k w).
(destruct k, w; reflexivity).
Qed.
Lemma match_ty_ev : forall (X : id) (k w : nat), |-[ k, w] TEV X <$ TEV X.
Proof.
(intros X k w).
(destruct k, w; reflexivity).
Qed.
Lemma match_ty_cname__inv : forall (v : ty) (c : cname) (k w : nat), |-[ k, w] v <$ TCName c -> v = TCName c.
Proof.
(intros v c k w Hm).
(destruct k, w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Lemma match_ty_pair__inv :
  forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k, w] v1 <$ t1 /\ |-[ k, w] v2 <$ t2.
Proof.
(intros v t1 t2 k w Hm).
(destruct k, w, v; simpl in Hm; contradiction || (exists v1,v2; split; [ reflexivity | tauto ])).
Qed.
Lemma match_ty_union__inv : forall (v t1 t2 : ty) (k w : nat), |-[ k, w] v <$ TUnion t1 t2 -> |-[ k, w] v <$ t1 \/ |-[ k, w] v <$ t2.
Proof.
(intros v t1 t2 k w Hm).
(destruct k, w, v; assumption).
Qed.
Lemma match_ty_ref__weak_inv : forall (v t : ty) (k w : nat), |-[ k, w] v <$ TRef t -> exists t' : ty, v = TRef t'.
Proof.
(intros v t k w Hm).
(destruct k, w, v; simpl in Hm; contradiction || (exists v; reflexivity)).
Qed.
Lemma match_ty_ref__inv : forall (v t : ty) (k w : nat), |-[ S k, w] v <$ TRef t -> exists t' : ty, v = TRef t' /\ ||-[ k][t']= [t].
Proof.
(intros v t k w Hm).
(destruct v; try (solve [ destruct k, w; simpl in Hm; contradiction ])).
exists v.
split.
reflexivity.
(destruct w; auto).
Qed.
Lemma match_ty_exist__0_inv : forall (v : ty) (X : id) (t : ty) (k : nat), |-[ k, 0] v <$ TExist X t -> False.
Proof.
(intros v X t k Hm).
(destruct k, v; simpl in Hm; contradiction).
Qed.
Lemma match_ty_exist__inv :
  forall (v : ty) (X : id) (t : ty) (k w : nat), |-[ k, S w] v <$ TExist X t -> exists tx : ty, |-[ k, w] v <$ [X := tx] t.
Proof.
(intros v X t k w Hm).
(destruct k, v; assumption).
Qed.
Lemma match_ty_var__inv : forall (v : ty) (X : id) (k w : nat), |-[ k, w] v <$ TVar X -> v = TEV X.
Proof.
(intros v X k w Hm).
(destruct k, w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Lemma match_ty_ev__inv : forall (v : ty) (X : id) (k w : nat), |-[ k, w] v <$ TEV X -> v = TEV X.
Proof.
(intros v X k w Hm).
(destruct k, w, v; simpl in Hm; subst; reflexivity || contradiction).
Qed.
Theorem match_ty__value_type_l : forall (k w : nat) (v t : ty), |-[ k, w] v <$ t -> value_type v.
Proof.
(intros k w; generalize dependent k; induction w, k; intros v t; generalize dependent v; induction t; intros v Hm;
  try (solve
   [ apply match_ty_cname__inv in Hm; subst; constructor
   | apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; constructor; [ eapply IHt1 | eapply IHt2 ]; eauto
   | apply match_ty_union__inv in Hm; destruct Hm as [Hm1| Hm2]; [ eapply IHt1 | eapply IHt2 ]; eauto
   | apply match_ty_ref__weak_inv in Hm; destruct Hm as [t' Heq]; subst; constructor
   | apply match_ty_var__inv in Hm; subst; constructor
   | apply match_ty_ev__inv in Hm; subst; constructor
   | apply match_ty_exist__0_inv in Hm; contradiction
   | apply match_ty_exist__inv in Hm; destruct Hm as [tx Hmx]; eapply IHw; eassumption ])).
Qed.
Lemma match_ty_value_type__reflexive : forall v : ty, value_type v -> forall k w : nat, |-[ k, w] v <$ v.
Proof.
(intros v Hv; induction Hv; intros k w).
-
(destruct k, w; reflexivity).
-
(apply match_ty_pair; auto).
-
(destruct k, w; try (solve [ simpl; tauto | simpl; split; intros w1; exists w1; tauto ])).
-
(destruct k, w; reflexivity).
Qed.
Lemma match_ty__ge_w : forall (w : nat) (t : ty) (k : nat) (v : ty), |-[ k, w] v <$ t -> forall w' : nat, w <= w' -> |-[ k, w'] v <$ t.
Proof.
(induction w; induction t; intros k v Hm w' Hle;
  try
   match goal with
   | |- |-[ _, _] _ <$ TCName _ => apply match_ty_cname__inv in Hm; subst; apply match_ty_cname
   | |- |-[ _, _] _ <$ TPair _ _ =>
         apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; apply match_ty_pair; [ eapply IHt1 | eapply IHt2 ]; eauto
   | |- |-[ _, _] _ <$ TUnion _ _ =>
         apply match_ty_union__inv in Hm; destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; eauto
   | |- |-[ _, _] _ <$ TVar _ => apply match_ty_var__inv in Hm; subst; apply match_ty_var
   | |- |-[ _, _] _ <$ TEV _ => apply match_ty_ev__inv in Hm; subst; apply match_ty_ev
   end).
-
(destruct k).
+
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(destruct w'; constructor).
+
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(destruct w'; assumption).
-
(apply match_ty_exist__0_inv in Hm; contradiction).
-
(destruct k).
+
(apply match_ty_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
(destruct w'; constructor).
+
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(destruct w'; assumption).
-
(apply match_ty_exist__inv in Hm).
(destruct Hm as [tx Hmx]).
(destruct w').
(inversion Hle).
(apply match_ty_exist).
exists tx.
(apply IHw).
assumption.
(apply le_S_n; assumption).
Qed.
Lemma match_ty__exists_w_v : forall (t : ty) (k : nat), exists (w : nat) (v : ty), |-[ k, w] v <$ t.
Proof.
(induction t; intros k).
-
exists 0,(TCName c).
(apply match_ty_value_type__reflexive; constructor).
-
(destruct (IHt1 k) as [w1 [v1 Hm1]]).
(destruct (IHt2 k) as [w2 [v2 Hm2]]).
exists (Nat.max w1 w2),(TPair v1 v2).
(apply match_ty_pair; eapply match_ty__ge_w; try eassumption).
(apply Nat.le_max_l).
(apply Nat.le_max_r).
-
(destruct (IHt1 k) as [w [v Hm]]).
exists w,v.
(apply match_ty_union_1; assumption).
-
exists 0,(TRef t).
(apply match_ty_value_type__reflexive; constructor).
-
(destruct (IHt k) as [w [v Hm]]).
exists (S w),v.
(apply match_ty_exist).
exists (TVar i).
(rewrite subs_id).
-
(destruct (IHt1 k) as [w1 [v1 Hm1]]).
(destruct (IHt2 k) as [w2 [v2 Hm2]]).
exists (Nat.max w1 w2),(TPair v1 v2).
(apply match_ty_pair; eapply match_ty__ge_w; try eassumption).
(apply Nat.le_max_l).
(apply Nat.le_max_r).
-
(destruct (IHt1 k) as [w [v Hm]]).
exists w,v.
(apply match_ty_union_1; assumption).
-
exists 0,(TRef t).
(apply match_ty_value_type__reflexive; constructor).
-
(destruct (IHt k) as [w [v Hm]]).
exists (S w),v.
(apply match_ty_exist).
exists (TVar i).
(rewrite subs_id).
assumption.
-
exists 0,(TEV i).
(apply match_ty_var).
-
exists 0,(TEV i).
(apply match_ty_ev).
Qed.
