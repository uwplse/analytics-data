Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
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
Unset Silent.
Lemma match_ty_i_pair : forall v1 v2 t1 t2 : ty, forall k : nat, |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ TPair t1 t2.
Set Silent.
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
Lemma match_ty_i__reflexive : forall v : ty, value_type v -> forall k : nat, |-[ k] v <$ v.
Proof.
(intros v Hv; induction Hv; intros k).
-
(destruct k; reflexivity).
-
(apply match_ty_i_pair; auto).
-
(destruct k).
Unset Silent.
constructor.
Set Silent.
(simpl).
tauto.
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
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Lemma match_ty_i_ref__weak_inv : forall v t : ty, forall k : nat, |-[ k] v <$ TRef t -> exists t' : ty, v = TRef t'.
Unset Silent.
Proof.
Set Printing Width 148.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; simpl in Hm; contradiction ])).
clear IHv.
(intros t k).
(intros Hm).
exists v.
reflexivity.
Qed.
Set Silent.
Lemma match_ty_i_ref__inv :
  forall v t : ty, forall k : nat, |-[ S k] v <$ TRef t -> exists t' : ty, v = TRef t' /\ (forall v' : ty, |-[ k] v' <$ t' <-> |-[ k] v' <$ t).
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
(intros v').
specialize (Href v').
(destruct Href; split; assumption).
Qed.
Lemma match_ty_i__value_type : forall (t : ty) (k : nat) (v : ty), |-[ k] v <$ t -> value_type v.
Proof.
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
Unset Silent.
Show.
Set Printing Width 148.
(apply match_ty_i_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
constructor.
Set Printing Width 148.
Set Printing Width 148.
Set Silent.
Lemma match_ty_i__transitive_on_value_type :
  forall v1 v2 t3 : ty, value_type v2 -> forall k : nat, |-[ k] v1 <$ v2 -> |-[ k] v2 <$ t3 -> |-[ k] v1 <$ t3.
Proof.
(intros v1 v2 t3 Hv2).
generalize dependent t3.
generalize dependent v1.
Unset Silent.
Show.
(induction Hv2).
Set Silent.
-
Unset Silent.
(intros v1 t3 k Hm1 Hm2).
Set Silent.
(apply match_ty_i_cname__inv in Hm1; subst).
Unset Silent.
assumption.
Set Silent.
-
Unset Silent.
Show.
(intros v0 t3 k Hm1 Hm2).
Set Silent.
(apply match_ty_i_pair__inv in Hm1).
(destruct Hm1 as [pv11 [pv12 [Heq [Hm11 Hmpv12]]]]; subst).
Unset Silent.
(induction t3; try (solve [ destruct k; simpl in Hm2; contradiction ])).
Set Silent.
+
(apply match_ty_i_pair__inv in Hm2).
(destruct Hm2 as [pv21 [pv22 [Heq [Hm21 Hm22]]]]).
(inversion Heq; subst).
Unset Silent.
auto using match_ty_i_pair.
Set Silent.
+
(apply match_ty_i_union__inv in Hm2).
Unset Silent.
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
Set Printing Width 148.
(intros v1 t3 k Hm1 Hm2).
Show.
(induction t3; try (solve [ destruct k; simpl in Hm2; contradiction ])).
Show.
Set Silent.
+
Unset Silent.
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
+
clear IHt3.
Set Silent.
Set Printing Width 148.
(destruct v1; contradiction || constructor).
Show.
Show.
Set Printing Width 148.
Set Printing Width 148.
(apply match_ty_i_ref__inv in Hm1).
Show.
(destruct Hm1 as [tx [Heqx Hrefx]]; inversion Heqx; subst).
Show.
(apply match_ty_i_ref__inv in Hm2).
(destruct Hm2 as [ty [Heqy Hrefy]]; inversion Heqy; subst).
Show.
(simpl).
Show.
Set Printing Width 148.
Show.
Set Printing Width 148.
Set Printing Width 148.
Set Printing Width 148.
(intros v; split; intros Hm; specialize (Hrefx v); specialize (Hrefy v); tauto).
Show.
Qed.
Set Silent.
Lemma value_sem_sub_k_union__value_sem_sub_k_component :
  forall k : nat, forall v : ty, value_type v -> forall ta tb : ty, ||-[ k][v]<= [TUnion ta tb] -> ||-[ k][v]<= [ta] \/ ||-[ k][v]<= [tb].
Proof.
(induction k; intros v Hv; induction Hv; intros ta tb Hsem).
6: {
idtac.
(unfold sem_sub_k_i in Hsem).
(assert (Hvref : value_type (TRef t)) by constructor).
(assert (Hmref : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; assumption)).
Show.
Set Printing Width 148.
(apply match_ty_i_union__inv in Hmu).
Show.
Set Printing Width 148.
Set Printing Width 148.
(destruct Hmu as [Hmu1| Hmu2]; [ left | right ]; intros v Hv Hm; apply match_ty_i_ref__inv in Hm; destruct Hm as [t' [Heq Href]]; subst).
Show.
Set Printing Width 148.
Set Printing Width 148.
(assert (Hmt't : |-[ S k] TRef t' <$ TRef t) by (intros v'; split; intros Hm'; specialize (Href v'); tauto)).
Show.
Set Printing Width 148.
Show.
Set Printing Width 148.
(apply match_ty_i__transitive_on_value_type with (TRef t); try assumption).
Show.
