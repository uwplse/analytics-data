Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.AltMatchDefs.
Require Import BetaJulia.Sub0250a.DeclSubProps.
Require Import BetaJulia.BasicTactics.
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
Lemma match_ty_i__reflexive : forall v : ty, value_type v -> forall k : nat, |-[ k] v <$ v.
Proof.
(intros v Hv; induction Hv; intros k).
-
(destruct k; reflexivity).
-
(apply match_ty_i_pair; auto).
-
(destruct k).
constructor.
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
Lemma match_ty_i_ref__weak_inv : forall v t : ty, forall k : nat, |-[ k] v <$ TRef t -> exists t' : ty, v = TRef t'.
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; simpl in Hm; contradiction ])).
clear IHv.
(intros t k).
(intros Hm).
exists v.
reflexivity.
Qed.
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
(apply match_ty_i_ref__weak_inv in Hm).
(destruct Hm as [t' Heq]; subst).
constructor.
Qed.
Lemma match_ty_i__transitive_on_value_type :
  forall v1 v2 t3 : ty, value_type v2 -> forall k : nat, |-[ k] v1 <$ v2 -> |-[ k] v2 <$ t3 -> |-[ k] v1 <$ t3.
Proof.
(intros v1 v2 t3 Hv2).
generalize dependent t3.
generalize dependent v1.
(induction Hv2).
-
(intros v1 t3 k Hm1 Hm2).
(apply match_ty_i_cname__inv in Hm1; subst).
assumption.
-
(intros v0 t3 k Hm1 Hm2).
(apply match_ty_i_pair__inv in Hm1).
(destruct Hm1 as [pv11 [pv12 [Heq [Hm11 Hmpv12]]]]; subst).
(induction t3; try (solve [ destruct k; simpl in Hm2; contradiction ])).
+
(apply match_ty_i_pair__inv in Hm2).
(destruct Hm2 as [pv21 [pv22 [Heq [Hm21 Hm22]]]]).
(inversion Heq; subst).
auto using match_ty_i_pair.
+
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
-
(intros v1 t3 k Hm1 Hm2).
(induction t3; try (solve [ destruct k; simpl in Hm2; contradiction ])).
+
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
+
clear IHt3.
(destruct k).
(destruct v1; contradiction || constructor).
(apply match_ty_i_ref__inv in Hm1).
(destruct Hm1 as [tx [Heqx Hrefx]]; inversion Heqx; subst).
(apply match_ty_i_ref__inv in Hm2).
(destruct Hm2 as [ty [Heqy Hrefy]]; inversion Heqy; subst).
(simpl).
(intros v; split; intros Hm; specialize (Hrefx v); specialize (Hrefy v); tauto).
Qed.
Lemma match_ty_i_exists : forall (t : ty) (k : nat), exists v : ty, |-[ k] v <$ t.
Proof.
(induction t; intros k).
-
(exists (TCName c); destruct k; reflexivity).
-
(destruct (IHt1 k) as [v1 Hm1]; destruct (IHt2 k) as [v2 Hm2]).
(exists (TPair v1 v2); apply match_ty_i_pair; assumption).
-
(destruct (IHt1 k) as [v1 Hm1]).
(exists v1; apply match_ty_i_union_1; assumption).
-
exists (TRef t).
(apply match_ty_i__reflexive).
constructor.
Qed.
Lemma sem_sub_k_union_l__inv : forall (k : nat) (t1 t2 t' : ty), ||-[ k][TUnion t1 t2]<= [t'] -> ||-[ k][t1]<= [t'] /\ ||-[ k][t2]<= [t'].
Proof.
(intros k t1 t2 t' Hsem).
(unfold sem_sub_k_i in Hsem).
(split; intros v Hm; assert (Hmu : |-[ k] v <$ TUnion t1 t2) by (apply match_ty_i_union_1; assumption) || (apply match_ty_i_union_2; assumption);
  apply Hsem; assumption).
Qed.
Lemma value_sem_sub_k_i_union__inv :
  forall v : ty, value_type v -> forall (k : nat) (ta tb : ty), ||-[ k][v]<= [TUnion ta tb] -> ||-[ k][v]<= [ta] \/ ||-[ k][v]<= [tb].
Proof.
(intros v Hv k ta tb Hsem; unfold sem_sub_k_i in Hsem).
(assert (Hm : |-[ k] v <$ v) by (apply match_ty_i__reflexive; assumption)).
specialize (Hsem _ Hm).
(apply match_ty_i_union__inv in Hsem).
(destruct Hsem; [ left | right ]; unfold sem_sub_k_i; intros v' Hm'; apply match_ty_i__transitive_on_value_type with v; assumption).
Qed.
Lemma sem_sub_k_i_pair__inv :
  forall (t1 t2 t1' t2' : ty) (k : nat), ||-[ k][TPair t1 t2]<= [TPair t1' t2'] -> ||-[ k][t1]<= [t1'] /\ ||-[ k][t2]<= [t2'].
Proof.
(intros t1 t2 t1' t2' k Hsem).
(unfold sem_sub_k_i in Hsem).
(split; intros v Hm; [ destruct (match_ty_i_exists t2 k) as [v' Hm'] | destruct (match_ty_i_exists t1 k) as [v' Hm'] ];
  [ assert (Hmp : |-[ k] TPair v v' <$ TPair t1 t2) by (apply match_ty_i_pair; assumption)
  | assert (Hmp : |-[ k] TPair v' v <$ TPair t1 t2) by (apply match_ty_i_pair; assumption) ]; specialize (Hsem _ Hmp);
  apply match_ty_i_pair__inv in Hsem; destruct Hsem as [v1 [v2 [Heq [Hm1 Hm2]]]]; inversion Heq; subst; assumption).
Qed.
Ltac
 solve__value_sem_sub_i_union__inv_depth_le Hv Hsem t'1 t'2 :=
  pose proof (value_sem_sub_k_i_union__inv _ Hv _ _ _ Hsem) as Hsemu; destruct Hsemu as [Hsemu| Hsemu];
   [ apply Nat.le_trans with (| t'1 |) | apply Nat.le_trans with (| t'2 |) ]; tauto || apply Max.le_max_l || apply Max.le_max_r.
Lemma sem_sub_k_i_nf__inv_depth_le_1 : forall (k : nat) (t t' : ty), InNF( t) -> | t | <= k -> ||-[ k][t]<= [t'] -> | t | <= | t' |.
Proof.
(induction k; induction t; induction t'; intros Hnft Hdept Hsem; try (solve [ simpl; constructor ]);
  try (solve
   [ match goal with
     | Hsem:||-[ ?k][?t]<= [?t']
       |- | ?t | <= | ?t' | =>
           assert (Hv : value_type t) by constructor; assert (Hm : |-[ k] t <$ t) by (apply match_ty_i__reflexive; assumption); specialize
            (Hsem _ Hm); contradiction
     | Hsem:||-[ ?k][TPair ?t1 ?t2]<= [TUnion ?t'1 ?t'2]
       |- _ =>
           assert (Hv : value_type (TPair t1 t2)) by (apply in_nf_pair__value_type; assumption);
            solve__value_sem_sub_i_union__inv_depth_le Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][?t]<= [TUnion ?t'1 ?t'2]
       |- | ?t | <= _ => assert (Hv : value_type t) by constructor; solve__value_sem_sub_i_union__inv_depth_le Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][TPair ?t1 ?t2]<= [?t']
       |- _ <= | ?t' | =>
           assert (Hvp : value_type (TPair t1 t2)) by (apply in_nf_pair__value_type; assumption);
            assert (Hmp : |-[ k] TPair t1 t2 <$ TPair t1 t2) by (apply match_ty_i__reflexive; assumption); specialize (Hsem _ Hmp); contradiction
     | Hsem:||-[ ?k][TPair _ _]<= [TPair _ _]
       |- _ =>
           destruct (in_nf_pair__inv _ _ Hnft) as [Hnft1 Hnft2]; destruct (max_inv_depth_le__components_le _ _ _ Hdept) as [Hdept1 Hdept2];
            destruct (sem_sub_k_i_pair__inv _ _ _ _ _ Hsem) as [Hsem1 Hsem2]; simpl; apply Nat.max_le_compat; auto
     | Hsem:||-[ ?k][TUnion _ _]<= [_], Hnft:InNF( TUnion _ _), Hdept:| TUnion _ _ | <= _
       |- _ =>
           destruct (max_inv_depth_le__components_le _ _ _ Hdept) as [Hdept1 Hdept2];
            destruct (sem_sub_k_union_l__inv _ _ _ _ Hsem) as [HSem1 Hsem2]; destruct (in_nf_union__inv _ _ Hnft) as [Hnft1 Hnft2];
            rewrite inv_depth_union; apply Nat.max_lub; auto
     end ])).
-
(inversion Hdept; subst).
-
(simpl).
(apply le_n_S).
(inversion Hnft; subst).
(inversion H; subst).
(simpl in Hdept).
(apply le_S_n in Hdept).
(apply IHk; try assumption).
(assert (Hv : value_type (TRef t)) by constructor).
(assert (Hm : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; constructor)).
specialize (Hsem _ Hm).
(simpl in Hsem).
(intros v').
specialize (Hsem v').
tauto.
Qed.
Ltac
 solve__value_sem_sub_i_union__inv_depth_le_2 Hdept' Hv Hsem t'1 t'2 :=
  destruct (max_inv_depth_le__components_le _ _ _ Hdept') as [Hdept'1 Hdept'2]; pose proof (value_sem_sub_k_i_union__inv _ Hv _ _ _ Hsem) as Hsemu;
   destruct Hsemu as [Hsemu| Hsemu]; [ apply Nat.le_trans with (| t'1 |) | apply Nat.le_trans with (| t'2 |) ];
   tauto || apply Max.le_max_l || apply Max.le_max_r.
Lemma sem_sub_k_i_nf__inv_depth_le_2 : forall (k : nat) (t t' : ty), InNF( t) -> | t' | <= k -> ||-[ k][t]<= [t'] -> | t | <= | t' |.
Proof.
(induction k; induction t; induction t'; intros Hnft Hdept' Hsem; try (solve [ simpl; constructor ]);
  try (solve
   [ match goal with
     | Hsem:||-[ ?k][?t]<= [?t']
       |- | ?t | <= | ?t' | =>
           assert (Hv : value_type t) by constructor; assert (Hm : |-[ k] t <$ t) by (apply match_ty_i__reflexive; assumption); specialize
            (Hsem _ Hm); contradiction
     | Hsem:||-[ ?k][TPair ?t1 ?t2]<= [TUnion ?t'1 ?t'2]
       |- _ =>
           assert (Hv : value_type (TPair t1 t2)) by (apply in_nf_pair__value_type; assumption);
            solve__value_sem_sub_i_union__inv_depth_le_2 Hdept' Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][?t]<= [TUnion ?t'1 ?t'2]
       |- | ?t | <= _ => assert (Hv : value_type t) by constructor; solve__value_sem_sub_i_union__inv_depth_le_2 Hdept' Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][TPair ?t1 ?t2]<= [?t']
       |- _ <= | ?t' | =>
           assert (Hvp : value_type (TPair t1 t2)) by (apply in_nf_pair__value_type; assumption);
            assert (Hmp : |-[ k] TPair t1 t2 <$ TPair t1 t2) by (apply match_ty_i__reflexive; assumption); specialize (Hsem _ Hmp); contradiction
     | Hsem:||-[ ?k][TPair _ _]<= [TPair _ _]
       |- _ =>
           destruct (in_nf_pair__inv _ _ Hnft) as [Hnft1 Hnft2]; destruct (max_inv_depth_le__components_le _ _ _ Hdept') as [Hdept'1 Hdept'2];
            destruct (sem_sub_k_i_pair__inv _ _ _ _ _ Hsem) as [Hsem1 Hsem2]; simpl; apply Nat.max_le_compat; auto
     | Hsem:||-[ ?k][TUnion _ _]<= [_], Hnft:InNF( TUnion _ _)
       |- _ =>
           destruct (sem_sub_k_union_l__inv _ _ _ _ Hsem) as [HSem1 Hsem2]; destruct (in_nf_union__inv _ _ Hnft) as [Hnft1 Hnft2];
            rewrite inv_depth_union; apply Nat.max_lub; auto
     end ])).
-
(inversion Hdept'; subst).
-
(simpl).
(apply le_n_S).
(inversion Hnft; subst).
(inversion H; subst).
(simpl in Hdept').
(apply le_S_n in Hdept').
(apply IHk; try assumption).
(assert (Hv : value_type (TRef t)) by constructor).
(assert (Hm : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; constructor)).
specialize (Hsem _ Hm).
(simpl in Hsem).
(intros v').
specialize (Hsem v').
tauto.
Qed.
Lemma match_ty_i_nf : forall (k : nat) (t : ty), ||-[ k][t]= [MkNF( t)].
Proof.
(induction k; induction t; intros v; split; intros Hm; try (solve [ simpl; assumption ])).
Admitted.
Lemma sem_sub_k__i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t3] -> ||-[ k][t1]<= [t3].
Proof.
auto with DBBetaJulia.
Qed.
Lemma sem_eq_k_i__sem_sub_k_i : forall (k : nat) (t t' : ty), ||-[ k][t]= [t'] -> ||-[ k][t]<= [t'] /\ ||-[ k][t']<= [t].
Proof.
(intros k t t' H).
(split; intros v Hm; specialize (H v); tauto).
Qed.
Lemma sem_sub_k_i__inv_depth_le_1 : forall (k : nat) (t t' : ty), | t | <= k -> ||-[ k][t]<= [t'] -> | t | <= | t' |.
Proof.
(intros k t t' Hdept Hsem).
(rewrite <- inv_depth_mk_nf).
(apply sem_sub_k_i_nf__inv_depth_le_1 with k).
(apply mk_nf__in_nf).
(rewrite inv_depth_mk_nf; assumption).
(apply sem_sub_k__i__trans with t; try assumption).
(pose proof (match_ty_i_nf k t) as H).
(intros v Hm; specialize (H v); tauto).
Qed.
Lemma sem_sub_k_i__inv_depth_le_2 : forall (k : nat) (t t' : ty), | t' | <= k -> ||-[ k][t]<= [t'] -> | t | <= | t' |.
Proof.
(intros k t t' Hdept' Hsem).
(rewrite <- inv_depth_mk_nf).
(apply sem_sub_k_i_nf__inv_depth_le_2 with k).
(apply mk_nf__in_nf).
assumption.
(apply sem_sub_k__i__trans with t; try assumption).
(pose proof (match_ty_i_nf k t) as H).
(intros v Hm; specialize (H v); tauto).
Qed.
Lemma sem_eq_k_i__inv_depth_eq_1 : forall (k : nat) (t t' : ty), | t | <= k -> ||-[ k][t]= [t'] -> | t | = | t' |.
Proof.
(intros k t t' Hdept H).
(destruct (sem_eq_k_i__sem_sub_k_i _ _ _ H) as [H1 H2]).
(pose proof (sem_sub_k_i__inv_depth_le_1 _ _ _ Hdept H1)).
(pose proof (sem_sub_k_i__inv_depth_le_2 _ _ _ Hdept H2)).
(apply Nat.le_antisymm; assumption).
Qed.
Lemma sem_eq_k_i__inv_depth_eq_2 : forall (k : nat) (t t' : ty), | t' | <= k -> ||-[ k][t]= [t'] -> | t | = | t' |.
Proof.
(intros k t t' Hdept' H).
(destruct (sem_eq_k_i__sem_sub_k_i _ _ _ H) as [H1 H2]).
(pose proof (sem_sub_k_i__inv_depth_le_2 _ _ _ Hdept' H1)).
(pose proof (sem_sub_k_i__inv_depth_le_1 _ _ _ Hdept' H2)).
(apply Nat.le_antisymm; assumption).
Qed.
Lemma sem_sub_i_union_l__inv : forall t1 t2 t' : ty, ||- [TUnion t1 t2]<= [t'] -> ||- [t1]<= [t'] /\ ||- [t2]<= [t'].
Proof.
(intros t1 t2 t' Hsem).
(unfold sem_sub_i in Hsem).
(split; intros k; specialize (Hsem k); destruct (sem_sub_k_union_l__inv _ _ _ _ Hsem); assumption).
Qed.
Lemma sem_sub_i_ref__inv : forall t t' : ty, ||- [TRef t]<= [TRef t'] -> ||- [t]<= [t'] /\ ||- [t']<= [t].
Proof.
(intros t t' Hsem).
(split; intros k; specialize (Hsem (S k)); assert (Hvref : value_type (TRef t)) by constructor;
  assert (Hm : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; assumption); specialize (Hsem _ Hm); simpl in Hsem; 
  intros v' Hm'; specialize (Hsem v'); tauto).
Qed.
Open Scope btj_scope.
Lemma match_ty__inv_depth_0_stable : forall t : ty, inv_depth t = 0 -> forall k v, |-[ k] v <$ t <-> |-[ 0] v <$ t.
Proof.
(induction t; intros Heqdep k v).
-
(split; intros Hm; apply match_ty_i_cname__inv in Hm; subst).
reflexivity.
(destruct k; reflexivity).
-
(simpl in Heqdep).
(assert (Hledep : Nat.max (inv_depth t1) (inv_depth t2) <= 0)).
{
(rewrite Heqdep).
constructor.
}
(destruct (max_inv_depth_le__components_le _ _ _ Hledep) as [Hdep1 Hdep2]).
(inversion Hdep1).
(inversion Hdep2).
specialize (IHt1 H0 k).
specialize (IHt2 H1 k).
(split; intros Hm; apply match_ty_i_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hvq Hv2]]]]; subst).
+
(rewrite H0).
(apply match_ty_i_pair; [ apply IHt1 | apply IHt2 ]; assumption).
+
(rewrite H0 in *).
(apply match_ty_i_pair; [ apply IHt1 | apply IHt2 ]; assumption).
-
(simpl in Heqdep).
(assert (Hledep : Nat.max (inv_depth t1) (inv_depth t2) <= 0)).
{
(rewrite Heqdep).
constructor.
}
(destruct (max_inv_depth_le__components_le _ _ _ Hledep) as [Hdep1 Hdep2]).
(inversion Hdep1).
(inversion Hdep2).
specialize (IHt1 H0 k).
specialize (IHt2 H1 k).
(rewrite H0 in *).
(split; intros Hm; apply match_ty_i_union__inv in Hm; destruct Hm; (solve
  [ apply match_ty_i_union_1; apply IHt1; assumption | apply match_ty_i_union_2; apply IHt2; assumption ])).
-
(inversion Heqdep).
Qed.
Lemma match_ty_i__inv_depth_stable :
  forall (k k' : nat) (t : ty), inv_depth t <= k -> inv_depth t <= k' -> forall v : ty, |-[ k] v <$ t <-> |-[ k'] v <$ t.
Proof.
(induction k; induction k').
-
tauto.
-
(intros).
symmetry.
(apply match_ty__inv_depth_0_stable).
(inversion H).
reflexivity.
-
(intros).
(apply match_ty__inv_depth_0_stable).
(inversion H0).
reflexivity.
-
(induction t).
+
(intros; split; intros Hm; apply match_ty_i_cname__inv in Hm; subst; reflexivity).
+
(intros Hdepk Hdepk' v).
(simpl in Hdepk, Hdepk').
(destruct (max_inv_depth_le__components_le _ _ _ Hdepk) as [Ht1k Ht2k]).
(destruct (max_inv_depth_le__components_le _ _ _ Hdepk') as [Ht1k' Ht2k']).
specialize (IHt1 Ht1k Ht1k').
specialize (IHt2 Ht2k Ht2k').
(split; intros Hm; apply match_ty_i_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hv1 Hv2]]]]; subst; specialize (IHt1 v1); specialize (IHt2 v2);
  apply match_ty_i_pair; tauto).
+
(intros Hdepk Hdepk' v).
(simpl in Hdepk, Hdepk').
(destruct (max_inv_depth_le__components_le _ _ _ Hdepk) as [Ht1k Ht2k]).
(destruct (max_inv_depth_le__components_le _ _ _ Hdepk') as [Ht1k' Ht2k']).
specialize (IHt1 Ht1k Ht1k' v).
specialize (IHt2 Ht2k Ht2k' v).
(split; intros Hm; apply match_ty_i_union__inv in Hm; destruct Hm; (apply match_ty_i_union_1; tauto) || (apply match_ty_i_union_2; tauto)).
+
clear IHk' IHt.
(intros Htk Htk' v).
(simpl in Htk, Htk').
(apply le_S_n in Htk).
(apply le_S_n in Htk').
(split; intros Hm; apply match_ty_i_ref__inv in Hm; destruct Hm as [t' [Heq Href]]; subst; simpl; intros v; pose proof (Href v) as Hrefv).
*
(assert (Hdepeq : | t' | = | t |) by apply (sem_eq_k_i__inv_depth_eq_2 _ _ _ Htk Href)).
(pose proof Htk as Ht'k; pose proof Htk' as Ht'k'; rewrite <- Hdepeq in Ht'k, Ht'k').
(pose proof (IHk k' t Htk Htk' v) as Ht).
(pose proof (IHk k' t' Ht'k Ht'k' v) as Ht').
tauto.
*
(assert (Hdepeq : | t' | = | t |) by apply (sem_eq_k_i__inv_depth_eq_2 _ _ _ Htk' Href)).
(pose proof Htk as Ht'k; pose proof Htk' as Ht'k'; rewrite <- Hdepeq in Ht'k, Ht'k').
(pose proof (IHk k' t Htk Htk' v) as Ht).
(pose proof (IHk k' t' Ht'k Ht'k' v) as Ht').
tauto.
Qed.
Lemma cname_sem_sub_k_i__sub_d : forall (k : nat) (c : cname), | TCName c | <= k -> forall t2 : ty, ||-[ k][TCName c]<= [t2] -> |- TCName c << t2.
Proof.
(intros k c Hdep t2).
(assert (Hva : value_type (TCName c)) by constructor).
(assert (Hma : |-[ k] TCName c <$ TCName c) by (apply match_ty_i__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); destruct k; simpl in Hsem; subst; constructor || contradiction ])).
-
(apply value_sem_sub_k_i_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; auto).
Qed.
Lemma pair_sem_sub_k_i__sub_d :
  forall k : nat,
  forall ta1 ta2 : ty,
  atom_type (TPair ta1 ta2) ->
  (forall tb1 : ty, ||-[ k][ta1]<= [tb1] -> |- ta1 << tb1) ->
  (forall tb2 : ty, ||-[ k][ta2]<= [tb2] -> |- ta2 << tb2) -> forall t2 : ty, ||-[ k][TPair ta1 ta2]<= [t2] -> |- TPair ta1 ta2 << t2.
Proof.
(intros k ta1 ta2 Hat IH1 IH2).
(pose proof (atom_type__value_type _ Hat) as Hva).
(assert (Hma : |-[ k] TPair ta1 ta2 <$ TPair ta1 ta2) by (apply match_ty_i__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); destruct k; simpl in Hsem; subst; constructor || contradiction ])).
-
(destruct (sem_sub_k_i_pair__inv _ _ _ _ _ Hsem) as [Hsem1 Hsem2]).
(constructor; [ apply IH1 | apply IH2 ]; tauto).
-
(apply value_sem_sub_k_i_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; auto).
Qed.
Lemma nf_sem_sub_k_i__sub_d : forall (k : nat) (t1 : ty), InNF( t1) -> | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2.
Proof.
(induction k;
  match goal with
  | |- forall t1 : ty, InNF( t1) -> | t1 | <= ?k -> forall t2 : ty, ||-[ ?k][t1]<= [t2] -> |- t1 << t2 =>
        apply
         (in_nf_mut (fun (t1 : ty) (_ : atom_type t1) => | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2)
            (fun (t1 : ty) (_ : in_nf t1) => | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2))
  end; try match goal with
           | |- context [ |- TCName _ << _ ] => apply cname_sem_sub_k_i__sub_d
           end).
-
(intros ta1 ta2 Hat1 IH1 Hat2 IH2 Hdep).
(assert (Hat : atom_type (TPair ta1 ta2)) by (constructor; assumption)).
(destruct (max_inv_depth_le__components_le _ _ _ Hdep) as [Hdep1 Hdep2]).
(apply pair_sem_sub_k_i__sub_d; try assumption).
(* Auto-generated comment: Failed. *)

