Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.AltMatchDef.
Require Import BetaJulia.Sub0250a.DeclSubProps.
Require Import BetaJulia.BasicTactics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Close Scope btjm.
Open Scope btjmi.
Lemma sem_eq_k_i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]= [t2] -> ||-[ k][t2]= [t3] -> ||-[ k][t1]= [t3].
Proof.
(intros k t1 t2 t3 Hsem1 Hsem2).
(unfold sem_eq_k in *).
(intros v).
specialize (Hsem1 v).
specialize (Hsem2 v).
tauto.
Qed.
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
(induction t3; try (solve [ destruct k; contradiction ])).
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
(induction t3; try (solve [ destruct k; contradiction ])).
+
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
+
clear IHt3.
(destruct k).
(destruct v1; contradiction || constructor).
(apply match_ty_i_ref__inv in Hm1).
(destruct Hm1 as [tx [Heqx Hrefx]]; inversion Heqx; subst).
(simpl in Hm2).
(apply sem_eq_k_i__trans with t; assumption).
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
Lemma sem_sub_k_i__trans : forall (k : nat) (t1 t2 t3 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t3] -> ||-[ k][t1]<= [t3].
Proof.
auto with DBBetaJulia.
Qed.
Lemma sem_eq_k_i__sem_sub_k_i : forall (k : nat) (t t' : ty), ||-[ k][t]= [t'] -> ||-[ k][t]<= [t'] /\ ||-[ k][t']<= [t].
Proof.
(intros k t t' H).
(split; intros v Hm; specialize (H v); tauto).
Qed.
Lemma sem_eq_k_i__comm : forall (k : nat) (t1 t2 : ty), ||-[ k][t1]= [t2] -> ||-[ k][t2]= [t1].
Proof.
(intros k t1 t2 Hsem).
(unfold sem_eq_k in *).
(intros v).
specialize (Hsem v).
tauto.
Qed.
Lemma sem_sub_k_i__sem_eq_k_i : forall (k : nat) (t1 t2 : ty), ||-[ k][t1]<= [t2] -> ||-[ k][t2]<= [t1] -> ||-[ k][t1]= [t2].
Proof.
(intros k t1 t2 Hsem1 Hsem2).
(split; auto).
Qed.
Lemma sem_sub_k_i_union_l__inv : forall (k : nat) (t1 t2 t' : ty), ||-[ k][TUnion t1 t2]<= [t'] -> ||-[ k][t1]<= [t'] /\ ||-[ k][t2]<= [t'].
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
Lemma match_ty_i__pair_unite_pairs :
  forall (t1 t2 v1 v2 : ty) (k : nat), |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ unite_pairs t1 t2.
Proof.
(intros ta; induction ta; intros tb; induction tb; intros v1 v2 k Hm1 Hm2; try (solve [ simpl; apply match_ty_i_pair; assumption ]);
  try
   match goal with
   | |- |-[ k] TPair ?v1 ?v2 <$ unite_pairs ?tx (TUnion ?tb1 ?tb2) =>
         change_no_check (|-[ k] TPair v1 v2 <$ TUnion (unite_pairs tx tb1) (unite_pairs tx tb2)); apply match_ty_i_union__inv in Hm2;
          destruct Hm2 as [Hm2| Hm2]; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; auto
   end;
  try
   match goal with
   | |- |-[ k] TPair ?v1 ?v2 <$ unite_pairs (TUnion ?tb1 ?tb2) ?tx =>
         change_no_check (|-[ k] TPair v1 v2 <$ TUnion (unite_pairs tb1 tx) (unite_pairs tb2 tx)); apply match_ty_i_union__inv in Hm1;
          destruct Hm1 as [Hm1| Hm1]; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; auto
   end).
Qed.
Lemma match_ty_i__unite_pairs_pair : forall (t1 t2 v : ty) (k : nat), |-[ k] v <$ unite_pairs t1 t2 -> |-[ k] v <$ TPair t1 t2.
Proof.
(intros ta; induction ta; intros tb; induction tb; intros v k Hm; try (solve [ simpl; assumption ]);
  try
   match goal with
   | Hm:|-[ k] ?v <$ unite_pairs ?tx (TUnion ?tb1 ?tb2)
     |- _ =>
         change_no_check (|-[ k] v <$ TUnion (unite_pairs tx tb1) (unite_pairs tx tb2)) in Hm; apply match_ty_i_union__inv in Hm;
          destruct Hm as [Hm| Hm]; [ specialize (IHtb1 _ _ Hm) | specialize (IHtb2 _ _ Hm) ];
          match goal with
          | IHtb:|-[ k] v <$ TPair tx ?tb
            |- _ =>
                apply match_ty_i_pair__inv in IHtb; destruct IHtb as [v1' [v2' [Heq [Hm1' Hm2]]]]; subst; apply match_ty_i_pair; try assumption;
                 try (solve [ apply match_ty_i_union_1; assumption | apply match_ty_i_union_2; assumption ])
          end
   end;
  try
   match goal with
   | Hm:|-[ k] ?v <$ unite_pairs (TUnion ?tb1 ?tb2) ?tx
     |- _ =>
         change_no_check (|-[ k] v <$ TUnion (unite_pairs tb1 tx) (unite_pairs tb2 tx)) in Hm; apply match_ty_i_union__inv in Hm;
          destruct Hm as [Hm| Hm]; [ specialize (IHta1 _ _ _ Hm) | specialize (IHta2 _ _ _ Hm) ];
          match goal with
          | IHtb:|-[ k] v <$ TPair ?tb tx
            |- _ =>
                apply match_ty_i_pair__inv in IHtb; destruct IHtb as [v1' [v2' [Heq [Hm1' Hm2]]]]; subst; apply match_ty_i_pair; try assumption;
                 try (solve [ apply match_ty_i_union_1; assumption | apply match_ty_i_union_2; assumption ])
          end
   end).
Qed.
Lemma match_ty_i_nf : forall (k : nat) (t : ty), ||-[ k][t]= [MkNF( t)].
Proof.
(induction k; induction t; intros v; split; intros Hm; try (solve [ simpl; assumption ]);
  try
   match goal with
   | Hm:|-[ _] ?v <$ TPair ?t1 ?t2
     |- |-[ _] ?v <$ MkNF( TPair ?t1 ?t2) =>
         apply match_ty_i_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; rewrite mk_nf_pair; apply match_ty_i__pair_unite_pairs;
          [ apply IHt1 | apply IHt2 ]; assumption
   | Hm:|-[ _] ?v <$ MkNF( TPair ?t1 ?t2)
     |- |-[ _] ?v <$ TPair ?t1 ?t2 =>
         rewrite mk_nf_pair in Hm; apply match_ty_i__unite_pairs_pair in Hm; apply match_ty_i_pair__inv in Hm;
          destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; apply match_ty_i_pair; [ apply IHt1 | apply IHt2 ]; assumption
   end;
  try
   match goal with
   | Hm:|-[ _] ?v <$ TUnion ?t1 ?t2
     |- |-[ _] ?v <$ MkNF( TUnion ?t1 ?t2) =>
         rewrite mk_nf_union; apply match_ty_i_union__inv in Hm; destruct Hm as [Hm| Hm]; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ];
          [ apply IHt1 | apply IHt2 ]; assumption
   | Hm:|-[ _] ?v <$ MkNF( TUnion ?t1 ?t2)
     |- |-[ _] ?v <$ TUnion ?t1 ?t2 =>
         rewrite mk_nf_union in Hm; apply match_ty_i_union__inv in Hm; destruct Hm as [Hm| Hm];
          [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; [ apply IHt1 | apply IHt2 ]; assumption
   end; try (solve [ rewrite mk_nf_ref in *; apply match_ty_i_ref__weak_inv in Hm; destruct Hm as [t' Heq]; subst; constructor ])).
-
clear IHt.
(rewrite mk_nf_ref).
(apply match_ty_i_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(simpl).
(eapply sem_eq_k_i__trans; eauto).
-
clear IHt.
(rewrite mk_nf_ref in Hm).
(apply match_ty_i_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(simpl).
(eapply sem_eq_k_i__trans; eauto).
(apply sem_eq_k_i__comm; auto).
Qed.
Theorem mk_nf__sem_eq_k_i : forall (k : nat) (t : ty), ||-[ k][t]= [MkNF( t)].
Proof.
(apply match_ty_i_nf).
Qed.
Lemma mk_nf__sem_sub_k_i_l : forall (k : nat) (t : ty), ||-[ k][MkNF( t)]<= [t].
Proof.
(intros k t).
(apply sem_eq_k_i__sem_sub_k_i).
(apply mk_nf__sem_eq_k_i).
Qed.
Ltac
 solve__value_sem_sub_i_union__inv_depth_le_1 Hv Hsem t'1 t'2 :=
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
           assert (Hv : value_type (TPair t1 t2)) by (apply pair_in_nf__value_type; assumption);
            solve__value_sem_sub_i_union__inv_depth_le_1 Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][?t]<= [TUnion ?t'1 ?t'2]
       |- | ?t | <= _ => assert (Hv : value_type t) by constructor; solve__value_sem_sub_i_union__inv_depth_le_1 Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][TPair ?t1 ?t2]<= [?t']
       |- _ <= | ?t' | =>
           assert (Hvp : value_type (TPair t1 t2)) by (apply pair_in_nf__value_type; assumption);
            assert (Hmp : |-[ k] TPair t1 t2 <$ TPair t1 t2) by (apply match_ty_i__reflexive; assumption); specialize (Hsem _ Hmp); contradiction
     | Hsem:||-[ ?k][TPair _ _]<= [TPair _ _]
       |- _ =>
           destruct (in_nf_pair__inv _ _ Hnft) as [Hnft1 Hnft2]; destruct (max_inv_depth_le__inv _ _ _ Hdept) as [Hdept1 Hdept2];
            destruct (sem_sub_k_i_pair__inv _ _ _ _ _ Hsem) as [Hsem1 Hsem2]; simpl; apply Nat.max_le_compat; auto
     | Hsem:||-[ ?k][TUnion _ _]<= [_], Hnft:InNF( TUnion _ _), Hdept:| TUnion _ _ | <= _
       |- _ =>
           destruct (max_inv_depth_le__inv _ _ _ Hdept) as [Hdept1 Hdept2]; destruct (sem_sub_k_i_union_l__inv _ _ _ _ Hsem) as [HSem1 Hsem2];
            destruct (in_nf_union__inv _ _ Hnft) as [Hnft1 Hnft2]; rewrite inv_depth_union; apply Nat.max_lub; auto
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
  destruct (max_inv_depth_le__inv _ _ _ Hdept') as [Hdept'1 Hdept'2]; pose proof (value_sem_sub_k_i_union__inv _ Hv _ _ _ Hsem) as Hsemu;
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
           assert (Hv : value_type (TPair t1 t2)) by (apply pair_in_nf__value_type; assumption);
            solve__value_sem_sub_i_union__inv_depth_le_2 Hdept' Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][?t]<= [TUnion ?t'1 ?t'2]
       |- | ?t | <= _ => assert (Hv : value_type t) by constructor; solve__value_sem_sub_i_union__inv_depth_le_2 Hdept' Hv Hsem t'1 t'2
     | Hsem:||-[ ?k][TPair ?t1 ?t2]<= [?t']
       |- _ <= | ?t' | =>
           assert (Hvp : value_type (TPair t1 t2)) by (apply pair_in_nf__value_type; assumption);
            assert (Hmp : |-[ k] TPair t1 t2 <$ TPair t1 t2) by (apply match_ty_i__reflexive; assumption); specialize (Hsem _ Hmp); contradiction
     | Hsem:||-[ ?k][TPair _ _]<= [TPair _ _]
       |- _ =>
           destruct (in_nf_pair__inv _ _ Hnft) as [Hnft1 Hnft2]; destruct (max_inv_depth_le__inv _ _ _ Hdept') as [Hdept'1 Hdept'2];
            destruct (sem_sub_k_i_pair__inv _ _ _ _ _ Hsem) as [Hsem1 Hsem2]; simpl; apply Nat.max_le_compat; auto
     | Hsem:||-[ ?k][TUnion _ _]<= [_], Hnft:InNF( TUnion _ _)
       |- _ =>
           destruct (sem_sub_k_i_union_l__inv _ _ _ _ Hsem) as [HSem1 Hsem2]; destruct (in_nf_union__inv _ _ Hnft) as [Hnft1 Hnft2];
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
Lemma sem_sub_k_i__inv_depth_le_1 : forall (k : nat) (t t' : ty), | t | <= k -> ||-[ k][t]<= [t'] -> | t | <= | t' |.
Proof.
(intros k t t' Hdept Hsem).
(rewrite <- inv_depth_mk_nf).
(apply sem_sub_k_i_nf__inv_depth_le_1 with k).
(apply mk_nf__in_nf).
(rewrite inv_depth_mk_nf; assumption).
(apply sem_sub_k_i__trans with t; try assumption).
(apply mk_nf__sem_sub_k_i_l).
Qed.
Lemma sem_sub_k_i__inv_depth_le_2 : forall (k : nat) (t t' : ty), | t' | <= k -> ||-[ k][t]<= [t'] -> | t | <= | t' |.
Proof.
(intros k t t' Hdept' Hsem).
(rewrite <- inv_depth_mk_nf).
(apply sem_sub_k_i_nf__inv_depth_le_2 with k).
(apply mk_nf__in_nf).
assumption.
(apply sem_sub_k_i__trans with t; try assumption).
(apply mk_nf__sem_sub_k_i_l).
Qed.
Lemma sem_eq_k_i__inv_depth_eq_1 : forall (k : nat) (t t' : ty), | t | <= k -> ||-[ k][t]= [t'] -> | t | = | t' |.
Proof.
(intros k t t' Hdept H).
(destruct (sem_eq_k_i__sem_sub_k_i _ _ _ H) as [H1 H2]).
(pose proof (sem_sub_k_i__inv_depth_le_1 _ _ _ Hdept H1)).
(pose proof (sem_sub_k_i__inv_depth_le_2 _ _ _ Hdept H2)).
(apply Nat.le_antisymm; assumption).
Qed.
Lemma sem_sub_i__trans : forall t1 t2 t3 : ty, ||- [t1]<= [t2] -> ||- [t2]<= [t3] -> ||- [t1]<= [t3].
Proof.
auto with DBBetaJulia.
Qed.
Lemma mk_nf__sem_sub_i_l : forall t : ty, ||- [MkNF( t)]<= [t].
Proof.
(intros t k).
(apply mk_nf__sem_sub_k_i_l).
Qed.
Lemma sem_sub_i_union_l__inv : forall t1 t2 t' : ty, ||- [TUnion t1 t2]<= [t'] -> ||- [t1]<= [t'] /\ ||- [t2]<= [t'].
Proof.
(intros t1 t2 t' Hsem).
(unfold sem_sub_i in Hsem).
(split; intros k; specialize (Hsem k); destruct (sem_sub_k_i_union_l__inv _ _ _ _ Hsem); assumption).
Qed.
Lemma sem_sub_i_ref__inv : forall t t' : ty, ||- [TRef t]<= [TRef t'] -> ||- [t]<= [t'] /\ ||- [t']<= [t].
Proof.
(intros t t' Hsem).
(split; intros k; specialize (Hsem (S k)); assert (Hvref : value_type (TRef t)) by constructor;
  assert (Hm : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; assumption); specialize (Hsem _ Hm); simpl in Hsem; 
  intros v' Hm'; specialize (Hsem v'); tauto).
Qed.
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
