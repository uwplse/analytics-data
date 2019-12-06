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
Check sem_eq_k_i__trans.
(eapply sem_eq_k_i__trans; eauto).
-
clear IHt.
(rewrite mk_nf_ref in Hm).
(apply match_ty_i_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(simpl).
(eapply sem_eq_k_i__trans; eauto).
(apply sem_eq_k_i__comm).
assumption.
(* Auto-generated comment: Failed. *)

(* Auto-generated comment: At 2019-08-16 14:13:16.840000.*)

