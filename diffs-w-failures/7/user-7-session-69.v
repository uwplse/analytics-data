Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 148.
Set Silent.
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
Theorem match_ty__value_type_l : forall (v t : ty) (k : nat), |-[ k] v <$ t -> value_type v.
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
Ltac
 solve_match_ty__inv_depth_l__union_r IHt1 IHt2 :=
  match goal with
  | Hm:|-[ _] _ <$ TUnion ?t1 ?t2
    |- _ =>
        apply match_ty_union__inv in Hm; destruct Hm as [Hm| Hm]; [ specialize (IHt1 _ Hm) | specialize (IHt2 _ Hm) ]; split; try tauto;
         rewrite inv_depth_union; [ apply Nat.le_trans with (| t1 |) | apply Nat.le_trans with (| t2 |) ]; try tauto;
         apply Max.le_max_l || apply Max.le_max_r
  end.
Lemma match_ty__inv_depth_l : forall (v t : ty) (k : nat), |-[ k] v <$ t -> | v | <= k /\ | v | <= | t |.
Proof.
(intros v; induction v).
-
(intros t k Hm).
(simpl).
(split; apply Nat.le_0_l).
-
(intros t; induction t; intros k Hm; try (solve [ destruct k; contradiction | solve_match_ty__inv_depth_l__union_r IHt1 IHt2 ])).
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
-
(intros t k Hm).
(apply match_ty__value_type_l in Hm).
(inversion Hm).
-
(intros t; induction t; intros k Hm; try (solve [ destruct k; contradiction | solve_match_ty__inv_depth_l__union_r IHt1 IHt2 ])).
+
clear IHt.
(destruct k).
contradiction.
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heqt' [[Hdept Hdept'] _]]]).
(inversion Heqt'; subst).
(simpl).
(rewrite Hdept').
(split; apply le_n_S; assumption || constructor).
Qed.
Lemma match_ty__inv_depth_l_le_index : forall (v t : ty) (k : nat), |-[ k] v <$ t -> inv_depth v <= k.
Proof.
(apply match_ty__inv_depth_l).
Qed.
Lemma match_ty__inv_depth_l_le_r : forall (v t : ty) (k : nat), |-[ k] v <$ t -> inv_depth v <= inv_depth t.
Proof.
(apply match_ty__inv_depth_l).
Qed.
Lemma match_ty_value_type_r__inv_depth_r_le_index : forall v v' : ty, value_type v' -> forall k : nat, |-[ k] v <$ v' -> inv_depth v' <= k.
Proof.
(intros v v' Hv').
generalize dependent v.
(induction Hv').
-
(intros).
(simpl).
(apply Nat.le_0_l).
-
(intros v k Hm).
(apply match_ty_pair__inv in Hm).
(destruct Hm as [v1' [v2' [Heqp [Hm1 Hm2]]]]; subst).
(simpl; apply Nat.max_lub; [ eapply IHHv'1 | eapply IHHv'2 ]; eassumption).
-
(intros v k Hm).
(destruct k).
(destruct v; contradiction).
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq [[Hdep _] _]]]; subst).
(simpl; apply le_n_S; assumption).
Qed.
Lemma match_ty_value_type__reflexive : forall v : ty, value_type v -> forall k : nat, inv_depth v <= k -> |-[ k] v <$ v.
Proof.
(intros v Hv; induction Hv; intros k Hdep).
-
(destruct k; reflexivity).
-
(simpl in Hdep).
(destruct (max_inv_depth_le__inv v1 v2 k Hdep)).
auto using match_ty_pair.
-
(simpl in Hdep).
(destruct k).
(inversion Hdep).
(apply le_S_n in Hdep).
(simpl).
(split; tauto || apply sem_eq_k__refl).
Qed.
Lemma match_ty__transitive_on_value_type :
  forall v1 v2 t3 : ty, value_type v2 -> forall k : nat, |-[ k] v1 <$ v2 -> |-[ k] v2 <$ t3 -> |-[ k] v1 <$ t3.
Proof.
(intros v1 v2 t3 Hv2).
generalize dependent t3.
generalize dependent v1.
(induction Hv2).
-
(intros v1 t3 k Hm1 Hm2).
(apply match_ty_cname__inv in Hm1; subst).
assumption.
-
(intros v0 t3 k Hm1 Hm2).
(apply match_ty_pair__inv in Hm1).
(destruct Hm1 as [pv11 [pv12 [Heq [Hm11 Hmpv12]]]]; subst).
(induction t3; try (solve [ destruct k; contradiction ])).
+
(apply match_ty_pair__inv in Hm2).
(destruct Hm2 as [pv21 [pv22 [Heq [Hm21 Hm22]]]]).
(inversion Heq; subst).
auto using match_ty_pair.
+
(apply match_ty_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
-
(intros v1 t3 k Hm1 Hm2).
(destruct k).
(destruct v1; inversion Hm1).
(apply match_ty_ref__inv in Hm1).
(destruct Hm1 as [t' [Heq [[Hdept Hdept'] Href]]]; subst).
(induction t3; try (solve [ destruct k; contradiction ])).
+
(apply match_ty_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_union_1 | apply match_ty_union_2 ]; tauto).
+
clear IHt3.
(apply match_ty_ref__inv in Hm2).
(destruct Hm2 as [t'' [Heq' [[Hdepv3 Hdept''] Href']]]).
(inversion Heq'; subst).
(simpl).
(rewrite Hdept').
(split; tauto || eapply sem_eq_k__trans; eassumption).
Qed.
Lemma match_ty_value_type_r : forall v : ty, value_type v -> forall k : nat, ~ (exists v' : ty, |-[ k] v' <$ v) \/ | v | <= k.
Proof.
(intros v Hv).
(induction Hv; intros k).
-
(right; simpl; apply Nat.le_0_l).
-
(specialize (IHHv1 k); specialize (IHHv2 k)).
(destruct IHHv1 as [IHv1| IHv1]; destruct IHHv2 as [IHv2| IHv2];
  try (solve
   [ left; intros Hcontra; destruct Hcontra as [v Hm]; apply match_ty_pair__inv in Hm; destruct Hm as [v1' [v2' [Heq [Hm1 Hm2]]]]; subst;
      apply IHv1 || apply IHv2; eexists; eassumption ])).
(right; apply Nat.max_lub; assumption).
-
(destruct (dec_le (| TRef t |) k) as [Hle| Hle]).
+
(right; assumption).
+
(left; intros Hcontra).
(destruct Hcontra as [v' Hm]).
(destruct k).
(destruct v'; contradiction).
(assert (Hdep : | TRef t | <= S k) by (eapply match_ty_value_type_r__inv_depth_r_le_index; constructor || eassumption)).
contradiction.
Qed.
Lemma value_type_matching_ty__exists : forall (t : ty) (k : nat), inv_depth t <= k -> exists v : ty, |-[ k] v <$ t.
Proof.
(intros t; induction t; intros k Hdep).
-
exists (TCName c).
(destruct k; reflexivity).
-
(destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]).
(destruct (IHt1 k Hdep1) as [v1 Hm1]).
(destruct (IHt2 k Hdep2) as [v2 Hm2]).
exists (TPair v1 v2).
(apply match_ty_pair; assumption).
-
(destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]).
(destruct (IHt1 k Hdep1) as [v Hm]).
exists v.
(apply match_ty_union_1; assumption).
-
exists (TRef t).
(apply match_ty_value_type__reflexive; constructor || assumption).
Qed.
Set Printing Width 148.
Set Silent.
Lemma match_ty__pair_unite_pairs :
  forall (t1 t2 v1 v2 : ty) (k : nat), |-[ k] v1 <$ t1 -> |-[ k] v2 <$ t2 -> |-[ k] TPair v1 v2 <$ unite_pairs t1 t2.
Unset Silent.
Proof.
Set Silent.
(intros ta; induction ta; intros tb; induction tb; intros v1 v2 k Hm1 Hm2; try (solve [ simpl; apply match_ty_pair; assumption ]);
  try
   match goal with
   | |- |-[ k] TPair ?v1 ?v2 <$ unite_pairs ?tx (TUnion ?tb1 ?tb2) =>
         change_no_check (|-[ k] TPair v1 v2 <$ TUnion (unite_pairs tx tb1) (unite_pairs tx tb2)); apply match_ty_union__inv in Hm2;
          destruct Hm2 as [Hm2| Hm2]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto
   end;
  try
   match goal with
   | |- |-[ k] TPair ?v1 ?v2 <$ unite_pairs (TUnion ?tb1 ?tb2) ?tx =>
         change_no_check (|-[ k] TPair v1 v2 <$ TUnion (unite_pairs tb1 tx) (unite_pairs tb2 tx)); apply match_ty_union__inv in Hm1;
          destruct Hm1 as [Hm1| Hm1]; [ apply match_ty_union_1 | apply match_ty_union_2 ]; auto
   end).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty__unite_pairs_pair : forall (t1 t2 v : ty) (k : nat), |-[ k] v <$ unite_pairs t1 t2 -> |-[ k] v <$ TPair t1 t2.
Proof.
(intros ta; induction ta; intros tb; induction tb; intros v k Hm; try (solve [ simpl; assumption ]);
  try
   match goal with
   | Hm:|-[ k] ?v <$ unite_pairs ?tx (TUnion ?tb1 ?tb2)
     |- _ =>
         change_no_check (|-[ k] v <$ TUnion (unite_pairs tx tb1) (unite_pairs tx tb2)) in Hm; apply match_ty_union__inv in Hm;
          destruct Hm as [Hm| Hm]; [ specialize (IHtb1 _ _ Hm) | specialize (IHtb2 _ _ Hm) ];
          match goal with
          | IHtb:|-[ k] v <$ TPair tx ?tb
            |- _ =>
                apply match_ty_pair__inv in IHtb; destruct IHtb as [v1' [v2' [Heq [Hm1' Hm2]]]]; subst; apply match_ty_pair; try assumption;
                 try (solve [ apply match_ty_union_1; assumption | apply match_ty_union_2; assumption ])
          end
   end;
  try
   match goal with
   | Hm:|-[ k] ?v <$ unite_pairs (TUnion ?tb1 ?tb2) ?tx
     |- _ =>
         change_no_check (|-[ k] v <$ TUnion (unite_pairs tb1 tx) (unite_pairs tb2 tx)) in Hm; apply match_ty_union__inv in Hm;
          destruct Hm as [Hm| Hm]; [ specialize (IHta1 _ _ _ Hm) | specialize (IHta2 _ _ _ Hm) ];
          match goal with
          | IHtb:|-[ k] v <$ TPair ?tb tx
            |- _ =>
                apply match_ty_pair__inv in IHtb; destruct IHtb as [v1' [v2' [Heq [Hm1' Hm2]]]]; subst; apply match_ty_pair; try assumption;
                 try (solve [ apply match_ty_union_1; assumption | apply match_ty_union_2; assumption ])
          end
   end).
Unset Silent.
Qed.
Set Silent.
Lemma match_ty_nf : forall (k : nat) (t : ty), ||-[ k][t]= [MkNF( t)].
Proof.
Unset Silent.
(induction k; induction t; intros v; split; intros Hm; try (solve [ simpl; assumption ]);
  try
   match goal with
   | Hm:|-[ _] ?v <$ TPair ?t1 ?t2
     |- |-[ _] ?v <$ MkNF( TPair ?t1 ?t2) =>
         apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; rewrite mk_nf_pair; apply match_ty__pair_unite_pairs;
          [ apply IHt1 | apply IHt2 ]; assumption
   | Hm:|-[ _] ?v <$ MkNF( TPair ?t1 ?t2)
     |- |-[ _] ?v <$ TPair ?t1 ?t2 =>
         rewrite mk_nf_pair in Hm; apply match_ty__unite_pairs_pair in Hm; apply match_ty_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]];
          subst; apply match_ty_pair; [ apply IHt1 | apply IHt2 ]; assumption
   end;
  try
   match goal with
   | Hm:|-[ _] ?v <$ TUnion ?t1 ?t2
     |- |-[ _] ?v <$ MkNF( TUnion ?t1 ?t2) =>
         rewrite mk_nf_union; apply match_ty_union__inv in Hm; destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ];
          [ apply IHt1 | apply IHt2 ]; assumption
   | Hm:|-[ _] ?v <$ MkNF( TUnion ?t1 ?t2)
     |- |-[ _] ?v <$ TUnion ?t1 ?t2 =>
         rewrite mk_nf_union in Hm; apply match_ty_union__inv in Hm; destruct Hm as [Hm| Hm]; [ apply match_ty_union_1 | apply match_ty_union_2 ];
          [ apply IHt1 | apply IHt2 ]; assumption
   end; try (solve [ destruct v; contradiction ])).
Set Silent.
-
Unset Silent.
Show.
clear IHt.
(rewrite mk_nf_ref).
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq [[Hdept Hdept'] Href]]]; subst).
(simpl).
(rewrite inv_depth_mk_nf).
split.
tauto.
Set Printing Width 148.
(eapply sem_eq_k__trans; eauto).
Set Silent.
-
Unset Silent.
Show.
clear IHt.
(rewrite mk_nf_ref in Hm).
(apply match_ty_ref__inv in Hm).
(destruct Hm as [t' [Heq [[Hdept Hdept'] Href]]]; subst).
(rewrite inv_depth_mk_nf in Hdept, Hdept').
split.
tauto.
(eapply sem_eq_k__trans; eauto).
Set Printing Width 148.
(apply sem_eq_k__comm; auto).
Qed.
