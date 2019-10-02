Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Require Import BetaJulia.Sub0250a.BaseProps.
Require Import BetaJulia.Sub0250a.MatchProps.
Require Import BetaJulia.Sub0250a.SemSubProps.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Open Scope btjt_scope.
Open Scope btjm_scope.
Open Scope btjnf_scope.
Open Scope btjd_scope.
Lemma sub_d__inv_depth_le : forall t t' : ty, |- t << t' -> | t | <= | t' |.
Proof.
(intros t t' Hsub).
(induction Hsub).
-
constructor.
-
(apply Nat.le_trans with (| t2 |); assumption).
-
(simpl).
(apply Nat.max_le_compat; assumption).
-
(simpl).
(apply Nat.max_lub; assumption).
-
(simpl).
(apply Nat.le_max_l).
-
(simpl).
(apply Nat.le_max_r).
-
(simpl).
(rewrite max_baca_eq_bca).
constructor.
-
(simpl).
(rewrite max_abac_eq_abc).
constructor.
-
(simpl).
(apply le_n_S).
assumption.
Qed.
Lemma sub_d_eq__inv_depth_eq : forall t t' : ty, |- t << t' -> |- t' << t -> | t | = | t' |.
Proof.
(intros t t' Hsub1 Hsub2).
(apply Nat.le_antisymm; apply sub_d__inv_depth_le; assumption).
Qed.
Lemma unite_pairs__preserves_sub_d_l : forall t1 t2 t1' t2' : ty, |- t1 << t1' -> |- t2 << t2' -> |- unite_pairs t1 t2 << TPair t1' t2'.
Proof.
(intros ta; induction ta; intros tb;
  try (solve
   [ induction tb; intros ta' tb' Hsub1 Hsub2; try (solve [ simpl; constructor; assumption ]);
      destruct (sub_d_union_l__inv _ _ _ Hsub2) as [Hsub21 Hsub22]; rewrite unite_pairs_t_union; try resolve_not_union; constructor;
      [ apply IHtb1 | apply IHtb2 ]; assumption ])).
-
(intros ta' tb' Hsub1 Hsub2).
(apply sub_d_union_l__inv in Hsub1).
(destruct Hsub1 as [Hsub11 Hsub12]).
(rewrite unite_pairs_union_t).
(constructor; [ apply IHta1 | apply IHta2 ]; assumption).
Qed.
Lemma unite_pairs__preserves_sub_d_r : forall t1' t2' t1 t2 : ty, |- t1 << t1' -> |- t2 << t2' -> |- TPair t1 t2 << unite_pairs t1' t2'.
Proof.
(intros ta'; induction ta'; intros tb';
  try (solve
   [ induction tb'; intros ta tb Hsub1 Hsub2; try (solve [ simpl; constructor; assumption ]); rewrite unite_pairs_t_union; try resolve_not_union;
      apply SD_Trans with (TPair ta (TUnion tb'1 tb'2));
      [ constructor; constructor || assumption
      | apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)); apply SD_Distr2 || apply SD_UnionL;
         [ apply union_right_1; apply IHtb'1 | apply union_right_2; apply IHtb'2 ]; assumption || constructor ] ])).
-
(intros ta tb Hsub1 Hsub2).
(rewrite unite_pairs_union_t).
(apply SD_Trans with (TPair (TUnion ta'1 ta'2) tb)).
+
(constructor; constructor || assumption).
+
(apply SD_Trans with (TUnion (TPair ta'1 tb) (TPair ta'2 tb))).
(apply SD_Distr1).
(apply SD_UnionL).
(apply union_right_1; apply IHta'1; assumption || constructor).
(apply union_right_2; apply IHta'2; assumption || constructor).
Qed.
Theorem mk_nf__sub_d_eq : forall t : ty, |- MkNF( t) << t /\ |- t << MkNF( t).
Proof.
(induction t).
-
(split; simpl; constructor).
-
(destruct IHt1; destruct IHt2).
(split; simpl).
(apply unite_pairs__preserves_sub_d_l; assumption).
(apply unite_pairs__preserves_sub_d_r; assumption).
-
(destruct IHt1; destruct IHt2).
(split; simpl; constructor; (apply union_right_1; assumption) || (apply union_right_2; assumption)).
-
(simpl).
(destruct IHt).
(split; constructor; assumption).
Qed.
Lemma mk_nf__sub_d_l : forall t : ty, |- MkNF( t) << t.
Proof.
(apply mk_nf__sub_d_eq).
Qed.
Lemma mk_nf__sub_d_r : forall t : ty, |- t << MkNF( t).
Proof.
(apply mk_nf__sub_d_eq).
Qed.
Lemma cname_sem_sub_k__sub_d : forall (k : nat) (c : cname), | TCName c | <= k -> forall t2 : ty, ||-[ k][TCName c]<= [t2] -> |- TCName c << t2.
Proof.
(intros k c Hdep t2).
(assert (Hva : value_type (TCName c)) by constructor).
(assert (Hma : |-[ k] TCName c <$ TCName c) by (apply match_ty_value_type__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); destruct k; simpl in Hsem; subst; constructor || contradiction ])).
-
(apply value_sem_sub_k_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; tauto).
Qed.
Lemma pair_sem_sub_k__sub_d :
  forall (k : nat) (ta1 ta2 : ty),
  atom_type (TPair ta1 ta2) ->
  | TPair ta1 ta2 | <= k ->
  (forall tb1 : ty, ||-[ k][ta1]<= [tb1] -> |- ta1 << tb1) ->
  (forall tb2 : ty, ||-[ k][ta2]<= [tb2] -> |- ta2 << tb2) -> forall t2 : ty, ||-[ k][TPair ta1 ta2]<= [t2] -> |- TPair ta1 ta2 << t2.
Proof.
(intros k ta1 ta2 Hat Hdep IH1 IH2).
(assert (Hva : value_type (TPair ta1 ta2)) by (apply atom_type__value_type; assumption)).
(assert (Hma : |-[ k] TPair ta1 ta2 <$ TPair ta1 ta2) by (apply match_ty_value_type__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); destruct k; simpl in Hsem; subst; constructor || contradiction ])).
-
clear IHt2_1 IHt2_2.
(destruct (sem_sub_k_pair__inv _ _ _ _ _ Hdep Hsem) as [Hsem1 Hsem2]).
(constructor; [ apply IH1 | apply IH2 ]; tauto).
-
(apply value_sem_sub_k_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; tauto).
Qed.
Lemma nf_sem_sub_k__sub_d : forall (k : nat) (t1 : ty), InNF( t1) -> | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2.
Proof.
(induction k;
  match goal with
  | |- forall t1 : ty, InNF( t1) -> | t1 | <= ?k -> forall t2 : ty, ||-[ ?k][t1]<= [t2] -> |- t1 << t2 =>
        apply
         (in_nf_mut (fun (t1 : ty) (_ : atom_type t1) => | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2)
            (fun (t1 : ty) (_ : in_nf t1) => | t1 | <= k -> forall t2 : ty, ||-[ k][t1]<= [t2] -> |- t1 << t2))
  end;
  try
   match goal with
   | |- context [ |- TCName _ << _ ] => apply cname_sem_sub_k__sub_d
   | |- context [ |- TPair _ _ << _ ] =>
         intros ta1 ta2 Hat1 IH1 Hat2 IH2 Hdep; assert (Hatp : atom_type (TPair ta1 ta2)) by (constructor; assumption);
          destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]; specialize (IH1 Hdep1); specialize (IH2 Hdep2); 
          apply pair_sem_sub_k__sub_d; assumption
   | |- context [ |- TUnion _ _ << _ ] =>
         intros t1 t2 Hnf1 IH1 Hnf2 IH2 Hdep; destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]; intros t' Hsem;
          apply sem_sub_k_union_l__inv in Hsem; destruct Hsem as [Hsem1 Hsem2]; constructor; auto
   | |- forall ta : ty, atom_type ta -> _ => tauto
   end).
-
(intros t Hnft IHt Hdt).
(inversion Hdt).
-
(intros t Hnft IH).
(intros Hdt t2).
(assert (Hva : value_type (TRef t)) by constructor).
(assert (Hma : |-[ S k] TRef t <$ TRef t) by (apply match_ty_value_type__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); contradiction ])).
+
(apply value_sem_sub_k_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; tauto).
+
clear IHt2.
(simpl in Hdt).
(pose proof (le_S_n _ _ Hdt) as Hdt').
(pose proof Hsem as Hsem').
(unfold sem_sub_k in Hsem).
specialize (Hsem _ Hma).
(apply match_ty_ref__inv in Hsem).
(destruct Hsem as [t' [Heqt' [[Hk Hdt't2] Href]]]).
(inversion Heqt'; subst).
clear Heqt'.
constructor.
*
(apply IHk; try assumption).
(apply sem_eq_k__sem_sub_k in Href).
tauto.
*
(apply SD_Trans with (MkNF( t2))).
(apply mk_nf__sub_d_r; assumption).
(apply IHk).
(apply mk_nf__in_nf).
(rewrite inv_depth_mk_nf).
assumption.
(apply mk_nf__sem_sub_k_l).
(apply sem_eq_k__trans with t2).
(* Failed. *)
