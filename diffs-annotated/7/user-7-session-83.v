Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
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
Lemma cname_sem_sub_k_i__sub_d : forall (k : nat) (c : cname) (t2 : ty), ||-[ k][TCName c]<= [t2] -> |- TCName c << t2.
Proof.
(intros k c t2).
(assert (Hva : value_type (TCName c)) by constructor).
(assert (Hma : |-[ k] TCName c <$ TCName c) by (apply match_ty_i__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); destruct k; simpl in Hsem; subst; constructor || contradiction ])).
-
(apply value_sem_sub_k_i_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; auto).
Qed.
Lemma pair_sem_sub_k_i__sub_d :
  forall (k : nat) (ta1 ta2 : ty),
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
  end; try tauto;
  try
   match goal with
   | |- context [ |- TCName _ << _ ] => intros c Hdep; apply cname_sem_sub_k_i__sub_d; assumption
   | |- context [ |- TPair _ _ << _ ] =>
         intros ta1 ta2 Hat1 IH1 Hat2 IH2 Hdep; assert (Hat : atom_type (TPair ta1 ta2)) by (constructor; assumption);
          destruct (max_inv_depth_le__components_le _ _ _ Hdep) as [Hdep1 Hdep2]; apply pair_sem_sub_k_i__sub_d; tauto
   | |- context [ |- TUnion _ _ << _ ] =>
         intros t1 t2 Hnf1 IH1 Hnf2 IH2 Hdep; destruct (max_inv_depth_le__components_le _ _ _ Hdep) as [Hdep1 Hdep2]; intros t' Hsem;
          apply sem_sub_k_union_l__inv in Hsem; destruct Hsem as [Hsem1 Hsem2]; constructor; auto
   end).
(* Failed. *)
