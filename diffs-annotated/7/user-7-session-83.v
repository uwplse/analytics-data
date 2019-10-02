Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Add LoadPath "../..".
Require Import BetaJulia.BasicPLDefs.Identifier.
Require Import BetaJulia.Sub0250a.BaseDefs.
Lemma sem_eq_k_i__sem_sub_k_i : forall (k : nat) (t t' : ty), ||-[ k][t]= [t'] -> ||-[ k][t]<= [t'] /\ ||-[ k][t']<= [t].
Proof.
(intros k t t' H).
(split; intros v Hm; specialize (H v); tauto).
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
          destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]; apply pair_sem_sub_k_i__sub_d; tauto
   | |- context [ |- TUnion _ _ << _ ] =>
         intros t1 t2 Hnf1 IH1 Hnf2 IH2 Hdep; destruct (max_inv_depth_le__inv _ _ _ Hdep) as [Hdep1 Hdep2]; intros t' Hsem;
          apply sem_sub_k_i_union_l__inv in Hsem; destruct Hsem as [Hsem1 Hsem2]; constructor; auto
   end).
-
(intros t Hnft _ Hdep).
(inversion Hdep).
-
(intros t Hnft _ Hdep t2).
(assert (Hva : value_type (TRef t)) by constructor).
(assert (Hma : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; assumption)).
(induction t2; intros Hsem; try (solve [ specialize (Hsem _ Hma); contradiction ])).
+
(apply value_sem_sub_k_i_union__inv in Hsem; try assumption).
(destruct Hsem as [Hsem| Hsem]; [ apply union_right_1 | apply union_right_2 ]; auto).
+
clear IHt2.
(simpl in Hdep).
(pose proof (le_S_n _ _ Hdep) as Hdep').
(unfold sem_sub_k in Hsem).
specialize (Hsem _ Hma).
(apply match_ty_i_ref__inv in Hsem).
(destruct Hsem as [t' [Heqt' Href]]).
(inversion Heqt'; subst).
clear Heqt'.
constructor.
*
(apply IHk; try assumption).
(apply sem_eq_k_i__sem_sub_k_i in Href).
tauto.
*
(apply SD_Trans with (MkNF( t2))).
(apply mk_nf__sub_d_r; assumption).
(* Failed. *)
