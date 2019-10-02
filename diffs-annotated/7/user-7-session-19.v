Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
(intros v; split; intros Hm; specialize (Hrefx v); specialize (Hrefy v); tauto).
Qed.
Lemma value_sem_sub_k_union__value_sem_sub_k_component :
  forall k : nat, forall v : ty, value_type v -> forall ta tb : ty, ||-[ k][v]<= [TUnion ta tb] -> ||-[ k][v]<= [ta] \/ ||-[ k][v]<= [tb].
Proof.
(induction k; intros v Hv; induction Hv; intros ta tb Hsem).
6: {
idtac.
(unfold sem_sub_k_i in Hsem).
(assert (Hvref : value_type (TRef t)) by constructor).
(assert (Hmref : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; assumption)).
(pose proof (Hsem _ Hvref Hmref) as Hmu).
(apply match_ty_i_union__inv in Hmu).
(destruct Hmu as [Hmu1| Hmu2]; [ left | right ]; intros v Hv Hm; apply match_ty_i_ref__inv in Hm; destruct Hm as [t' [Heq Href]]; subst).
(* Failed. *)
