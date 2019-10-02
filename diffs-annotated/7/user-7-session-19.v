Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
(induction k; intros v Hv; induction Hv; intros ta tb Hsem; unfold sem_sub_k_i in Hsem;
  try
   match goal with
   | Hsem:forall v, value_type v -> |-[ ?k] v <$ TCName ?c -> _
     |- _ =>
         assert (Hvv : value_type (TCName c)) by constructor;
          assert (Hmv : |-[ k] TCName c <$ TCName c) by (apply match_ty_i__reflexive; assumption); specialize (Hsem _ Hvv Hmv);
          apply match_ty_i_union__inv in Hsem; destruct Hsem; [ left | right ]; unfold sem_sub_k_i; intros v' Hv' Hm';
          apply match_ty_i_cname__inv in Hm'; subst; assumption
   | Hsem:forall v, value_type v -> |-[ ?k] v <$ TPair ?v1 ?v2 -> _ |- _ => assert (Hvv : value_type (TPair v1 v2)) by (constructor; assumption)
   end).
(* Failed. *)
