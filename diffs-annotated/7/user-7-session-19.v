Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
(induction k; intros v Hv; induction Hv; intros ta tb Hsem; unfold sem_sub_k_i in Hsem).
(try
  match goal with
  | Hsem:forall v, value_type v -> |-[ ?k] v <$ TCName ?c -> _
    |- _ =>
        assert (Hvv : value_type (TCName c)) by constructor; assert (Hmv : |-[ k] TCName c <$ TCName c) by reflexivity; specialize (Hsem _ Hv Hm)
  end).
(* Failed. *)
