Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
exists (TRef t).
(split; intros v Hm; assert (Hmu : |-[ k] v <$ TUnion t1 t2) by (apply match_ty_i_union_1; assumption) || (apply match_ty_i_union_2; assumption);
  apply Hsem; assumption).
-
(assert (Hv : value_type (TCName c)) by constructor).
(pose proof (value_sem_sub_k_i_union__inv _ Hv _ _ _ H) as Hsemu).
(* Failed. *)
