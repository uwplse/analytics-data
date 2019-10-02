Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(destruct Hsem; [ left | right ]; unfold sem_sub_k_i; intros v' Hm'; apply match_ty_i__transitive_on_value_type with v; assumption).
(pose proof (value_sem_sub_k_i_union__inv _ _ _ _ H)).
(* Failed. *)
