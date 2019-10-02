Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
(intros v Hv k ta tb Hsem; unfold sem_sub_k_i in Hsem).
(assert (Hmv : |-[ k] v <$ v) by (apply match_ty_i__reflexive; assumption)).
(* Failed. *)
