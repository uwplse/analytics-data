Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
(destruct Hmu as [Hmu1| Hmu2]; [ left | right ]; intros v Hv Hm; apply match_ty_i_ref__inv in Hm; destruct Hm as [t' [Heq Href]]; subst).
(* Failed. *)
