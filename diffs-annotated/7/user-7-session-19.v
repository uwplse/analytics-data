Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_union__inv in Hm2).
(destruct Hm2; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; tauto).
(apply match_ty_i_ref__inv in Hm1).
(destruct Hm1 as [tx [Heqx Hrefx]]; inversion Heqx; subst).
(apply match_ty_i_ref__inv in Hm2).
(destruct Hm2 as [ty [Heqy Hrefy]]; inversion Heqy; subst).
(simpl).
(intros v; auto).
(* Failed. *)
