Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(destruct Hmu as [Hmu1| Hmu2]; [ left | right ]; intros v Hv Hm; apply match_ty_i_ref__inv in Hm; destruct Hm as [t' [Heq Href]]; subst).
(* Failed. *)
