Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(assert (Hm : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; constructor)).
specialize (H _ Hm).
(apply match_ty_i_ref__inv in H).
(destruct H as [t' [Heq Href]]; subst).
(* Failed. *)
