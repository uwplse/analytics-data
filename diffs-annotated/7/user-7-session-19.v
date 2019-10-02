Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
specialize (H (S k) (TRef t)).
(destruct H as [H _]).
specialize (H Hmt).
(apply match_ty_i_ref__inv in H).
(destruct H as [tx [Heq Href]]).
(inversion Heq; subst).
tauto.
(* Failed. *)
