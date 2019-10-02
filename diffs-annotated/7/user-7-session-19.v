Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(destruct (max_inv_depth_le__components_le _ _ _ Htk) as [Htk1 Htk2]).
(apply match_ty_i_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst).
SearchPattern (Nat.max _ _ <= Nat.max _ _).
(simpl; apply Nat.max_le_compat).
(* Failed. *)
