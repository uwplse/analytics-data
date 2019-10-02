Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(destruct (max_inv_depth_le__components_le _ _ _ Htk) as [Htk1 Htk2]).
(apply Nat.max_le_compat; auto).
(* Failed. *)
