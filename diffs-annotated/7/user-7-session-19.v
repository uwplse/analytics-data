Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(pose proof (value_sem_sub_k_i_union__inv _ Hv _ _ _ H) as Hsemu).
(destruct Hsemu as [Hsemu1| Hsemu2]).
(* Failed. *)
