Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
exists (TRef t).
(split; intros v Hm; [ pose proof (match_ty_i_exists t2 k) | pose proof (match_ty_i_exists t1 k) ]).
(* Failed. *)
