Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(pose proof (Hsem _ Hv Hm) as Hmu).
(destruct Hmu as [Hmu1| Hmu2]; [ left | right ]).
(* Failed. *)
