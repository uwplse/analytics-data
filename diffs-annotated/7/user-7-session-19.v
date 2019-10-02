Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(destruct Hsemu as [Hsemu| Hsemu]; [ apply Nat.le_trans with (| t'1 |) | apply Nat.le_trans with (| t'2 |) ]).
(* Failed. *)
