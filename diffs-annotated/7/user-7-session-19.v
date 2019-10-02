Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(induction k; induction t; induction t'; intros v Hmt Hmt').
Show 2.
32: {
idtac.
(simpl).
(apply le_n_S).
(apply IHk).
(* Failed. *)
