Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(induction k; intros v Hv; induction Hv; intros ta tb Hsem).
6: {
idtac Abort.
(* Failed. *)
