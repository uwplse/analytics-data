Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
2: {
idtac.
clear IHt'1 IHt'2.
(simpl).
(apply f_equals).
(* Failed. *)
