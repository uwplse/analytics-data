Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
(assert (Heq1 : | t1 | = | t'1 |)).
{
(apply IHt1).
(* Failed. *)
