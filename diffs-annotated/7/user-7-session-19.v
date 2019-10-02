Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
exists (TRef t).
(assert (Hmp : |-[ k] TPair v v' <$ TPair t1 t2) by (apply match_ty_i_pair__inv; assumption)).
(* Failed. *)
