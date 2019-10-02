Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(assert (Hv : value_type (TRef t)) by constructor).
(assert (Hm : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; constructor)).
(* Failed. *)
