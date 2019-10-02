Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(assert (Hvref : value_type (TRef t)) by constructor).
(assert (Hmref : |-[ S k] TRef t <$ TRef t) by (apply match_ty_i__reflexive; assumption)).
(pose proof (Hsem _ Hvref Hmref) as Hm).
(apply match_ty_i_union__inv in Hm).
(destruct Hm as [Hm1| Hm2]; [ left | right ]).
(* Failed. *)
