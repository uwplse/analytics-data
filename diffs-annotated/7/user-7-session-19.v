Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(assert (Hmt : |-[ S k] TRef t <$ TRef t) by (simpl; tauto)).
(assert (Hmt' : |-[ S k] TRef t' <$ TRef t') by (simpl; tauto)).
(* Failed. *)
