Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(assert (Hm : |-[ S k] TRef t <$ TRef t) by (simpl; tauto)).
specialize (H _ _ Hm).
(* Failed. *)
