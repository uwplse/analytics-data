Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
(assert (Hv : value_type (TCName c)) by constructor; assert (Hm : |-[ 0] TCName c <$ TCName c) by (apply match_ty_i__reflexive; assumption);
  specialize (H 0 _ Hv); destruct H as [H _]; specialize (H Hm)).
(* Failed. *)
