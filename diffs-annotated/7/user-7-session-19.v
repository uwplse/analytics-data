Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
(match goal with
 | |- | ?t1 | = | ?t2 | =>
       assert (Hv : value_type t1) by constructor; assert (Hm : |-[ 0] t1 <$ t1) by (apply match_ty_i__reflexive; assumption); specialize
        (H 0 _ Hv); destruct H as [H _]; specialize (H Hm); contradiction
 end).
(* Failed. *)
