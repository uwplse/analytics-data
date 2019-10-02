Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(match goal with
 | |- | ?t1 | <= | ?t2 | =>
       assert (Hv : value_type t1) by constructor; assert (Hm : |-[ 0] t1 <$ t1) by (apply match_ty_i__reflexive; assumption); specialize (H _ Hm);
        apply match_ty_i_union__inv in H; rewrite inv_depth_union; destruct H as [Hm1| Hm2];
        [ apply Nat.le_trans with (| t'1 |) | apply Nat.le_trans with (| t'2 |) ]; try apply Max.le_max_l || apply Max.le_max_r
 end).
(* Failed. *)
