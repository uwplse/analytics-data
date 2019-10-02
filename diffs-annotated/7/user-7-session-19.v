Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(induction k; induction t; induction t'; intros H; try (solve [ simpl; constructor ]);
  try (solve
   [ match goal with
     | |- | ?t1 | <= | ?t2 | =>
           (assert (Hv : value_type t1) by constructor; assert (Hm : |-[ 0] t1 <$ t1) by (apply match_ty_i__reflexive; assumption); specialize
             (H _ Hm); contradiction) ||
             (assert (Hv : value_type t2) by constructor; assert (Hm : |-[ 0] t2 <$ t2) by (apply match_ty_i__reflexive; assumption); specialize
               (H _ Hm); contradiction)
     end ])).
(* Failed. *)
