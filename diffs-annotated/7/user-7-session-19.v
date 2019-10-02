Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
exists (TRef t).
(split; intros v Hm; assert (Hmu : |-[ k] v <$ TUnion t1 t2) by (apply match_ty_i_union_1; assumption) || (apply match_ty_i_union_2; assumption);
  apply Hsem; assumption).
(induction k; induction t; induction t'; intros Hnft Hsem; try (solve [ simpl; constructor ]);
  try (solve
   [ match goal with
     | Hsem:||-[ ?k][?t1]<= [?t2]
       |- | ?t1 | <= | ?t2 | =>
           assert (Hv : value_type t1) by constructor; assert (Hm : |-[ k] t1 <$ t1) by (apply match_ty_i__reflexive; assumption); specialize
            (Hsem _ Hm); contradiction
     end ])).
(assert (Hv : value_type (TCName c)) by constructor).
(* Failed. *)
