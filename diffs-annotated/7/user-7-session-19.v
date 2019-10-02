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
     | Hsem:||-[ ?k][?t]<= [?t']
       |- | ?t | <= | ?t' | =>
           assert (Hv : value_type t) by constructor; assert (Hm : |-[ k] t <$ t) by (apply match_ty_i__reflexive; assumption); specialize
            (Hsem _ Hm); contradiction
     | Hsem:||-[ ?k][?t]<= [TUnion ?t'1 ?t'2]
       |- | ?t | <= _ =>
           assert (Hv : value_type t) by constructor; pose proof (value_sem_sub_k_i_union__inv _ Hv _ _ _ Hsem) as Hsemu;
            destruct Hsemu as [Hsemu| Hsemu]; [ apply Nat.le_trans with (| t'1 |) | apply Nat.le_trans with (| t'2 |) ];
            tauto || apply Max.le_max_l || apply Max.le_max_r
     end ])).
-
(destruct (match_ty_i_exists t1) as [v1 Hm1]; destruct (match_ty_i_exists t2) as [v2 Hm2]).
(* Failed. *)
