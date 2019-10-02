Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
exists (TRef t).
(split; intros v Hm; assert (Hmu : |-[ k] v <$ TUnion t1 t2) by (apply match_ty_i_union_1; assumption) || (apply match_ty_i_union_2; assumption);
  apply Hsem; assumption).
Lemma sem_sub_k_i_nf__inv_depth_le : forall (k : nat) (t t' : ty), InNF( t) -> ||-[ k][t]<= [t'] -> | t | <= | t' |.
Proof.
(induction k; induction t; induction t'; intros Hnft Hsem; try (solve [ simpl; constructor ])).
(* Failed. *)
