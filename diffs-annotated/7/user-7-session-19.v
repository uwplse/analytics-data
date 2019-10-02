Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma value_sem_sub_k_union__value_sem_sub_k_component :
  forall k : nat, forall v : ty, value_type v -> forall ta tb : ty, ||-[ k][v]<= [TUnion ta tb] -> ||-[ k][v]<= [ta] \/ ||-[ k][v]<= [tb].
Proof.
(induction k; intros v Hv; induction Hv; intros Hsem).
(* Failed. *)
