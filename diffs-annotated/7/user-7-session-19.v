Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma match_ty_i_t_le_k__v_ke_t : forall (k : nat) (t : ty), | t | <= k -> forall v : ty, |-[ k] v <$ t -> | v | <= | t |.
Proof.
(induction k; induction t; intros Htk v Hm).
(* Failed. *)
