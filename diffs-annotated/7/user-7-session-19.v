Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma match_ty_i__value_type : forall (k : nat) (v t : ty), |-[ k] v <$ t -> value_type v.
Proof.
(* Failed. *)
