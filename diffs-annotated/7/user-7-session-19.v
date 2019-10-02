Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma aaa : forall (k : nat) (t t' : ty), (forall v : ty, |-[ k] v <$ t -> |-[ k] v <$ t') -> | t | <= | t' |.
Proof.
(induction k; induction t; induction t'; intros H).
32: {
idtac.
(simpl).
(apply le_n_S).
(apply IHk).
(assert (Hv : value_type (TRef t)) by (apply match_ty_i__reflexive; constructor)).
(* Failed. *)
