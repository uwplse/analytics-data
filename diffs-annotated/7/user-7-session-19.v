Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma bbb : forall (k : nat) (t t' v : ty), (|-[ k] v <$ t -> |-[ k] v <$ t') -> | t | <= | t' |.
Proof.
(induction k; induction t; induction t'; intros v H).
32: {
idtac.
(simpl).
(apply le_n_S).
(apply IHk).
(* Failed. *)
