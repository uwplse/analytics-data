Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma match_ty_i_eq__inv_depth_eq : forall t t' : ty, (forall (k : nat) (v : ty), |-[ k] v <$ t <-> |-[ k] v <$ t') -> | t | = | t' |.
Proof.
(induction t; induction t'; H).
(* Failed. *)
