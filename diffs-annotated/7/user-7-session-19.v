Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma aaa : forall (k : nat) (t t' : ty), forall v : ty, |-[ k] v <$ t -> |-[ k] v <$ t' -> | t | <= | t' |.
(* Failed. *)
