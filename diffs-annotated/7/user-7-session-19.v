Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
-
(assert (IH1 : forall (k : nat) (v : ty), value_type v -> |-[ k] v <$ TCName c <-> |-[ k] v <$ t'1)).
{
(intros k v Hv).
specialize (H k v Hv).
(destruct H as [H1 H2]).
(split; intros Hm).
(* Failed. *)
