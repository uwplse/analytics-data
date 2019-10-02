Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma match_ty_i_eq__inv_depth_eq :
  forall t t' : ty, (forall (k : nat) (v : ty), value_type v -> |-[ k] v <$ t <-> |-[ k] v <$ t') -> | t | = | t' |.
Proof.
(induction t; induction t'; intros H).
reflexivity.
15: {
idtac.
clear IHt'.
(simpl).
(apply f_equal).
(apply IHt).
(intros k v).
(assert (Hmt : |-[ S k] TRef t <$ TRef t) by (simpl; tauto)).
specialize (H (S k) (TRef t)).
(destruct H as [H _]).
(* Failed. *)
