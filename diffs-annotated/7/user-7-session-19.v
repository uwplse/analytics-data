Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
clear IHt'.
(simpl).
(apply f_equal).
(apply IHt).
(intros k v Hv).
(assert (Hmt : |-[ S k] TRef t <$ TRef t) by (simpl; tauto)).
specialize (H (S k) (TRef t)).
(destruct H as [H _]).
constructor.
specialize (H Hmt).
(apply match_ty_i_ref__inv in H).
(destruct H as [tx [Heq Href]]).
(inversion Heq; subst).
auto.
(* Failed. *)
