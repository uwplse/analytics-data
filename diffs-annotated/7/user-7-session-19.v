Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
Show 3.
9: {
idtac.
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
}
Abort.
Lemma match_ty_i__inv_depth_stable :
  forall (k k' : nat) (t : ty),
  inv_depth t <= k -> inv_depth t <= k' -> forall v : ty, inv_depth v <= k -> inv_depth v <= k' -> |-[ k] v <$ t <-> |-[ k'] v <$ t.
Proof.
(induction k; induction k').
-
tauto.
-
admit.
-
admit.
-
(induction t).
admit.
admit.
admit.
+
clear IHk' IHt.
(intros Htk Htk' v Hvk Hvk').
(simpl in Htk, Htk').
(apply le_S_n in Htk).
(apply le_S_n in Htk').
(split; intros Hm; apply match_ty_i_ref__inv in Hm; destruct Hm as [t' [Heq Href]]; subst; simpl; intros v Hv; specialize (Href v Hv)).
(* Failed. *)
