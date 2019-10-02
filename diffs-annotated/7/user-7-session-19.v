Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(simpl).
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
clear IHk'.
(intros Htk Htk' v Hvk Hvk').
(simpl in Htk).
(* Failed. *)
