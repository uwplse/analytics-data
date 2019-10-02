Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma match_ty_i__transitive_on_value_type :
  forall v1 v2 v3 : ty, value_type v2 -> forall k : nat, |-[ k] v1 <$ v2 -> |-[ k] v2 <$ v3 -> |-[ k] v1 <$ v3.
Proof.
(intros v1 v2 v3 Hv2).
generalize dependent v3.
generalize dependent v1.
(induction Hv2).
-
(intros v1 v3 k Hm1 Hm2).
(apply match_ty_i_cname__inv in Hm1; subst).
assumption.
-
(intros v0 v3 k Hm1 Hm2).
(apply match_ty_i_pair__inv in Hm1).
(destruct Hm1 as [pv11 [pv12 [Heq [Hm11 Hmpv12]]]]; subst).
(induction v3; try (solve [ destruct k; simpl in Hm2; contradiction ])).
+
(apply match_ty_i_pair__inv in Hm2).
(destruct Hm2 as [pv21 [pv22 [Heq [Hm21 Hm22]]]]).
(inversion Heq; subst).
auto using match_ty_pair.
(* Failed. *)
