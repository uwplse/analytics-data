Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
tauto.
-
(apply match_ty_i_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(inversion Hle; subst).
+
(simpl).
(intros v Hv).
specialize (Href v Hv).
(split; tauto).
+
(destruct k').
tauto.
(* Failed. *)
