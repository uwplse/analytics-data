Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(inversion Hle; subst).
+
(simpl).
(intros v Hv).
specialize (Href v Hv).
(split; tauto).
+
(simpl).
(intros v Hv).
