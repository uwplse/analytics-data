Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(apply match_ty_i_pair; auto).
(split; intros Hm; apply match_ty_i_ref__inv in Hm; destruct Hm as [t' [Heq Href]]; subst; simpl; intros v Hv; specialize (Href v Hv);
  simpl in Hvk, Hvk'; apply le_S_n in Hvk; apply le_S_n in Hvk').
(* Failed. *)
