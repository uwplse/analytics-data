Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(induction k; induction t; intros Htk v Hm;
  try match goal with
      | Hm:|-[ ?k'] ?v <$ TCName _ |- _ => apply match_ty_i_cname__inv in Hm; subst; constructor
      end).
(destruct (max_inv_depth_le__components_le _ _ Htk) as [Htk1 Htk2]).
(* Failed. *)
