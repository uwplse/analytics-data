Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma match_ty_i_t_le_k__v_ke_t : forall (k : nat) (t : ty), | t | <= k -> forall v : ty, |-[ k] v <$ t -> | v | <= | t |.
Proof.
(induction k; induction t; intros Htk v Hm;
  try
   match goal with
   | Hm:|-[ ?k'] ?v <$ TCName _ |- _ => apply match_ty_i_cname__inv in Hm; subst; constructor
   | H:|-[ ?k'] ?v <$ TPair _ _
     |- _ =>
         destruct (max_inv_depth_le__components_le _ _ _ Htk) as [Htk1 Htk2]; apply match_ty_i_pair__inv in Hm;
          destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; apply Nat.max_le_compat; auto
   | H:|-[ ?k'] ?v <$ TUnion _ _
     |- _ =>
         destruct (max_inv_depth_le__components_le _ _ _ Htk) as [Htk1 Htk2]; apply match_ty_i_union__inv in Hm; destruct Hm as [Hm1| Hm2];
          [ apply Nat.le_trans with (| t1 |) | apply Nat.le_trans with (| t2 |) ]; auto; apply Max.le_max_l || apply Max.le_max_r
   end).
-
(destruct v; try contradiction).
(inversion Htk).
-
clear IHt.
(simpl in Htk).
(apply le_S_n in Htk).
(apply match_ty_i_ref__inv in Hm).
(destruct Hm as [t' [Heq Href]]; subst).
(* Failed. *)
