Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Lemma match_ty_i_k__match_le_k : forall (k : nat) (v t : ty), |-[ k] v <$ t -> forall k' : nat, k' <= k -> |-[ k'] v <$ t.
Proof.
(induction k; intros v t; generalize dependent v; induction t; intros v Hm k' Hlt Hle;
  try
   match goal with
   | |- |-[ ?k'] ?v <$ TCName _ => apply match_ty_i_cname__inv in Hm; subst; destruct k'; reflexivity
   | |- |-[ ?k'] ?v <$ TPair _ _ => apply match_ty_i_pair__inv in Hm; destruct Hm as [v1 [v2 [Heq [Hm1 Hm2]]]]; subst; apply match_ty_i_pair; auto
   | |- |-[ ?k'] ?v <$ TUnion _ _ =>
         apply match_ty_i_union__inv in Hm; destruct Hm as [Hm1| Hm2]; [ apply match_ty_i_union_1 | apply match_ty_i_union_2 ]; auto
   end).
