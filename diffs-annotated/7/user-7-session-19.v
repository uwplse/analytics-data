Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
(induction t; induction t'; intros H).
reflexivity.
15: {
idtac.
clear IHt'.
(simpl).
(apply f_equal).
(eapply IHt).
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
Abort.
Lemma value_sem_sub_i_union__inv : forall v : ty, value_type v -> forall ta tb : ty, ||- [v]<= [TUnion ta tb] -> ||- [v]<= [ta] \/ ||- [v]<= [tb].
Proof.
(intros v Hv; induction Hv).
-
Abort.
Close Scope btjmi_scope.
Open Scope btjmdeq_scope.
Lemma match_ty_deq_cname__inv : forall (v : ty) (c : cname), forall k : nat, |-[ k] v <$ TCName c -> v = TCName c.
Proof.
(intros v; induction v; try (solve [ intros c k Hm; destruct k; simpl in Hm; contradiction ])).
(intros c0 k Hm).
(destruct k; simpl in Hm; subst; reflexivity).
Qed.
Lemma match_ty_deq_pair__inv :
  forall v t1 t2 : ty, forall k : nat, |-[ k] v <$ TPair t1 t2 -> exists v1 v2 : ty, v = TPair v1 v2 /\ |-[ k] v1 <$ t1 /\ |-[ k] v2 <$ t2.
Proof.
(intros v; induction v; try (solve [ intros t1 t2 k Hm; destruct k; simpl in Hm; contradiction ])).
(intros t1 t2 k Hm).
exists v1,v2.
(split; try reflexivity).
(destruct k; simpl in Hm; assumption).
Qed.
Lemma match_ty_deq_union__inv : forall v t1 t2 : ty, forall k : nat, |-[ k] v <$ TUnion t1 t2 -> |-[ k] v <$ t1 \/ |-[ k] v <$ t2.
Proof.
(intros v t1 t2 k Hm).
(destruct k; destruct v; assumption).
Qed.
Lemma match_ty_deq_ref__inv :
  forall v t : ty,
  forall k : nat,
  |-[ S k] v <$ TRef t ->
  exists t' : ty,
    v = TRef t' /\ inv_depth t <= k /\ inv_depth t' = inv_depth t /\ (forall v' : ty, value_type v' -> |-[ k] v' <$ t' <-> |-[ k] v' <$ t).
Proof.
(intros v; induction v; try (solve [ intros t k Hm; destruct k; simpl in Hm; contradiction ])).
clear IHv.
(intros t k).
(intros Hm).
(simpl in Hm).
(destruct Hm as [Hdept [Hdepv Href]]).
exists v.
split.
reflexivity.
split.
assumption.
split.
assumption.
(intros v' Hv').
specialize (Href v' Hv').
(destruct Href; split; assumption).
Qed.
Close Scope btjmdeq_scope.
Theorem sem_sub_i__sem_sub_deq : forall t1 t2 : ty, (||- [t1]<= [t2])%btjmi -> (||- [t1]<= [t2])%btjmdeq.
Proof.
(intros ta; induction ta; intros tb; induction tb; intros Hsem; pose proof Hsem as Hsem'; unfold sem_sub_i, sem_sub_k_i in Hsem';
  unfold sem_sub_deq, sem_sub_k_deq; intros k v Hv Hm1;
  try
   match goal with
   | Hm1:(|-[ ?k] ?v <$ TCName ?c)%btjmdeq
     |- _ =>
         apply match_ty_deq_cname__inv in Hm1; subst; assert (Hm : (|-[ k] TCName c <$ TCName c)%btjmi) by (destruct k; reflexivity); specialize
          (Hsem' _ _ Hv Hm)
   end).
-
(apply match_ty_i_cname__inv in Hsem').
(inversion Hsem').
(destruct k; reflexivity).
-
(apply match_ty_i_pair__inv in Hsem').
(destruct Hsem' as [v1 [v2 [Heq _]]]).
(inversion Heq).
-
Abort.
(* Failed. *)
