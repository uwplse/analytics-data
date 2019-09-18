Time From Transitions Require Import RelationDefs Rewriting.
Time From Classes Require Import Classes.
Time Import RelationNotations.
Time
Fixpoint seq_rep_n {A T} (n : nat) (p : relation A A T) : 
relation A A T :=
  match n with
  | O => identity
  | S n' => p;; seq_rep_n n' p
  end.
Time
Fixpoint bind_rep_n {A T} (n : nat) (p : T -> relation A A T) 
(o : T) : relation A A T :=
  match n with
  | O => pure o
  | S n' => x <- p o; bind_rep_n n' p x
  end.
Time
Fixpoint bind_rep_r_n {A T} (n : nat) (p : T -> relation A A T) 
(o : T) : relation A A T :=
  match n with
  | O => pure o
  | S n' => x <- bind_rep_r_n n' p o; p x
  end.
Time
Lemma seq_star_inv_rep_n A T (p : relation A A T) 
  a1 a2 : seq_star p a1 a2 -> exists n, seq_rep_n n p a1 a2.
Time Proof.
Time (induction 1).
Time -
Time exists O.
Time (do 2 econstructor).
Time -
Time (destruct IHseq_star as (n, ?)).
Time exists (S n).
Time destruct_return.
Time *
Time (simpl).
Time econstructor.
Time (do 2 eexists; intuition eauto).
Time *
Time (simpl).
Time right.
Time (do 2 eexists; intuition eauto).
Time -
Time exists 1.
Time (econstructor; eauto).
Time Qed.
Time
Lemma bind_star_inv_rep_n A T (p : T -> relation A A T) 
  (o : T) a1 a2 : bind_star p o a1 a2 -> exists n, bind_rep_n n p o a1 a2.
Time Proof.
Time (induction 1).
Time -
Time (exists O; firstorder).
Time -
Time (destruct IHbind_star as (n, ?)).
Time exists (S n).
Time destruct_return.
Time *
Time (simpl).
Time (do 2 eexists; intuition eauto).
Time *
Time (simpl).
Time right.
Time (do 2 eexists; intuition eauto).
Time -
Time exists 1.
Time (econstructor; eauto).
Time Qed.
Time
Lemma bind_star_rep_n_to_bind_star A T (p : T -> relation A A T) 
  (o : T) a1 a2 n : bind_rep_n n p o a1 a2 -> bind_star p o a1 a2.
Time Proof.
Time revert o a1 a2.
Time (induction n; intros o a1 a2).
Time -
Time (simpl).
Time (inversion 1; subst).
Time (apply bind_star_pure).
Time -
Time (simpl).
Time destruct_return.
Time *
Time (intros (v, (a', (?, ?)))).
Time (econstructor; eauto).
Time *
Time (intros [?| (?, (?, (?, ?)))]).
Time **
Time (eapply bind_star_one_more_err; eauto).
Time **
Time (eapply bind_star_one_more_valid; eauto  10).
Time Qed.
Time
Lemma seq_star_rep_n_ind {A1} {A2} {T1} {T2} (p : relation A1 A2 T1) 
  q (r : relation A1 A2 T2) :
  (forall n, (p;; seq_rep_n n q) ---> r) -> (p;; seq_star q) ---> r.
Time Proof.
Time (intros).
Time (intros a1 a2 Hl).
Time destruct_return.
Time *
Time (destruct Hl as (t1, (a2', (Hp, Hstar)))).
Time (eapply seq_star_inv_rep_n in Hstar as (n, ?)).
Time (eapply H; do 2 eexists; intuition eauto).
Time *
Time (destruct Hl as [Hhd| (?, (?, (Hp, Hstar)))]).
Time **
Time (eapply (H O)).
Time (left; eauto).
Time **
Time (eapply seq_star_inv_rep_n in Hstar as (n, ?)).
Time (eapply H).
Time right.
Time eauto.
Time Qed.
Time
Lemma bind_star_rep_n_ind {A1} {A2} {T1} (p : relation A1 A2 T1) 
  q (r : relation A1 A2 T1) :
  (forall n, o <- p; bind_rep_n n q o ---> r) -> o <- p; bind_star q o ---> r.
Time Proof.
Time (intros).
Time (intros a1 a2 Hl).
Time destruct_return.
Time *
Time (destruct Hl as (t1, (a2', (Hp, Hstar)))).
Time (eapply bind_star_inv_rep_n in Hstar as (n, ?)).
Time (eapply H; do 2 eexists; intuition eauto).
Time *
Time (destruct Hl as [Hhd| (?, (?, (Hp, Hstar)))]).
Time **
Time (eapply (H O)).
Time (left; eauto).
Time **
Time (eapply bind_star_inv_rep_n in Hstar as (n, ?)).
Time (eapply H).
Time right.
Time eauto.
Time Qed.
Time
Theorem bind_rep_r_n_err_inv A T (r : T -> relation A A T) 
  n o a :
  bind_rep_r_n n r o a (@Err _ _) ->
  exists n' o' a',
    n' <= n /\ bind_rep_r_n n' r o a (Val a' o') /\ r o' a' (@Err _ _).
Time Proof.
Time (induction n).
Time -
Time (inversion 1).
Time -
Time (intros [Hleft| (o', (a', ?))]).
Time *
Time (edestruct IHn as (n', (o', (a', ?))); eauto).
Time exists n',o',a'.
Time intuition.
Time *
Time exists n,o',a'.
Time intuition.
Time Qed.
Time
Lemma seq_star_alt A T r (x : A) (y : Return A T) :
  seq_star r x y <-> (exists n, seq_rep_n n r x y).
Time Proof.
Time split.
Time -
Time (induction 1).
Time *
Time exists O.
Time (econstructor; eauto).
Time *
Time (destruct IHseq_star as (n, Hseq)).
Time exists (S n).
Time destruct_return.
Time **
Time (econstructor; eauto).
Time **
Time right.
Time eauto  10.
Time *
Time exists (S O).
Time (econstructor; eauto).
Time -
Time (intros (n, Hseq)).
Time revert x y Hseq.
Time (induction n; intros x y Hseq).
Time *
Time (inversion Hseq; subst; econstructor).
Time *
Time destruct_return.
Time **
Time (destruct Hseq as (t', (?, (?, ?)))).
Time (econstructor; eauto).
Time **
Time (destruct Hseq as [Hhd| (?, (?, (?, ?)))]).
Time ***
Time (eapply seq_star_one_more_err; eauto).
Time ***
Time (eapply seq_star_one_more_valid; eauto).
Time Qed.
Time
Lemma bind_rep_lr_n A T (r : T -> relation A A T) 
  o n : bind_rep_n n r o <---> bind_rep_r_n n r o.
Time Proof.
Time revert o.
Time (induction n; intros o).
Time {
Time reflexivity.
Time }
Time (simpl).
Time setoid_rewrite IHn.
Time clear.
Time (induction n).
Time -
Time (simpl).
Time rew bind_right_id.
Time -
Time (simpl).
Time rew<- IHn.
Time Qed.
Time
Lemma bind_rep_lr_n_val A T (r : T -> relation A A T) 
  o n a a' o' :
  bind_rep_n n r o a (Val a' o') <-> bind_rep_r_n n r o a (Val a' o').
Time Proof.
Time revert o a a' o'.
Time (induction n; intros o a a' o').
Time {
Time reflexivity.
Time }
Time split.
Time -
Time (intros (omid, (amid, (Hr, Hn)))).
Time (eapply IHn in Hn).
Time clear - Hr Hn.
Time revert o a amid omid a' o' Hr Hn.
Time (induction n; intros).
Time *
Time (inversion Hn; subst).
Time (do 2 eexists; split; eauto).
Time econstructor.
Time *
Time (destruct Hn as (omid'', (amid'', (?, ?)))).
Time (eapply IHn in H; eauto).
Time (do 2 eexists; split; eauto).
Time -
Time (intros (omid, (amid, (Hn, Hr)))).
Time (eapply IHn in Hn).
Time clear - Hr Hn.
Time revert o a amid omid a' o' Hr Hn.
Time (induction n; intros).
Time *
Time (inversion Hn; subst).
Time (do 2 eexists; split; eauto).
Time econstructor.
Time *
Time (destruct Hn as (omid'', (amid'', (?, ?)))).
Time (eapply IHn in H0; eauto).
Time (do 2 eexists; split; eauto).
Time Qed.
Time
Lemma bind_star_alt A T r (x : A) o (y : Return A T) :
  bind_star r o x y <-> (exists n, bind_rep_n n r o x y).
Time Proof.
Time split.
Time -
Time (induction 1).
Time *
Time exists O.
Time (econstructor; eauto).
Time *
Time (destruct IHbind_star as (n, Hseq)).
Time exists (S n).
Time destruct_return.
Time **
Time (econstructor; eauto).
Time **
Time right.
Time eauto  10.
Time *
Time exists (S O).
Time (econstructor; eauto).
Time -
Time (intros (n, Hseq)).
Time revert o x y Hseq.
Time (induction n; intros o x y Hseq).
Time *
Time (inversion Hseq; subst; econstructor).
Time *
Time destruct_return.
Time **
Time (destruct Hseq as (t', (?, (?, ?)))).
Time (eapply bind_star_one_more_valid; eauto).
Time **
Time (destruct Hseq as [Hhd| (?, (?, (?, ?)))]).
Time ***
Time (eapply bind_star_one_more_err; eauto).
Time ***
Time (eapply bind_star_one_more_valid; eauto).
Time Qed.
Time
Lemma seq_star_mid_invariant A (p : relation A A unit)
  (q : relation A A unit) P :
  (test P;; p) ---> (q;; test P) ->
  (q;; seq_star q) ---> q -> (q;; test P;; seq_star p) ---> (q;; test P).
Time Proof.
Time (intros Hinv Htrans).
Time setoid_rewrite  <- bind_assoc.
Time (apply seq_star_rep_n_ind).
Time (induction n).
Time -
Time (simpl).
Time (rewrite bind_assoc).
Time setoid_rewrite unit_identity.
Time setoid_rewrite bind_right_id_unit.
Time reflexivity.
Time -
Time (simpl).
Time setoid_rewrite bind_assoc.
Time setoid_rewrite  <- bind_assoc at 2.
Time setoid_rewrite Hinv.
Time setoid_rewrite IHn.
Time setoid_rewrite  <- bind_assoc.
Time setoid_rewrite  <- seq_star1 in Htrans.
Time setoid_rewrite  <- seq_star_none in Htrans.
Time setoid_rewrite unit_identity in Htrans.
Time setoid_rewrite bind_right_id_unit in Htrans.
Time rew Htrans.
Time Qed.
Time
Lemma any_seq_star_any A T : (@any A A T;; seq_star (@any A A T)) ---> any.
Time Proof.
Time (eapply seq_star_rep_n_ind).
Time (induction n; simpl).
Time -
Time firstorder.
Time -
Time setoid_rewrite IHn.
Time (apply any_idem).
Time Qed.
Time
Theorem bind_star_ind_r A B T1 (q x : relation A B T1)
  (p : T1 -> relation B B T1) :
  q + and_then x p ---> x -> and_then q (bind_star p) ---> x.
Time Proof.
Time (intros Himpl).
Time (assert (q ---> x) as ->).
Time {
Time rew<- Himpl.
Time Left.
Time }
Time (assert (Himpl' : and_then x p ---> x)).
Time {
Time setoid_rewrite  <- Himpl at 2.
Time Right.
Time }
Time (eapply bind_star_rep_n_ind).
Time (intros n).
Time (induction n).
Time -
Time (simpl).
Time rew bind_right_id.
Time -
Time (simpl).
Time setoid_rewrite  <- bind_assoc.
Time rew Himpl'.
Time eauto.
Time Qed.
Time
Theorem bind_star_ind_r_pure A T1 t (x : relation A A T1)
  (p : T1 -> relation A A T1) :
  pure t + and_then x p ---> x -> bind_star p t ---> x.
Time Proof.
Time specialize (@bind_star_ind_r A A _ (pure t) x p).
Time (setoid_rewrite bind_left_id; auto).
Time Qed.
Time
Theorem simulation_seq A B (p : relation A B unit) 
  (q : relation B B unit) (r : relation A A unit) :
  (p;; q) ---> (r;; p) -> (p;; seq_star q) ---> (seq_star r;; p).
Time Proof.
Time (intros Hconv).
Time (apply seq_star_rep_n_ind).
Time (intros n).
Time (induction n).
Time (simpl).
Time -
Time setoid_rewrite  <- seq_star_none.
Time rew unit_identity.
Time rew bind_right_id_unit.
Time -
Time (simpl).
Time setoid_rewrite  <- bind_assoc.
Time rew Hconv.
Time rew IHn.
Time setoid_rewrite  <- bind_assoc.
Time (setoid_rewrite seq_star_fold; reflexivity).
Time Qed.
Time
Theorem simulation_seq_value A B T (_ : Default T) 
  (p : relation A B unit) (q : relation B B T) (r : relation A A T) :
  (p;; q) ---> v <- r; p;; pure v ->
  (p;; seq_star q) ---> v <- seq_star r; p;; pure v.
Time Proof.
Time (intros Hconv).
Time (apply seq_star_rep_n_ind).
Time (intros n).
Time (induction n).
Time (simpl).
Time -
Time setoid_rewrite  <- seq_star_none.
Time (intros a1 a2).
Time destruct_return.
Time *
Time (intros ([], (?, (?, ?)))).
Time right.
Time (do 2 eexists; split; eauto).
Time (econstructor; eauto).
Time (do 2 eexists; split; eauto).
Time (inversion H0; subst).
Time (inversion H1; subst).
Time (econstructor; eauto).
Time *
Time (intros [?| ([], (?, (?, ?)))]).
Time **
Time left.
Time right.
Time (unshelve (do 2 eexists; split; eauto; econstructor; eauto); eauto).
Time **
Time (inversion H0; congruence).
Time -
Time (simpl).
Time setoid_rewrite  <- bind_assoc.
Time rew Hconv.
Time rew IHn.
Time setoid_rewrite  <- bind_assoc.
Time (setoid_rewrite seq_star_fold; reflexivity).
Time Qed.
Time
Theorem simulation_seq_value_no_err A B T (p : relation A B unit)
  (q : relation B B T) (r : relation A A T) :
  (forall a, p a (Err _ _) -> False) ->
  (p;; q) ---> v <- r; p;; pure v ->
  (p;; seq_star q) ---> v <- seq_star r; p;; pure v.
Time Proof.
Time (intros Herr Hconv).
Time (apply seq_star_rep_n_ind).
Time (intros n).
Time (induction n).
Time (simpl).
Time -
Time setoid_rewrite  <- seq_star_none.
Time (intros a1 a2).
Time destruct_return.
Time *
Time (intros ([], (?, (?, ?)))).
Time right.
Time (do 2 eexists; split; eauto).
Time (econstructor; eauto).
Time (do 2 eexists; split; eauto).
Time (inversion H0; subst).
Time (inversion H1; subst).
Time (econstructor; eauto).
Time *
Time (intros [?| ([], (?, (?, ?)))]).
Time **
Time (exfalso; eauto).
Time **
Time (inversion H0; congruence).
Time -
Time (simpl).
Time setoid_rewrite  <- bind_assoc.
Time rew Hconv.
Time rew IHn.
Time setoid_rewrite  <- bind_assoc.
Time (setoid_rewrite seq_star_fold; reflexivity).
Time Qed.
Time
Theorem bind_pure_no_err A B C T (p : relation A B T) 
  (f : T -> C) a : (x <- p; pure (f x)) a (@Err _ _) -> p a (@Err _ _).
Time Proof.
Time (eapply bind_with_no_err; intros; eapply pure_no_err; eauto).
Time Qed.
Time
Lemma fst_lift_non_err {A1} {A2} {B} {T} (r : relation A1 A2 T) 
  s (b : B) : ~ r s (@Err _ _) -> ~ fst_lift r (s, b) (@Err _ _).
Time Proof.
Time intuition.
Time Qed.
Time
Lemma snd_lift_non_err {A1} {A2} {B} {T} (r : relation A1 A2 T) 
  s (b : B) : ~ r s (@Err _ _) -> ~ snd_lift r (b, s) (@Err _ _).
Time Proof.
Time intuition.
Time Qed.
