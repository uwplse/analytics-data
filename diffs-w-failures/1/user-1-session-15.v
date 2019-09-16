From Coq Require Import List.
From Coq Require Import Omega.
Require Init.Nat.
From Classes Require Import Default.
Set Implicit Arguments.
Set Warnings "-undeclared-scope".
Section Array.
Context (A : Type).
Context {def : Default A}.
Notation list := (list A).
Implicit Types (l : list) (n : nat) (x : A).
Fixpoint assign l n x' : list :=
  match l with
  | nil => nil
  | x :: xs => match n with
               | 0 => x' :: xs
               | S n => x :: assign xs n x'
               end
  end.
Hint Extern 3 (_ < _) => omega: core.
Hint Extern 3 (_ >= _) => omega: core.
Hint Rewrite @eq_refl False using fail : solve_rewrite.
Ltac simplify := autorewrite with solve_rewrite in *.
Ltac solver := eauto; try omega; try congruence.
Ltac finish_solve := solve [ solver ].
Ltac
 induct l :=
  induction l; simpl; intros n; intros;
   [ simplify; solver
   | try (destruct n; simpl in *; simplify; [ finish_solve | solver ]) ].
Theorem length_assign l x' : forall n, length (assign l n x') = length l.
Proof.
(induct l).
Qed.
Theorem assign_oob l x : forall n, n >= length l -> assign l n x = l.
Proof.
(induct l).
(rewrite IHl by omega; auto).
Qed.
Theorem assign_assign_eq l x1 x2 :
  forall n, assign (assign l n x1) n x2 = assign l n x2.
Proof.
(induct l).
Qed.
Theorem assign_assign_ne l x1 x2 :
  forall n1 n2,
  n1 <> n2 -> assign (assign l n1 x1) n2 x2 = assign (assign l n2 x2) n1 x1.
Proof.
(induct l).
(destruct n, n2; simpl; try congruence).
(rewrite IHl by congruence; auto).
Qed.
Fixpoint index l n : option A :=
  match l with
  | nil => None
  | x :: xs => match n with
               | 0 => Some x
               | S n => index xs n
               end
  end.
Theorem index_assign_eq l :
  forall n x', n < length l -> index (assign l n x') n = Some x'.
Proof.
(induct l).
Qed.
Theorem index_assign_ne l :
  forall n1 n2 x', n1 <> n2 -> index (assign l n2 x') n1 = index l n1.
Proof.
(induct l).
-
generalize dependent n.
(induction n2; simpl; intros).
+
(destruct n; solver).
+
(destruct n; solver).
Qed.
Theorem index_oob l : forall n, n >= length l -> index l n = None.
Proof.
(induct l).
Qed.
Theorem index_not_none l : forall n, n < length l -> index l n <> None.
Proof.
(induct l).
Qed.
Theorem index_none_bound l n : index l n = None -> length l <= n.
Proof.
(intros).
(destruct (lt_dec n (length l)); try omega).
(exfalso; apply index_not_none in H; auto).
Qed.
Theorem index_some_bound l n x : index l n = Some x -> n < length l.
Proof.
(intros).
(destruct (lt_dec n (length l)); eauto).
(assert (index l n = None) by eauto using index_oob).
congruence.
Qed.
Theorem index_inbounds_exists l n :
  n < length l -> exists v, index l n = Some v.
Proof.
(intros).
(destruct_with_eqn index l n; eauto).
(apply index_none_bound in Heqo; omega).
Qed.
Theorem index_ext_eq l1 l2 : (forall n, index l1 n = index l2 n) -> l1 = l2.
Proof.
generalize dependent l2.
(induction l1; intros l2; intros).
-
(destruct l2; auto).
(specialize (H 0); simpl in *; congruence).
-
(destruct l2).
+
(specialize (H 0); simpl in *; congruence).
+
f_equal.
(specialize (H 0); simpl in *; congruence).
(apply IHl1; eauto; intros).
(specialize (H (S n)); simpl in *; auto).
Qed.
Theorem index_bound_ext_eq l1 l2 :
  length l1 = length l2 ->
  (forall n, n < length l1 -> n < length l2 -> index l1 n = index l2 n) ->
  l1 = l2.
Proof.
(intros).
(apply index_ext_eq; intros).
(destruct (lt_dec n (length l1)); auto).
(rewrite ?index_oob by auto; auto).
Qed.
Definition sel l n : A :=
  match index l n with
  | Some x => x
  | None => default
  end.
Ltac index_to_sel H := unfold sel; intros; try rewrite H; (solve [ auto ]).
Theorem sel_assign_eq l :
  forall n x', n < length l -> sel (assign l n x') n = x'.
Proof.
(index_to_sel index_assign_eq).
Qed.
Theorem sel_assign_ne l :
  forall n1 n2 x', n1 <> n2 -> sel (assign l n2 x') n1 = sel l n1.
Proof.
(index_to_sel index_assign_ne).
Qed.
Theorem index_inbounds l n : n < length l -> index l n = Some (sel l n).
Proof.
(unfold sel; intros).
(destruct_with_eqn index l n; eauto).
(apply index_none_bound in Heqo; omega).
Qed.
Theorem sel_index_eq l1 n1 l2 n2 :
  index l1 n1 = index l2 n2 -> sel l1 n1 = sel l2 n2.
Proof.
(index_to_sel H).
Qed.
Theorem index_sel_eq l1 n1 l2 n2 :
  n1 < length l1 ->
  n2 < length l2 -> sel l1 n1 = sel l2 n2 -> index l1 n1 = index l2 n2.
Proof.
(intros).
(rewrite ?index_inbounds by auto; congruence).
Qed.
Theorem sel_ext_eq l1 l2 :
  length l1 = length l2 ->
  (forall n, n < length l1 -> n < length l2 -> sel l1 n = sel l2 n) ->
  l1 = l2.
Proof.
(intros).
(apply index_bound_ext_eq; auto; intros).
(apply index_sel_eq; auto).
Qed.
Definition index_dec l n :
  {n < length l /\ index l n = Some (sel l n)} +
  {length l <= n /\ index l n = None}.
Proof.
(destruct (lt_dec n (length l)); [ left | right ]; split; try omega; auto
  using index_inbounds, index_oob).
Qed.
Definition subslice l n m : list := firstn m (skipn n l).
Ltac solve_lengths := autorewrite with length; auto; omega.
Lemma skipn_nil n : skipn n (@nil A) = nil.
Proof.
(destruct n; simpl; auto).
Qed.
Lemma skipn_length n : forall l, length (skipn n l) = length l - n.
Proof.
(induction n; simpl; intros; auto).
(rewrite <- minus_n_O; auto).
(destruct l; simpl; auto).
Qed.
Hint Rewrite firstn_nil skipn_nil : solve_rewrite.
Hint Rewrite firstn_length_le using solve_lengths : length.
Hint Rewrite skipn_length : length.
Theorem subslice_nil n m : subslice nil n m = @nil A.
Proof.
(unfold subslice).
(rewrite skipn_nil, firstn_nil; auto).
Qed.
Theorem length_subslice_general l n m :
  length (subslice l n m) = Nat.min m (length l - n).
Proof.
(unfold subslice).
(rewrite firstn_length).
(rewrite skipn_length).
auto.
Qed.
Theorem length_subslice l n m :
  n + m <= length l -> length (subslice l n m) = m.
Proof.
(unfold subslice; intros).
(autorewrite with length; auto).
Qed.
Theorem length_subslice_oob l n m :
  n + m >= length l -> length (subslice l n m) = length l - n.
Proof.
(rewrite length_subslice_general).
(intros).
(destruct (Nat.min_spec m (length l - n)); omega).
Qed.
Lemma index_firstn l : forall n i, i < n -> index (firstn n l) i = index l i.
Proof.
(induct l).
(destruct i; auto).
Qed.
Lemma index_firstn_oob l : forall n i, i >= n -> index (firstn n l) i = None.
Proof.
(induct l).
(destruct i; solver).
Qed.
Lemma index_skipn l : forall n i, index (skipn n l) i = index l (n + i).
Proof.
(induct l).
Qed.
Hint Rewrite index_oob using omega : array.
Hint Rewrite index_firstn using omega : array.
Hint Rewrite index_firstn_oob using omega : array.
Hint Rewrite index_skipn using omega : array.
Theorem subslice_index_ok l :
  forall n m i, i < m -> index (subslice l n m) i = index l (n + i).
Proof.
(unfold subslice; intros).
(autorewrite with array; auto).
Qed.
Theorem subslice_index_oob l :
  forall n m i, i >= m -> index (subslice l n m) i = None.
Proof.
(unfold subslice; intros).
(autorewrite with array; auto).
Qed.
Theorem subslice_index_oob_l l :
  forall n m i, n + i >= length l -> index (subslice l n m) i = None.
Proof.
(unfold subslice; intros).
(destruct (lt_dec i m); autorewrite with array; auto).
Qed.
Theorem subslice_sel_ok l :
  forall n m i, i < m -> sel (subslice l n m) i = sel l (n + i).
Proof.
(index_to_sel subslice_index_ok).
Qed.
Theorem subslice_index_conv l :
  forall n m i,
  i >= n -> i + n < m -> index l i = index (subslice l n m) (i - n).
Proof.
(intros).
(rewrite subslice_index_ok by omega).
(f_equal; omega).
Qed.
Theorem subslice_cons x xs n m : subslice (x :: xs) (S n) m = subslice xs n m.
Proof.
(unfold subslice; simpl).
reflexivity.
Qed.
Theorem subslice_at0 l m : subslice l 0 m = firstn m l.
Proof.
(unfold subslice; simpl; auto).
Qed.
Theorem firstn_oob l n : n >= length l -> firstn n l = l.
Proof.
generalize dependent l.
(induction n; simpl; intros).
-
(destruct l; simpl in *; auto).
(exfalso; omega).
-
(destruct l; simpl in *; auto).
(rewrite IHn by omega; auto).
Qed.
Theorem subslice_to_end l n m :
  n + m >= length l -> subslice l n m = skipn n l.
Proof.
(unfold subslice; intros).
(rewrite firstn_oob; auto).
(rewrite skipn_length; omega).
Qed.
Theorem subslice_whole l m : m >= length l -> subslice l 0 m = l.
Proof.
(intros).
(rewrite subslice_at0).
(rewrite firstn_oob; auto).
Qed.
Theorem subslice_one_more l :
  forall i n p,
  index l i = Some p ->
  S i + n <= length l -> subslice l i (S n) = p :: subslice l (S i) n.
Proof.
(induction l; simpl; intros).
-
congruence.
-
(rewrite subslice_cons).
(destruct i; simpl in *).
+
(inversion H; subst; clear H).
(rewrite subslice_at0 by omega).
(rewrite subslice_at0 by (simpl; omega)).
(simpl; auto).
+
(rewrite <- IHl; eauto; try omega).
Qed.
Theorem index_app_fst l1 :
  forall l2 i, i < length l1 -> index (l1 ++ l2) i = index l1 i.
Proof.
(induction l1; simpl; intros).
-
omega.
-
(destruct i; simpl; auto).
Qed.
Theorem index_app_snd l1 :
  forall l2 i,
  i >= length l1 -> index (l1 ++ l2) i = index l2 (i - length l1).
Proof.
(induction l1; simpl; intros).
-
(f_equal; omega).
-
(destruct i; simpl; try omega).
(apply IHl1; auto; omega).
Qed.
Theorem index_app_snd_off l1 :
  forall l2 i, index (l1 ++ l2) (length l1 + i) = index l2 i.
Proof.
(intros).
(rewrite index_app_snd by omega).
(f_equal; omega).
Qed.
Theorem subslice_select_array l1 l2 l3 n m :
  n = length l1 -> m = length l2 -> subslice (l1 ++ l2 ++ l3) n m = l2.
Proof.
(intros; subst).
(apply index_ext_eq; intros).
(destruct (lt_dec n (length l2))).
(rewrite subslice_index_ok by omega).
(rewrite index_app_snd_off).
(rewrite index_app_fst by omega).
auto.
(rewrite subslice_index_oob by omega).
(rewrite index_oob by omega).
auto.
Qed.
Theorem length_bounds l n : length l <= n -> length l >= n -> length l = n.
Proof.
omega.
Qed.
End Array.
Module ArrayNotations.
Delimit Scope array_scope with array.
Notation "l [ i  :=  v ]" := (assign l i v)
  (at level 10, left associativity) : array_scope.
Notation "l [ i ]" := (index l i) (at level 11, no associativity) :
  array_scope.
Notation "l [! i ]" := (sel l i) (at level 11, no associativity) :
  array_scope.
End ArrayNotations.
Arguments index_oob [A].
Arguments index_inbounds [A] {def}.
#[local]Ltac solve_bounds := auto; omega.
#[local]Ltac solve_lengths := autorewrite with length; solve_bounds.
Hint Rewrite length_assign : length.
Hint Rewrite length_subslice_oob using solve_lengths : length.
Hint Rewrite index_oob using solve_lengths : array.
Hint Rewrite index_assign_eq using solve_lengths : array.
Hint Rewrite index_assign_ne using solve_bounds : array.
Hint Rewrite sel_assign_eq using solve_lengths : array.
Hint Rewrite sel_assign_ne using solve_bounds : array.
Hint Rewrite assign_oob using solve_lengths : array.
Hint Rewrite assign_assign_eq : array.
Hint Rewrite index_app_fst using solve_lengths : array.
Hint Rewrite index_app_snd using solve_lengths : array.
Hint Rewrite index_app_snd_off : array.
Hint Rewrite subslice_index_ok using solve_bounds : array.
Hint Rewrite subslice_index_oob using solve_bounds : array.
Hint Rewrite subslice_index_oob_l using solve_lengths : array.
Hint Rewrite subslice_sel_ok using solve_bounds : array.
Hint Rewrite subslice_select_array using solve_lengths : array.
Ltac array := autorewrite with length array; auto.
