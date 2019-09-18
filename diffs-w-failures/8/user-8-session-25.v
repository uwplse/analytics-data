Require Export Prelim.
Require Export Monoid.
Open Scope list_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation " W1 \226\138\151 W2 " := (Tensor W1 W2) (at level 40, left associativity) :
  circ_scope.
Open Scope circ_scope.
Fixpoint size_wtype (W : WType) : nat :=
  match W with
  | One => 0
  | Qubit => 1
  | Bit => 1
  | W1 \226\138\151 W2 => size_wtype W1 + size_wtype W2
  end.
Fixpoint interpret (w : WType) : Set :=
  match w with
  | Qubit => bool
  | Bit => bool
  | One => unit
  | w1 \226\138\151 w2 => interpret w1 * interpret w2
  end.
Fixpoint NTensor (n : nat) (W : WType) :=
  match n with
  | 0 => One
  | S n' => W \226\138\151 NTensor n' W
  end.
Infix "\226\168\130" := NTensor (at level 30) : circ_scope.
Lemma size_ntensor : forall n W, size_wtype (n \226\168\130 W) = (n * size_wtype W)%nat.
Proof.
(intros n W).
(induction n; trivial).
(simpl).
(rewrite IHn).
reflexivity.
Qed.
Definition Var := nat.
Definition Ctx := list (option WType).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma ctx_octx : forall \206\147 \206\147', Valid \206\147 = Valid \206\147' <-> \206\147 = \206\147'.
Proof.
(intuition; congruence).
Defined.
Fixpoint size_ctx (\206\147 : Ctx) : nat :=
  match \206\147 with
  | [] => 0
  | None :: \206\147' => size_ctx \206\147'
  | Some _ :: \206\147' => S (size_ctx \206\147')
  end.
Definition size_octx (\206\147 : OCtx) : nat :=
  match \206\147 with
  | Invalid => 0
  | Valid \206\147' => size_ctx \206\147'
  end.
Lemma size_ctx_size_octx : forall \206\147 : Ctx, size_ctx \206\147 = size_octx (Valid \206\147).
Proof.
easy.
Qed.
Lemma size_ctx_app :
  forall \206\1471 \206\1472 : Ctx, size_ctx (\206\1471 ++ \206\1472) = (size_ctx \206\1471 + size_ctx \206\1472)%nat.
Proof.
(induction \206\1471; intros; simpl; auto).
(destruct a; trivial).
(rewrite IH\206\1471; easy).
Qed.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma Singleton_size : forall x w \206\147, SingletonCtx x w \206\147 -> size_ctx \206\147 = 1%nat.
Proof.
(induction 1; auto).
Qed.
Fixpoint singleton (x : Var) (W : WType) : Ctx :=
  match x with
  | O => [Some W]
  | S x => None :: singleton x W
  end.
Lemma singleton_singleton : forall x W, SingletonCtx x W (singleton x W).
Proof.
(induction x; intros W).
-
constructor.
-
(simpl).
constructor.
(apply IHx).
Defined.
Lemma singleton_equiv : forall x W \206\147, SingletonCtx x W \206\147 -> \206\147 = singleton x W.
Proof.
(induction 1; trivial).
(simpl).
(rewrite IHSingletonCtx).
reflexivity.
Defined.
Lemma singleton_size : forall x w, size_ctx (singleton x w) = 1%nat.
Proof.
(induction x; auto).
Qed.
Definition merge_wire (o1 o2 : option WType) : OCtx :=
  match o1, o2 with
  | None, o2 => Valid [o2]
  | Some w1, None => Valid [Some w1]
  | _, _ => Invalid
  end.
Fixpoint merge' (\206\1471 \206\1472 : Ctx) : OCtx :=
  match \206\1471, \206\1472 with
  | [], _ => Valid \206\1472
  | _, [] => Valid \206\1471
  | o1 :: \206\1471', o2 :: \206\1472' =>
      match merge_wire o1 o2 with
      | Invalid => Invalid
      | Valid \206\1470 =>
          match merge' \206\1471' \206\1472' with
          | Invalid => Invalid
          | Valid \206\147' => Valid (\206\1470 ++ \206\147')
          end
      end
  end.
Definition merge (\206\1471 \206\1472 : OCtx) : OCtx :=
  match \206\1471, \206\1472 with
  | Valid \206\1471', Valid \206\1472' => merge' \206\1471' \206\1472'
  | _, _ => Invalid
  end.
Lemma merge_shadow :
  merge =
  (fun \206\1471 \206\1472 =>
   match \206\1471 with
   | Invalid => Invalid
   | Valid \206\1471' =>
       match \206\1472 with
       | Invalid => Invalid
       | Valid \206\1472' => merge' \206\1471' \206\1472'
       end
   end).
Proof.
reflexivity.
Qed.
Ltac unlock_merge := rewrite merge_shadow in *.
Notation "\226\136\133" := (Valid []).
Infix "\226\139\147" := merge (left associativity, at level 50).
Coercion Valid : Ctx >-> OCtx.
Lemma merge_merge' : forall \206\1471 \206\1472 : Ctx, \206\1471 \226\139\147 \206\1472 = merge' \206\1471 \206\1472.
Proof.
reflexivity.
Defined.
Lemma merge_cancel_l : forall \206\147 \206\1471 \206\1472, \206\1471 = \206\1472 -> \206\147 \226\139\147 \206\1471 = \206\147 \226\139\147 \206\1472.
Proof.
(intros; subst; reflexivity).
Defined.
Lemma merge_cancel_r : forall \206\147 \206\1471 \206\1472, \206\1471 = \206\1472 -> \206\1471 \226\139\147 \206\147 = \206\1472 \226\139\147 \206\147.
Proof.
(intros; subst; reflexivity).
Defined.
Lemma merge_I_l : forall \206\147, Invalid \226\139\147 \206\147 = Invalid.
Proof.
reflexivity.
Defined.
Lemma merge_I_r : forall \206\147, \206\147 \226\139\147 Invalid = Invalid.
Proof.
(destruct \206\147; reflexivity).
Defined.
Lemma merge_valid :
  forall (\206\1471 \206\1472 : OCtx) (\206\147 : Ctx),
  \206\1471 \226\139\147 \206\1472 = Valid \206\147 ->
  {\206\1471' : Ctx & \206\1471 = Valid \206\1471'} * {\206\1472' : Ctx & \206\1472 = Valid \206\1472'}.
Proof.
(intros \206\1471 \206\1472 \206\147 M).
(destruct \206\1471 as [| \206\1471'], \206\1472 as [| \206\1472']; inversion M).
eauto.
Defined.
Lemma merge_invalid_iff :
  forall (o1 o2 : option WType) (\206\1471 \206\1472 : Ctx),
  Valid (o1 :: \206\1471) \226\139\147 Valid (o2 :: \206\1472) = Invalid <->
  merge_wire o1 o2 = Invalid \/ \206\1471 \226\139\147 \206\1472 = Invalid.
Proof.
(intros o1 o2 \206\1471 \206\1472).
split.
+
(intros H).
(destruct o1, o2; auto; right; simpl in H).
-
(rewrite <- merge_merge' in H).
(destruct (\206\1471 \226\139\147 \206\1472); trivial).
(inversion H).
-
(rewrite <- merge_merge' in H).
(destruct (\206\1471 \226\139\147 \206\1472); trivial).
(inversion H).
-
(rewrite <- merge_merge' in H).
(destruct (\206\1471 \226\139\147 \206\1472); trivial).
(inversion H).
+
(intros H).
(inversion H).
(simpl).
(rewrite H0; reflexivity).
(simpl).
(destruct (merge_wire o1 o2); trivial).
(rewrite merge_merge' in H0).
(rewrite H0).
reflexivity.
Defined.
Lemma merge_nil_l : forall \206\147, \226\136\133 \226\139\147 \206\147 = \206\147.
Proof.
(destruct \206\147; reflexivity).
Defined.
Lemma merge_nil_r : forall \206\147, \206\147 \226\139\147 \226\136\133 = \206\147.
Proof.
(destruct \206\147; trivial).
(destruct c; trivial).
Defined.
Lemma merge_comm : forall \206\1471 \206\1472, \206\1471 \226\139\147 \206\1472 = \206\1472 \226\139\147 \206\1471.
Proof.
(intros \206\1471 \206\1472).
(destruct \206\1471 as [| \206\1471], \206\1472 as [| \206\1472]; trivial).
generalize dependent \206\1472.
(induction \206\1471).
+
(destruct \206\1472; trivial).
+
(destruct \206\1472; trivial).
(simpl).
(unfold merge in IH\206\1471).
(rewrite IH\206\1471).
(destruct a, o; reflexivity).
Defined.
Lemma merge_assoc : forall \206\1471 \206\1472 \206\1473, \206\1471 \226\139\147 (\206\1472 \226\139\147 \206\1473) = \206\1471 \226\139\147 \206\1472 \226\139\147 \206\1473.
Proof.
(intros \206\1471 \206\1472 \206\1473).
(destruct \206\1471 as [| \206\1471], \206\1472 as [| \206\1472], \206\1473 as [| \206\1473]; repeat rewrite merge_I_r;
  trivial).
generalize dependent \206\1473.
generalize dependent \206\1471.
(induction \206\1472 as [| o2 \206\1472']).
+
(intros).
(rewrite merge_nil_l, merge_nil_r; reflexivity).
+
(intros \206\1471 \206\1473).
(destruct \206\1471 as [| o1 \206\1471'], \206\1473 as [| o3 \206\1473']; trivial).
-
(rewrite 2!merge_nil_l).
reflexivity.
-
(rewrite 2!merge_nil_r).
reflexivity.
-
(destruct o1, o2, o3; trivial).
*
(simpl).
(destruct (merge' \206\1472' \206\1473'); reflexivity).
*
(simpl).
(destruct (merge' \206\1471' \206\1472'), (merge' \206\1472' \206\1473'); reflexivity).
*
(simpl).
(destruct (merge' \206\1471' \206\1472') eqn:M12, (merge' \206\1472' \206\1473') eqn:M23).
reflexivity.
(rewrite <- merge_merge' in *).
(rewrite <- M23).
(rewrite IH\206\1472').
(rewrite M12).
reflexivity.
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
reflexivity.
(destruct (merge' \206\1471' c0) eqn:M123).
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
assumption.
(simpl).
(rewrite <- merge_merge' in *).
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23, M123).
reflexivity.
*
(simpl).
(destruct (merge' \206\1471' \206\1472'), (merge' \206\1472' \206\1473'); reflexivity).
*
(simpl).
(destruct (merge' \206\1471' \206\1472') eqn:M12, (merge' \206\1472' \206\1473') eqn:M23).
reflexivity.
(rewrite <- merge_merge' in *).
(rewrite <- M23).
(rewrite IH\206\1472').
(rewrite M12).
reflexivity.
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
reflexivity.
(destruct (merge' \206\1471' c0) eqn:M123).
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
assumption.
(simpl).
(rewrite <- merge_merge' in *).
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23, M123).
reflexivity.
*
(simpl).
(destruct (merge' \206\1471' \206\1472') eqn:M12, (merge' \206\1472' \206\1473') eqn:M23).
reflexivity.
(rewrite <- merge_merge' in *).
(rewrite <- M23).
(rewrite IH\206\1472').
(rewrite M12).
reflexivity.
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
reflexivity.
(destruct (merge' \206\1471' c0) eqn:M123).
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
assumption.
(simpl).
(rewrite <- merge_merge' in *).
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23, M123).
reflexivity.
*
(simpl).
(destruct (merge' \206\1471' \206\1472') eqn:M12, (merge' \206\1472' \206\1473') eqn:M23).
reflexivity.
(rewrite <- merge_merge' in *).
(rewrite <- M23).
(rewrite IH\206\1472').
(rewrite M12).
reflexivity.
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
reflexivity.
(destruct (merge' \206\1471' c0) eqn:M123).
(rewrite <- merge_merge' in *).
symmetry.
(apply merge_invalid_iff).
right.
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23).
assumption.
(simpl).
(rewrite <- merge_merge' in *).
(rewrite <- M12).
(rewrite <- IH\206\1472').
(rewrite M23, M123).
reflexivity.
Defined.
Definition cons_o (o : option WType) (\206\147 : OCtx) : OCtx :=
  match \206\147 with
  | Invalid => Invalid
  | Valid \206\147' => Valid (o :: \206\147')
  end.
Lemma cons_dist_merge :
  forall \206\1471 \206\1472, cons_o None (\206\1471 \226\139\147 \206\1472) = cons_o None \206\1471 \226\139\147 cons_o None \206\1472.
Proof.
(destruct \206\1471; destruct \206\1472; simpl; auto).
Defined.
Lemma merge_nil_inversion' :
  forall \206\1471 \206\1472 : Ctx, \206\1471 \226\139\147 \206\1472 = \226\136\133 -> (\206\1471 = []) * (\206\1472 = []).
Proof.
(induction \206\1471 as [| o \206\1471]; intros \206\1472; try inversion 1; auto).
(destruct \206\1472 as [| o' \206\1472]; try (solve [ inversion H1 ])).
(destruct o, o', (merge' \206\1471 \206\1472); inversion H1).
Defined.
Lemma merge_nil_inversion :
  forall \206\1471 \206\1472 : OCtx, \206\1471 \226\139\147 \206\1472 = \226\136\133 -> (\206\1471 = \226\136\133) * (\206\1472 = \226\136\133).
Proof.
(intros \206\1471 \206\1472 eq).
(destruct \206\1471 as [| \206\1471], \206\1472 as [| \206\1472]; try (solve [ inversion eq ])).
(apply merge_nil_inversion' in eq).
(intuition; congruence).
Defined.
Lemma ctx_cons_inversion :
  forall (\206\147 \206\1471 \206\1472 : Ctx) o o1 o2,
  Valid (o1 :: \206\1471) \226\139\147 Valid (o2 :: \206\1472) = Valid (o :: \206\147) ->
  (\206\1471 \226\139\147 \206\1472 = Valid \206\147) * (merge_wire o1 o2 = Valid [o]).
Proof.
(intros \206\147 \206\1471 \206\1472 o o1 o2 H).
(inversion H).
(destruct (merge_wire o1 o2) eqn:Eq1).
(inversion H1).
(rewrite <- merge_merge' in H1).
(destruct (\206\1471 \226\139\147 \206\1472) eqn:Eq2).
(inversion H1).
(destruct o1, o2; simpl in Eq1).
(inversion Eq1).
-
(apply ctx_octx in Eq1).
(rewrite <- Eq1 in *).
(simpl in H1).
(inversion H1; subst; auto).
-
(apply ctx_octx in Eq1).
(rewrite <- Eq1 in *).
(simpl in H1).
(inversion H1; subst; auto).
-
(apply ctx_octx in Eq1).
(rewrite <- Eq1 in *).
(simpl in H1).
(inversion H1; subst; auto).
Defined.
Lemma merge_singleton_append :
  forall W (\206\147 : Ctx), \206\147 \226\139\147 singleton (length \206\147) W = Valid (\206\147 ++ [Some W]).
Proof.
(induction \206\147).
-
(simpl).
reflexivity.
-
(simpl in *).
(destruct a; simpl; rewrite IH\206\147; reflexivity).
Qed.
Lemma merge_offset :
  forall (n : nat) (\206\1471 \206\1472 \206\147 : Ctx),
  Valid \206\147 = \206\1471 \226\139\147 \206\1472 ->
  Valid (repeat None n ++ \206\1471) \226\139\147 Valid (repeat None n ++ \206\1472) =
  Valid (repeat None n ++ \206\147).
Proof.
(intros n \206\1471 \206\1472 \206\147 H).
(induction n).
-
(simpl).
auto.
-
(simpl in *).
(rewrite IHn).
reflexivity.
Qed.
Instance PCM_OCtx : (PCM OCtx) := { one :=\226\136\133; zero :=Invalid; m :=merge}.
Instance PCM_Laws_OCtx : (PCM_Laws OCtx) := { M_unit :=merge_nil_r;
 M_assoc :=merge_assoc; M_comm :=merge_comm; M_absorb :=merge_I_r}.
Hint Resolve PCM_OCtx.
Hint Resolve PCM_Laws_OCtx.
Definition is_valid (\206\147 : OCtx) : Prop := exists \206\147', \206\147 = Valid \206\147'.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation "\206\147 \226\169\181 \206\1471 \226\136\153 \206\1472" := (valid_merge \206\1471 \206\1472 \206\147) (at level 20) : circ_scope.
Lemma valid_valid : forall \206\147, is_valid (Valid \206\147).
Proof.
(intros).
exists \206\147.
reflexivity.
Defined.
Lemma valid_empty : is_valid \226\136\133.
Proof.
(unfold is_valid; eauto).
Defined.
Lemma not_valid : not (is_valid Invalid).
Proof.
(intros [\206\147 F]; inversion F).
Defined.
Lemma valid_l : forall \206\1471 \206\1472, is_valid (\206\1471 \226\139\147 \206\1472) -> is_valid \206\1471.
Proof.
(intros \206\1471 \206\1472 V).
(unfold is_valid in *).
(destruct V as [\206\147' V]).
(apply merge_valid in V as [[\206\1471'] [\206\1472']]).
eauto.
Defined.
Lemma valid_r : forall \206\1471 \206\1472, is_valid (\206\1471 \226\139\147 \206\1472) -> is_valid \206\1472.
Proof.
(intros \206\1471 \206\1472 V).
(unfold is_valid in *).
(destruct V as [\206\147' V]).
(apply merge_valid in V as [[\206\1471'] [\206\1472']]).
eauto.
Defined.
Lemma valid_cons :
  forall (o1 o2 : option WType) (\206\1471 \206\1472 : Ctx),
  is_valid (Valid (o1 :: \206\1471) \226\139\147 Valid (o2 :: \206\1472)) <->
  is_valid (merge_wire o1 o2) /\ is_valid (\206\1471 \226\139\147 \206\1472).
Proof.
(intros o1 o2 \206\1471 \206\1472).
split.
-
(intros [\206\147 V]).
(inversion V).
(destruct (merge_wire o1 o2)).
(inversion H0).
(simpl).
(destruct (merge' \206\1471 \206\1472)).
(inversion H0).
(unfold is_valid; split; eauto).
-
(intros [[W Vo] [\206\147 V]]).
(simpl in *).
(rewrite Vo, V).
(unfold is_valid; eauto).
Defined.
Lemma valid_join :
  forall \206\1471 \206\1472 \206\1473,
  is_valid (\206\1471 \226\139\147 \206\1472) ->
  is_valid (\206\1471 \226\139\147 \206\1473) -> is_valid (\206\1472 \226\139\147 \206\1473) -> is_valid (\206\1471 \226\139\147 \206\1472 \226\139\147 \206\1473).
Proof.
(destruct \206\1471 as [| \206\1471]).
(intros \206\1472 \206\1473 [\206\14712 V12]; inversion V12).
(induction \206\1471 as [| o1 \206\1471]).
+
(intros \206\1472 \206\1473 V12 V13 V23).
(rewrite merge_nil_l).
assumption.
+
(intros \206\1472 \206\1473 V12 V13 V23).
(destruct \206\1472 as [| \206\1472], \206\1473 as [| \206\1473];
  try (solve [ inversion V23; inversion H ])).
(destruct \206\1472 as [| o2 \206\1472], \206\1473 as [| o3 \206\1473];
  try (rewrite merge_nil_r in *; auto)).
(destruct o1, o2, o3; try (solve [ inversion V12; inversion H ]);
  try (solve [ inversion V13; inversion H ]);
  try (solve [ inversion V23; inversion H ])).
-
(apply valid_cons in V12 as [_ [\206\14712 V12]]).
(apply valid_cons in V13 as [_ [\206\14713 V13]]).
(apply valid_cons in V23 as [_ [\206\14723 V23]]).
(destruct (IH\206\1471 (Valid \206\1472) (Valid \206\1473)) as [\206\147 V123]; unfold is_valid; eauto).
exists (Some w :: \206\147).
(simpl in *).
(rewrite V12).
(simpl in *).
(rewrite V12 in V123).
(simpl in V123).
(rewrite V123).
reflexivity.
-
(apply valid_cons in V12 as [_ [\206\14712 V12]]).
(apply valid_cons in V13 as [_ [\206\14713 V13]]).
(apply valid_cons in V23 as [_ [\206\14723 V23]]).
(destruct (IH\206\1471 (Valid \206\1472) (Valid \206\1473)) as [\206\147 V123]; unfold is_valid; eauto).
exists (Some w :: \206\147).
(simpl in *).
(rewrite V12).
(simpl in *).
(rewrite V12 in V123).
(simpl in V123).
(rewrite V123).
reflexivity.
-
(apply valid_cons in V12 as [_ [\206\14712 V12]]).
(apply valid_cons in V13 as [_ [\206\14713 V13]]).
(apply valid_cons in V23 as [_ [\206\14723 V23]]).
(destruct (IH\206\1471 (Valid \206\1472) (Valid \206\1473)) as [\206\147 V123]; unfold is_valid; eauto).
exists (Some w :: \206\147).
(simpl in *).
(rewrite V12).
(simpl in *).
(rewrite V12 in V123).
(simpl in V123).
(rewrite V123).
reflexivity.
-
(apply valid_cons in V12 as [_ [\206\14712 V12]]).
(apply valid_cons in V13 as [_ [\206\14713 V13]]).
(apply valid_cons in V23 as [_ [\206\14723 V23]]).
(destruct (IH\206\1471 (Valid \206\1472) (Valid \206\1473)) as [\206\147 V123]; unfold is_valid; eauto).
exists (None :: \206\147).
(simpl in *).
(rewrite V12).
(simpl in *).
(rewrite V12 in V123).
(simpl in V123).
(rewrite V123).
reflexivity.
Defined.
Lemma valid_split :
  forall \206\1471 \206\1472 \206\1473,
  is_valid (\206\1471 \226\139\147 \206\1472 \226\139\147 \206\1473) ->
  is_valid (\206\1471 \226\139\147 \206\1472) /\ is_valid (\206\1471 \226\139\147 \206\1473) /\ is_valid (\206\1472 \226\139\147 \206\1473).
Proof.
(intros \206\1471 \206\1472 \206\1473 [\206\147 V]).
(unfold is_valid).
intuition.
+
(destruct (\206\1471 \226\139\147 \206\1472); [ inversion V | eauto ]).
+
(rewrite (merge_comm \206\1471 \206\1472), <- merge_assoc in V).
(destruct (\206\1471 \226\139\147 \206\1473); [ rewrite merge_I_r in V; inversion V | eauto ]).
+
(rewrite <- merge_assoc in V).
(destruct (\206\1472 \226\139\147 \206\1473); [ rewrite merge_I_r in V; inversion V | eauto ]).
Defined.
Lemma size_octx_merge :
  forall \206\1471 \206\1472 : OCtx,
  is_valid (\206\1471 \226\139\147 \206\1472) ->
  size_octx (\206\1471 \226\139\147 \206\1472) = (size_octx \206\1471 + size_octx \206\1472)%nat.
Proof.
(intros \206\1471 \206\1472 V).
(destruct \206\1471 as [| \206\1471], \206\1472 as [| \206\1472]; try apply not_valid in V; try easy).
revert \206\1472 V.
(induction \206\1471 as [| [W1| ] \206\1471]; intros \206\1472 V;
  [ rewrite merge_nil_l; auto |  |  ];
  (destruct \206\1472 as [| [W2| ] \206\1472]; [ rewrite merge_nil_r; auto |  |  ]);
  [ absurd (is_valid Invalid); auto; apply not_valid |  |  |  ]).
-
specialize IH\206\1471 with \206\1472.
(simpl in *).
(destruct (merge' \206\1471 \206\1472) as [| \206\147] eqn:H;
  [ absurd (is_valid Invalid); auto; apply not_valid |  ]).
(simpl in *).
(rewrite IH\206\1471; auto).
(apply valid_valid).
-
specialize IH\206\1471 with \206\1472.
(simpl in *).
(destruct (merge' \206\1471 \206\1472) as [| \206\147] eqn:H;
  [ absurd (is_valid Invalid); auto; apply not_valid |  ]).
(simpl in *).
(rewrite IH\206\1471; auto).
(apply valid_valid).
-
specialize IH\206\1471 with \206\1472.
(simpl in *).
(destruct (merge' \206\1471 \206\1472) as [| \206\147] eqn:H;
  [ absurd (is_valid Invalid); auto; apply not_valid |  ]).
(simpl in *).
(rewrite IH\206\1471; auto).
(apply valid_valid).
Defined.
Ltac
 simplify_invalid :=
  repeat rewrite merge_I_l in *; repeat rewrite merge_I_r in *.
Ltac
 invalid_contradiction :=
  absurd False; [ inversion 1 |  ];
   repeat match goal with
          | H:?\206\147 \226\169\181 ?\206\1471 \226\136\153 ?\206\1472 |- _ => destruct H
          end; subst; simplify_invalid;
   match goal with
   | H:is_valid Invalid |- _ => apply (False_rect _ (not_valid H))
   | H:Valid _ = Invalid |- _ => inversion H
   end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma merge_o_ind_fun :
  forall o1 o2 o, merge_o o1 o2 o -> merge_wire o1 o2 = Valid [o].
Proof.
(induction 1; auto).
Qed.
Lemma merge_ind_fun : forall \206\1471 \206\1472 \206\147, merge_ind \206\1471 \206\1472 \206\147 -> \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472.
Proof.
(induction 1).
*
(split; [ apply valid_valid | auto ]).
*
(split; [ apply valid_valid | rewrite merge_nil_r; auto ]).
*
(destruct IHmerge_ind).
(split; [ apply valid_valid |  ]).
(simpl).
(erewrite merge_o_ind_fun; [  | eauto ]).
(unfold merge in pf_merge0).
(rewrite <- pf_merge0).
auto.
Qed.
Lemma merge_o_fun_ind :
  forall o1 o2 o, merge_wire o1 o2 = Valid [o] -> merge_o o1 o2 o.
Proof.
(intros [w1| ] [w2| ] [w| ]; simpl; inversion 1; constructor).
Qed.
Lemma merge_fun_ind : forall \206\1471 \206\1472 \206\147, \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> merge_ind \206\1471 \206\1472 \206\147.
Proof.
(intros [| \206\1471] [| \206\1472] [| \206\147]; intros; try invalid_contradiction).
generalize dependent \206\147.
generalize dependent \206\1472.
(induction \206\1471 as [| o1 \206\1471]; intros \206\1472 \206\147 [pf_valid pf_merge]).
*
(simpl in pf_merge).
(rewrite pf_merge).
constructor.
*
(destruct \206\1472 as [| o2 \206\1472]).
+
(rewrite merge_nil_r in pf_merge).
(rewrite pf_merge).
constructor.
+
(destruct o1 as [w1| ], o2 as [w2| ]).
-
(simpl in *).
invalid_contradiction.
-
(simpl in pf_merge).
(destruct (merge' \206\1471 \206\1472) as [| \206\147'] eqn:H_\206\147'; [ invalid_contradiction |  ]).
(rewrite pf_merge).
(constructor; [ apply merge_o_fun_ind; auto |  ]).
(apply IH\206\1471).
(split; [ apply valid_valid | auto ]).
-
(simpl in pf_merge).
(destruct (merge' \206\1471 \206\1472) as [| \206\147'] eqn:H_\206\147'; [ invalid_contradiction |  ]).
(rewrite pf_merge).
(constructor; [ apply merge_o_fun_ind; auto |  ]).
(apply IH\206\1471).
(split; [ apply valid_valid | auto ]).
-
(simpl in pf_merge).
(destruct (merge' \206\1471 \206\1472) as [| \206\147'] eqn:H_\206\147'; [ invalid_contradiction |  ]).
(rewrite pf_merge).
(constructor; [ apply merge_o_fun_ind; auto |  ]).
(apply IH\206\1471).
(split; [ apply valid_valid | auto ]).
Qed.
Lemma merge_intersection :
  forall \206\1471 \206\1472 \206\1473 \206\1474,
  is_valid (\206\1471 \226\139\147 \206\1472) ->
  \206\1471 \226\139\147 \206\1472 = \206\1473 \226\139\147 \206\1474 ->
  {\206\14713 : OCtx &
  {\206\14714 : OCtx &
  {\206\14723 : OCtx &
  {\206\14724 : OCtx &
  \206\1471 \226\169\181 \206\14713 \226\136\153 \206\14714 /\ \206\1472 \226\169\181 \206\14723 \226\136\153 \206\14724 /\ \206\1473 \226\169\181 \206\14713 \226\136\153 \206\14723 /\ \206\1474 \226\169\181 \206\14714 \226\136\153 \206\14724}}}}.
Proof.
(intros \206\1471 \206\1472 \206\1473 \206\1474 V M).
(assert (H : (\206\1471 \226\139\147 \206\1472) \226\169\181 \206\1473 \226\136\153 \206\1474)).
(constructor; assumption).
clear M V.
(apply merge_fun_ind in H).
(remember (\206\1471 \226\139\147 \206\1472) as \206\147).
generalize dependent \206\1472.
generalize dependent \206\1471.
(induction H).
-
(intros \206\1471 \206\1472).
exists \226\136\133,\206\1471,\226\136\133,\206\1472.
(repeat split; try apply valid_valid).
(destruct \206\1471; [ invalid_contradiction | apply valid_valid ]).
(rewrite merge_nil_l; reflexivity).
(destruct \206\1472; [ invalid_contradiction | apply valid_valid ]).
(rewrite merge_nil_l; reflexivity).
assumption.
-
(intros \206\1471 \206\1472).
exists \206\1471,\226\136\133,\206\1472,\226\136\133.
(repeat split; try apply valid_valid).
(destruct \206\1471; [ invalid_contradiction | apply valid_valid ]).
(rewrite merge_nil_r; reflexivity).
(destruct \206\1472; [ invalid_contradiction | apply valid_valid ]).
(rewrite merge_nil_r; reflexivity).
assumption.
-
rename \206\1471 into \206\1473.
rename \206\1472 into \206\1474.
rename o1 into o3.
rename o2 into o4.
(intros \206\1471 \206\1472 M).
(destruct \206\1471 as [| \206\1471]).
invalid_contradiction.
(destruct \206\1472 as [| \206\1472]).
invalid_contradiction.
(destruct \206\1471 as [| o1 \206\1471], \206\1472 as [| o2 \206\1472]).
+
(inversion M).
+
(rewrite merge_nil_l in M).
(inversion M).
subst.
exists \226\136\133,\226\136\133,(Valid (o3 :: \206\1473)),(Valid (o4 :: \206\1474)).
(repeat split; try apply valid_valid).
(apply merge_ind_fun).
(constructor; assumption).
+
(rewrite merge_nil_r in M).
(inversion M).
subst.
exists (Valid (o3 :: \206\1473)),(Valid (o4 :: \206\1474)),\226\136\133,\226\136\133.
(repeat split; try apply valid_valid).
(apply merge_ind_fun).
(constructor; assumption).
+
(assert (M12 : Valid (o :: \206\147) \226\169\181 Valid (o1 :: \206\1471) \226\136\153 Valid (o2 :: \206\1472))).
constructor.
(apply valid_valid).
assumption.
clear M.
(apply merge_fun_ind in M12).
(inversion M12).
subst.
clear M12.
(destruct (IHmerge_ind (Valid \206\1471) (Valid \206\1472)) as [\206\14713 [\206\14714 [\206\14723 [\206\14724 pf]]]]).
(apply merge_ind_fun in H7 as [V M]).
assumption.
(destruct pf as [pf1 [pf2 [pf3 pf4]]]).
(destruct \206\14713 as [| \206\14713]).
invalid_contradiction.
(destruct \206\14714 as [| \206\14714]).
invalid_contradiction.
(destruct \206\14723 as [| \206\14723]).
invalid_contradiction.
(destruct \206\14724 as [| \206\14724]).
invalid_contradiction.
(destruct pf1 as [_ M1], pf2 as [_ M2], pf3 as [_ M3], pf4 as [_ M4]).
(simpl in *).
(inversion m; subst; inversion H3; subst).
*
exists (Valid (None :: \206\14713)),(Valid (None :: \206\14714)),
 (Valid (None :: \206\14723)),(Valid (None :: \206\14724)).
(repeat split; try apply valid_valid; simpl).
(rewrite <- M1; reflexivity).
(rewrite <- M2; reflexivity).
(rewrite <- M3; reflexivity).
(rewrite <- M4; reflexivity).
*
exists (Valid (Some w :: \206\14713)),(Valid (None :: \206\14714)),
 (Valid (None :: \206\14723)),(Valid (None :: \206\14724)).
(repeat split; try apply valid_valid; simpl).
(rewrite <- M1; reflexivity).
(rewrite <- M2; reflexivity).
(rewrite <- M3; reflexivity).
(rewrite <- M4; reflexivity).
*
exists (Valid (None :: \206\14713)),(Valid (None :: \206\14714)),
 (Valid (Some w :: \206\14723)),(Valid (None :: \206\14724)).
(repeat split; try apply valid_valid; simpl).
(rewrite <- M1; reflexivity).
(rewrite <- M2; reflexivity).
(rewrite <- M3; reflexivity).
(rewrite <- M4; reflexivity).
*
exists (Valid (None :: \206\14713)),(Valid (Some w :: \206\14714)),
 (Valid (None :: \206\14723)),(Valid (None :: \206\14724)).
(repeat split; try apply valid_valid; simpl).
(rewrite <- M1; reflexivity).
(rewrite <- M2; reflexivity).
(rewrite <- M3; reflexivity).
(rewrite <- M4; reflexivity).
*
exists (Valid (None :: \206\14713)),(Valid (None :: \206\14714)),
 (Valid (None :: \206\14723)),(Valid (Some w :: \206\14724)).
(repeat split; try apply valid_valid; simpl).
(rewrite <- M1; reflexivity).
(rewrite <- M2; reflexivity).
(rewrite <- M3; reflexivity).
(rewrite <- M4; reflexivity).
Qed.
Definition Disjoint \206\1471 \206\1472 : Prop :=
  match \206\1471, \206\1472 with
  | Invalid, _ => True
  | _, Invalid => True
  | Valid _, Valid _ => is_valid (\206\1471 \226\139\147 \206\1472)
  end.
Lemma disjoint_nil_r : forall \206\147, Disjoint \206\147 \226\136\133.
Proof.
(destruct \206\147 as [| \206\147]; [ exact I |  ]).
(unfold Disjoint).
(rewrite merge_nil_r).
exists \206\147.
reflexivity.
Defined.
Lemma disjoint_valid :
  forall \206\1471 \206\1472,
  Disjoint \206\1471 \206\1472 -> is_valid \206\1471 -> is_valid \206\1472 -> is_valid (\206\1471 \226\139\147 \206\1472).
Proof.
(intros \206\1471 \206\1472 disj [\206\1471' valid1] [\206\1472' valid2]).
(rewrite valid1 in *; rewrite valid2 in *; auto).
Defined.
Lemma disjoint_merge :
  forall \206\147 \206\1471 \206\1472, Disjoint \206\147 \206\1471 -> Disjoint \206\147 \206\1472 -> Disjoint \206\147 (\206\1471 \226\139\147 \206\1472).
Proof.
(intros \206\147 \206\1471 \206\1472 disj1 disj2).
(remember (\206\1471 \226\139\147 \206\1472) as \206\147').
(destruct \206\147 as [| \206\147]; [ exact I |  ]).
(destruct \206\147' as [| \206\147']; [ exact I |  ]).
(assert (valid0 : is_valid \206\147)).
{
(apply valid_valid).
}
(assert (valid1 : is_valid \206\1471)).
{
(destruct \206\1471 as [| \206\1471]; [ inversion Heq\206\147' |  ]).
(apply valid_valid).
}
(assert (valid2 : is_valid \206\1472)).
{
(destruct \206\1472 as [| \206\1472]; [ rewrite merge_I_r in *; inversion Heq\206\147' |  ]).
(apply valid_valid).
}
(assert (valid1' : is_valid (\206\147 \226\139\147 \206\1471))).
{
(apply disjoint_valid; auto).
}
(assert (valid2' : is_valid (\206\147 \226\139\147 \206\1472))).
{
(apply disjoint_valid; auto).
}
(unfold Disjoint).
(rewrite Heq\206\147').
(rewrite merge_assoc).
(apply valid_join; auto).
(exists \206\147'; auto).
Defined.
Lemma disjoint_split :
  forall \206\1471 \206\1472 \206\147,
  is_valid \206\1471 ->
  is_valid \206\1472 ->
  Disjoint \206\1471 \206\1472 -> Disjoint (\206\1471 \226\139\147 \206\1472) \206\147 -> Disjoint \206\1471 \206\147 /\ Disjoint \206\1472 \206\147.
Proof.
(intros \206\1471 \206\1472 \206\147 [\206\1471' valid1] [\206\1472' valid2] disj disj').
subst.
(unfold Disjoint in disj).
(destruct \206\147 as [| \206\147]; [ split; exact I |  ]).
(unfold Disjoint).
(destruct disj as [\206\147' is_valid]).
(rewrite is_valid in disj').
(unfold Disjoint in disj').
(rewrite <- is_valid in disj').
(apply valid_split in disj').
(destruct disj' as [H1 [H2 H3]]; split; auto).
Defined.
Definition xor_option {a} (o1 : option a) (o2 : option a) : 
  option a :=
  match o1, o2 with
  | Some a1, None => Some a1
  | None, Some a2 => Some a2
  | _, _ => None
  end.
Fixpoint index (\206\147 : OCtx) (i : nat) : option WType :=
  match \206\147 with
  | Invalid => None
  | Valid \206\147' => maybe (\206\147' !! i) None
  end.
Lemma index_invalid : forall i, index Invalid i = None.
Proof.
auto.
Qed.
Lemma index_empty : forall i, index \226\136\133 i = None.
Proof.
(intros).
(simpl).
(rewrite nth_nil).
auto.
Qed.
Lemma singleton_index :
  forall x w \206\147, SingletonCtx x w \206\147 -> index \206\147 x = Some w.
Proof.
(induction 1; simpl; auto).
Qed.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma empty_ctx_size : forall \206\147, empty_ctx \206\147 -> size_ctx \206\147 = 0%nat.
Proof.
(induction 1; auto).
Qed.
Lemma eq_dec_empty_ctx : forall \206\147, {empty_ctx \206\147} + {~ empty_ctx \206\147}.
Proof.
(intros).
(induction \206\147).
-
(left; constructor).
-
(destruct a).
+
right.
easy.
+
(destruct IH\206\147).
*
(left; constructor; easy).
*
right.
(intros F).
(apply n).
(inversion F).
easy.
Qed.
Lemma merge_empty :
  forall \206\147 \206\1471 \206\1472 : Ctx,
  \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> empty_ctx \206\147 -> empty_ctx \206\1471 /\ empty_ctx \206\1472.
Proof.
(intros \206\147 \206\1471 \206\1472 M E).
(apply merge_fun_ind in M).
dependent induction M.
-
(split; trivial; constructor).
-
(split; trivial; constructor).
-
(inversion E; subst).
(inversion m; subst).
specialize (IHM \206\1470 \206\1473 \206\1474 eq_refl eq_refl eq_refl H0) as [E\206\1473 E\206\1474].
(split; constructor; easy).
Qed.
Fixpoint trim (\206\147 : Ctx) : Ctx :=
  match \206\147 with
  | [] => []
  | None :: \206\147' => match trim \206\147' with
                  | [] => []
                  | \206\147'' => None :: \206\147''
                  end
  | Some w :: \206\147' => Some w :: trim \206\147'
  end.
Definition otrim (\206\147 : OCtx) :=
  match \206\147 with
  | Invalid => Invalid
  | Valid \206\147 => Valid (trim \206\147)
  end.
Lemma trim_otrim : forall \206\147 : Ctx, Valid (trim \206\147) = otrim \206\147.
Proof.
easy.
Qed.
Lemma size_ctx_trim : forall \206\147, size_ctx (trim \206\147) = size_ctx \206\147.
Proof.
(induction \206\147; auto).
(destruct a; simpl).
(rewrite IH\206\147; easy).
(simpl).
(destruct (trim \206\147); easy).
Qed.
Lemma size_octx_trim : forall \206\147, size_octx (trim \206\147) = size_octx \206\147.
Proof.
(apply size_ctx_trim).
Qed.
Lemma index_trim : forall \206\147 i, index (trim \206\147) i = index \206\147 i.
Proof.
(induction \206\147 as [| [w| ] \206\147]; intros i).
*
(simpl).
auto.
*
(simpl).
(destruct i; simpl; auto).
(apply IH\206\147).
*
(simpl).
(remember (trim \206\147) as \206\147').
(destruct \206\147' as [| o \206\147']; auto).
+
(rewrite nth_nil).
(destruct i; simpl; auto).
(simpl in IH\206\147).
(rewrite <- IH\206\147).
(rewrite nth_nil).
auto.
+
(destruct i; simpl; auto).
(apply IH\206\147).
Qed.
Lemma trim_empty : forall \206\147, empty_ctx \206\147 -> trim \206\147 = [].
Proof.
(induction 1; simpl; auto).
(rewrite IHempty_ctx; auto).
Qed.
Lemma trim_non_empty : forall \206\147, ~ empty_ctx \206\147 -> trim \206\147 <> [].
Proof.
(intros \206\147 NE).
(induction \206\147).
-
(contradict NE).
constructor.
-
(destruct a).
+
(simpl).
easy.
+
(simpl).
(destruct (trim \206\147)).
*
(apply IH\206\147).
(intros F).
(apply NE).
(constructor; easy).
*
easy.
Qed.
Lemma trim_cons_non_empty :
  forall o \206\147, ~ empty_ctx \206\147 -> trim (o :: \206\147) = o :: trim \206\147.
Proof.
(intros o \206\147 H).
(destruct o; trivial).
(simpl).
(apply trim_non_empty in H).
(destruct (trim \206\147); easy).
Qed.
Lemma trim_valid : forall \206\147 : OCtx, is_valid \206\147 <-> is_valid (otrim \206\147).
Proof.
(destruct \206\147 as [| \206\147]).
-
(simpl).
easy.
-
(simpl).
(split; intros; apply valid_valid).
Qed.
Lemma trim_merge_dist : forall \206\1471 \206\1472, otrim \206\1471 \226\139\147 otrim \206\1472 = otrim (\206\1471 \226\139\147 \206\1472).
Proof.
(destruct \206\1471 as [| \206\1471], \206\1472 as [| \206\1472]; try (simpl; easy)).
gen \206\1472.
(induction \206\1471 as [| o1 \206\1471 IH]).
-
(intros \206\1472).
easy.
-
(intros \206\1472).
(destruct \206\1472 as [| o2 \206\1472]).
(rewrite 2!merge_nil_r).
easy.
specialize (IH \206\1472).
(destruct (eq_dec_empty_ctx \206\1471) as [E1| NE1];
  destruct (eq_dec_empty_ctx \206\1472) as [E2| NE2]).
+
(repeat rewrite <- trim_otrim in *).
(apply trim_empty in E1).
(apply trim_empty in E2).
(rewrite E1, E2 in *).
(rewrite merge_nil_l in *).
(destruct o1, o2).
*
(simpl).
easy.
*
(simpl).
(rewrite E1, E2).
(simpl in IH).
(destruct (merge' \206\1471 \206\1472)).
(inversion IH).
(simpl in *).
(inversion IH).
easy.
*
(simpl).
(rewrite E1, E2).
(simpl in IH).
(destruct (merge' \206\1471 \206\1472)).
(inversion IH).
(simpl in *).
(inversion IH).
easy.
*
(simpl).
(rewrite E1, E2).
(simpl in IH).
(destruct (merge' \206\1471 \206\1472)).
(inversion IH).
(simpl in *).
(inversion IH).
easy.
+
(repeat rewrite <- trim_otrim in *).
(apply trim_empty in E1).
(rewrite E1 in *).
(rewrite merge_nil_l in *).
(eapply trim_cons_non_empty in NE2).
(rewrite NE2 in *).
(destruct o1, o2).
*
(simpl).
easy.
*
(simpl in *).
(rewrite E1; simpl).
(destruct (merge' \206\1471 \206\1472) eqn:M).
(inversion IH).
(simpl).
(inversion IH).
easy.
*
(simpl in *).
(rewrite E1).
(simpl).
(destruct (merge' \206\1471 \206\1472) eqn:M).
(inversion IH).
(simpl).
(inversion IH).
easy.
*
(simpl).
(simpl in IH).
(rewrite E1).
(simpl).
(destruct (merge' \206\1471 \206\1472) eqn:M).
(inversion IH).
(simpl).
(inversion IH).
(simpl in *).
(destruct (trim \206\1472)).
(inversion NE2).
easy.
+
(repeat rewrite <- trim_otrim in *).
(apply trim_empty in E2).
(rewrite E2 in *).
(rewrite merge_nil_r in *).
(eapply trim_cons_non_empty in NE1).
(rewrite NE1 in *).
(destruct o1, o2).
*
(simpl).
easy.
*
(simpl in *).
(rewrite E2; simpl).
(destruct (merge' \206\1471 \206\1472) eqn:M).
(inversion IH).
(simpl).
(inversion IH).
easy.
*
(simpl in *).
(rewrite E2).
(simpl).
(destruct (merge' \206\1471 \206\1472) eqn:M).
(inversion IH).
(rewrite <- merge_merge').
(rewrite merge_nil_r).
(simpl).
(inversion IH).
easy.
*
(simpl).
(simpl in IH).
(rewrite E2).
(simpl).
(destruct (merge' \206\1471 \206\1472) eqn:M).
(inversion IH).
(simpl).
(inversion IH).
(simpl in *).
(destruct (trim \206\1471)).
(inversion NE1).
easy.
+
(repeat rewrite <- trim_otrim in *).
(eapply trim_cons_non_empty in NE1).
(rewrite NE1 in *).
(eapply trim_cons_non_empty in NE2).
(rewrite NE2 in *).
(destruct o1, o2).
*
(simpl).
easy.
*
(simpl in *).
(rewrite IH).
(destruct (merge' \206\1471 \206\1472)).
easy.
(simpl).
easy.
*
(simpl in *).
(rewrite IH).
(destruct (merge' \206\1471 \206\1472)).
easy.
(simpl).
easy.
*
(simpl in *).
(rewrite IH).
(destruct (merge' \206\1471 \206\1472) eqn:E).
easy.
(simpl in *).
(destruct (trim c)).
(destruct (trim \206\1471)).
(inversion NE1).
(destruct (trim \206\1472)).
(inversion NE2).
(simpl in IH).
(destruct (merge_wire o o0) eqn:EW).
(inversion IH).
(destruct (merge' c0 c1) eqn:E').
(inversion IH).
(destruct o, o0; simpl in EW; inversion EW as [S]; rewrite <- S in IH;
  inversion IH).
easy.
Qed.
Lemma trim_merge :
  forall \206\147 \206\1471 \206\1472, \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> otrim \206\147 \226\169\181 otrim \206\1471 \226\136\153 otrim \206\1472.
Proof.
(intros \206\147 \206\1471 \206\1472 M).
(apply merge_fun_ind in M).
(induction M).
-
split.
(simpl; apply valid_valid).
(rewrite merge_nil_l; easy).
-
split.
(simpl; apply valid_valid).
(rewrite merge_nil_r; easy).
-
split.
(simpl).
(apply valid_valid).
(destruct (eq_dec_empty_ctx \206\147)).
+
(apply merge_ind_fun in M).
specialize (merge_empty _ _ _ M e) as [E1 E2].
(inversion m; subst; simpl).
*
(repeat rewrite trim_empty; easy).
*
(repeat rewrite trim_empty; easy).
*
(repeat rewrite trim_empty; easy).
+
(apply trim_non_empty in n).
(destruct IHM as [V IHM]).
(inversion m; subst; simpl in *).
*
(destruct (trim \206\147) eqn:E).
easy.
(destruct (trim \206\1471) eqn:E1, (trim \206\1472) eqn:E2; simpl in *; inversion IHM; easy).
*
(destruct (trim \206\1471) eqn:E1, (trim \206\1472) eqn:E2; simpl in *; inversion IHM; easy).
*
(destruct (trim \206\1471) eqn:E1, (trim \206\1472) eqn:E2; simpl in *; inversion IHM; easy).
Qed.
Definition octx_length (\206\147 : OCtx) : nat :=
  match \206\147 with
  | Invalid => O
  | Valid ls => length ls
  end.
Lemma merge_dec \206\1471 \206\1472 : is_valid (\206\1471 \226\139\147 \206\1472) + {\206\1471 \226\139\147 \206\1472 = Invalid}.
Proof.
(induction \206\1471 as [| \206\1471]; [ right; auto |  ]).
(destruct \206\1472 as [| \206\1472]; [ right; auto |  ]).
(revert \206\1472; induction \206\1471 as [| o1 \206\1471]; intros \206\1472).
{
(simpl).
left.
(apply valid_valid).
}
(destruct \206\1472 as [| o2 \206\1472]).
{
(simpl).
left.
(apply valid_valid).
}
(destruct (IH\206\1471 \206\1472) as [IH| IH]).
-
(destruct o1 as [| W1]; destruct o2 as [| W2]; simpl in *).
{
(right; auto).
}
{
(left; destruct (merge' \206\1471 \206\1472); auto).
(apply valid_valid).
}
{
(left; destruct (merge' \206\1471 \206\1472); auto).
(apply valid_valid).
}
{
(left; destruct (merge' \206\1471 \206\1472); auto).
(apply valid_valid).
}
-
right.
(simpl in *).
(rewrite IH).
(destruct (merge_wire o1 o2); auto).
Defined.
Open Scope circ_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Fixpoint pat_to_list {w} (p : Pat w) : list Var :=
  match p with
  | unit => []
  | qubit x => [x]
  | bit x => [x]
  | pair p1 p2 => pat_to_list p1 ++ pat_to_list p2
  end.
Fixpoint pat_map {w} (f : Var -> Var) (p : Pat w) : 
Pat w :=
  match p with
  | unit => unit
  | qubit x => qubit (f x)
  | bit x => bit (f x)
  | pair p1 p2 => pair (pat_map f p1) (pat_map f p2)
  end.
Reserved Notation "\206\147 \226\138\162 p ':Pat'" (at level 30).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma pat_ctx_valid : forall \206\147 W (p : Pat W), \206\147 \226\138\162 p :Pat -> is_valid \206\147.
Proof.
(intros \206\147 W p TP).
(unfold is_valid).
(inversion TP; eauto).
Qed.
Lemma octx_wtype_size :
  forall w (p : Pat w) (\206\147 : OCtx), \206\147 \226\138\162 p :Pat -> size_wtype w = size_octx \206\147.
Proof.
(intros w p \206\147 H).
(dependent induction H; simpl; auto).
*
(apply Singleton_size in s).
easy.
*
(apply Singleton_size in s).
easy.
*
subst.
(rewrite size_octx_merge; auto).
Qed.
Lemma ctx_wtype_size :
  forall w (p : Pat w) (\206\147 : Ctx), \206\147 \226\138\162 p :Pat -> size_wtype w = size_ctx \206\147.
Proof.
(intros w p \206\147 H).
replace (size_ctx \206\147) with size_octx \206\147 by easy.
(eapply octx_wtype_size; apply H).
Qed.
Lemma size_wtype_length :
  forall {w} (p : Pat w), length (pat_to_list p) = size_wtype w.
Proof.
(induction p; simpl; auto).
(rewrite app_length).
(rewrite IHp1, IHp2).
auto.
Qed.
Ltac
 PCMize :=
  simpl translate in *; try replace merge with m by auto;
   try replace \226\136\133 with \226\138\164 by auto; try replace Invalid with \226\138\165 by auto.
Ltac
 unPCMize := simpl translate in *; simpl m in *; simpl \226\138\164 in *; simpl \226\138\165 in *.
Ltac monoid := PCMize; try Monoid.monoid.
Ltac
 validate :=
  unPCMize;
   repeat
    match goal with
    | H:Types_Pat _ _ |- _ => apply pat_ctx_valid in H
    | |- is_valid (Valid _) => apply valid_valid
    | H:is_valid ?\206\147 |- is_valid ?\206\147 => exact H
    | H:is_valid (?\206\1471 \226\139\147 ?\206\1472) |- is_valid ?\206\1471 => eapply valid_l; exact H
    | H:is_valid (?\206\1471 \226\139\147 ?\206\1472) |- is_valid ?\206\1472 => eapply valid_r; exact H
    | H:is_valid (?\206\1471 \226\139\147 ?\206\1472)
      |- is_valid (?\206\1472 \226\139\147 ?\206\1471) => rewrite merge_comm; exact H
    | |- context [ \226\136\133 \226\139\147 ?\206\147 ] => rewrite (merge_nil_l \206\147)
    | |- context [ ?\206\147 \226\139\147 \226\136\133 ] => rewrite (merge_nil_r \206\147)
    | H:is_valid (?\206\1471 \226\139\147 (?\206\1472 \226\139\147 ?\206\1473))
      |- _ => rewrite (merge_assoc \206\1471 \206\1472 \206\1473) in H
    | H:is_valid (?\206\1471 \226\139\147 ?\206\1472 \226\139\147 ?\206\1473)
      |- _ => apply valid_split in H as [? [? ?]]
    | |- is_valid (?\206\1471 \226\139\147 (?\206\1472 \226\139\147 ?\206\1473)) => rewrite (merge_assoc \206\1471 \206\1472 \206\1473)
    | |- is_valid (?\206\1471 \226\139\147 ?\206\1472 \226\139\147 ?\206\1473) => apply valid_join; validate
    end.
Ltac
 has_evars term :=
  match term with
  | ?L = ?R => has_evars (L \226\139\147 R)
  | ?L \226\169\181 ?R1 \226\136\153 ?R2 => has_evars (L \226\139\147 R1 \226\139\147 R2)
  | ?\206\1471 \226\139\147 ?\206\1472 => has_evar \206\1471; has_evar \206\1472
  | ?\206\1471 \226\139\147 ?\206\1472 => has_evars \206\1471
  | ?\206\1471 \226\139\147 ?\206\1472 => has_evars \206\1472
  end.
Ltac goal_evars := match goal with
                   | |- ?g => has_evars g
                   end.
Ltac
 solve_merge :=
  match goal with
  | |- ?g => has_evars g
  | |- _ =>
        repeat match goal with
               | H:_ \226\169\181 _ \226\136\153 _ |- _ => destruct H
               end; subst;
         repeat
          match goal with
          | |- _ \226\169\181 _ \226\136\153 _ => split
          | |- is_valid _ => validate
          | |- _ = _ => monoid
          end
  end.
Fixpoint mk_typed_bit (\206\147 : Ctx) : Pat Bit * Ctx :=
  match \206\147 with
  | [] => (bit O, [Some Bit])
  | None :: \206\147' => (bit O, [Some Bit])
  | Some W :: \206\147' =>
      let (p, \206\147'') := mk_typed_bit \206\147' in
      match p with
      | bit n => (bit (S n), None :: \206\147'')
      end
  end.
Fixpoint mk_typed_qubit (\206\147 : Ctx) : Pat Qubit * Ctx :=
  match \206\147 with
  | [] => (qubit O, [Some Qubit])
  | None :: \206\147' => (qubit O, [Some Qubit])
  | Some W :: \206\147' =>
      let (p, \206\147'') := mk_typed_qubit \206\147' in
      match p with
      | qubit n => (qubit (S n), None :: \206\147'')
      end
  end.
Definition dummy_ctx : Ctx.
exact [].
Qed.
Definition dummy_pat {W} : Pat W.
(induction W).
-
exact (qubit O).
-
exact (bit O).
-
exact unit.
-
(constructor; auto).
Qed.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma typed_pat_merge_valid :
  forall W \206\147 \206\147' (p : Pat W), (p, \206\147') = mk_typed_pat W \206\147 -> is_valid (\206\147 \226\139\147 \206\147').
Proof.
(induction W).
-
(induction \206\147; intros \206\147' p H).
(simpl).
validate.
(destruct a).
+
(simpl in H).
dependent destruction p.
(destruct (mk_typed_qubit \206\147) as [p1 \206\1471] eqn:E1).
dependent destruction p1.
(inversion H; subst).
symmetry in E1.
(simpl in IH\206\147).
specialize (IH\206\147 _ _ E1).
(simpl in *).
(destruct (merge' \206\147 \206\1471)).
invalid_contradiction.
validate.
+
(simpl in *).
(inversion H; subst).
replace (merge' \206\147 []) with Valid \206\147 \226\139\147 \226\136\133 by easy.
(rewrite merge_nil_r).
validate.
-
(induction \206\147; intros \206\147' p H).
(simpl).
validate.
(destruct a).
+
(simpl in H).
dependent destruction p.
(destruct (mk_typed_bit \206\147) as [p1 \206\1471] eqn:E1).
dependent destruction p1.
(inversion H; subst).
symmetry in E1.
(simpl in IH\206\147).
specialize (IH\206\147 _ _ E1).
(simpl).
(destruct (merge' \206\147 \206\1471)).
invalid_contradiction.
validate.
+
(simpl in H).
(inversion H; subst).
(simpl).
replace (merge' \206\147 []) with Valid \206\147 \226\139\147 \226\136\133 by easy.
(rewrite merge_nil_r).
validate.
-
(intros \206\147 \206\147' p H).
(simpl in H).
(inversion H).
(rewrite merge_nil_r).
validate.
-
(intros \206\147 \206\147' p H).
(simpl in H).
(destruct (mk_typed_pat W1 \206\147) as [p1 \206\1471] eqn:E1).
symmetry in E1.
(destruct (IHW1 _ _ _ E1) as [\206\1471' M1]).
(simpl in M1).
(rewrite M1 in H).
(destruct (mk_typed_pat W2 \206\1471') as [p2 \206\1472] eqn:E2).
symmetry in E2.
(destruct (IHW2 _ _ _ E2) as [\206\1472' M2]).
(simpl in M2).
replace (merge' \206\147 \206\1471) with \206\147 \226\139\147 \206\1471 in M1 by easy.
replace (merge' \206\1471' \206\1472) with \206\1471' \226\139\147 \206\1472 in M2 by easy.
(assert (V2 : is_valid (\206\1471' \226\139\147 \206\1472))).
(rewrite M2; validate).
(assert (V12 : is_valid (\206\1471 \226\139\147 \206\1472))).
(rewrite <- M1 in V2; validate).
(simpl in V12).
(destruct (merge' \206\1471 \206\1472) as [| \206\14712] eqn:E12).
invalid_contradiction.
(inversion H; subst).
replace (merge' \206\1471 \206\1472) with \206\1471 \226\139\147 \206\1472 in E12 by easy.
symmetry in M1, M2, E12.
(rewrite M1, E12 in *).
validate.
Qed.
Lemma typed_bit_typed :
  forall \206\147 p \206\147', (p, \206\147') = mk_typed_bit \206\147 -> \206\147' \226\138\162 p :Pat.
Proof.
(induction \206\147 as [| o \206\147]).
-
(intros p \206\147' H).
(simpl in H).
(inversion H; subst).
constructor.
(apply singleton_singleton).
-
(intros p \206\147' H).
(destruct o).
+
dependent destruction p.
(simpl in H).
(destruct (mk_typed_bit \206\147) as [p \206\147'']).
dependent destruction p.
(inversion H).
subst.
specialize (IH\206\147 (bit v) \206\147'' eq_refl).
(inversion IH\206\147; subst).
constructor.
constructor.
easy.
+
(simpl in H).
(inversion H; subst).
constructor.
constructor.
Qed.
Lemma typed_qubit_typed :
  forall \206\147 p \206\147', (p, \206\147') = mk_typed_qubit \206\147 -> \206\147' \226\138\162 p :Pat.
Proof.
(induction \206\147 as [| o \206\147]).
-
(intros p \206\147' H).
(simpl in H).
(inversion H; subst).
constructor.
(apply singleton_singleton).
-
(intros p \206\147' H).
(destruct o).
+
dependent destruction p.
(simpl in H).
(destruct (mk_typed_qubit \206\147) as [p \206\147'']).
dependent destruction p.
(inversion H).
subst.
specialize (IH\206\147 (qubit v) \206\147'' eq_refl).
(inversion IH\206\147; subst).
constructor.
constructor.
easy.
+
(simpl in H).
(inversion H; subst).
constructor.
constructor.
Qed.
Lemma typed_pat_typed :
  forall W \206\147 (p : Pat W) \206\147', (p, \206\147') = mk_typed_pat W \206\147 -> \206\147' \226\138\162 p :Pat.
Proof.
(induction W; intros \206\147 p \206\147' H).
-
(eapply (typed_qubit_typed \206\147); easy).
-
(eapply (typed_bit_typed \206\147); easy).
-
dependent destruction p.
(simpl in H).
(inversion H; subst).
constructor.
-
(simpl in H).
(destruct (mk_typed_pat W1 \206\147) as [p1 \206\1471] eqn:E1).
symmetry in E1.
(destruct (merge' \206\147 \206\1471) as [| \206\1471'] eqn:M1).
(apply typed_pat_merge_valid in E1).
(simpl in E1).
(rewrite M1 in E1).
invalid_contradiction.
(destruct (mk_typed_pat W2 \206\1471') as [p2 \206\1472] eqn:E2).
symmetry in E2.
(destruct (merge' \206\1471 \206\1472) as [| \206\14712] eqn:M2).
(apply typed_pat_merge_valid in E2).
(rewrite <- M1 in E2).
replace (merge' \206\147 \206\1471) with \206\147 \226\139\147 \206\1471 in E2 by easy.
validate.
(simpl in H2).
(rewrite M2 in H2).
invalid_contradiction.
(inversion H).
(rewrite <- M2).
replace (merge' \206\1471 \206\1472) with \206\1471 \226\139\147 \206\1472 in * by easy.
econstructor.
(rewrite M2).
validate.
reflexivity.
(eapply IHW1).
(apply E1).
(eapply IHW2).
(apply E2).
Qed.
