Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqafu5FU"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Program.
Require Import Arith.
Require Import Omega.
Require Import Setoid.
Require Import Monad.
Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Require Export Quantum.
Require Import List.
Import ListNotations.
Set Bullet Behavior Strict Subproofs.
Global Unset Asymmetric Patterns.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation "\226\159\166 s \226\159\167" := (denote s) (at level 10).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Instance Denote_WType : (Denote WType nat) := {| denote := size_wtype |}.
Instance Denote_Ctx : (Denote Ctx nat) := {| denote := size_ctx |}.
Instance Denote_OCtx : (Denote OCtx nat) := {| denote := size_octx |}.
Fixpoint denote_unitary {W} (U : Unitary W) : Square (2 ^ \226\159\166 W \226\159\167) :=
  match U with
  | _H => hadamard
  | _X => \207\131x
  | _Y => \207\131y
  | _Z => \207\131z
  | _R_ \207\149 => phase_shift \207\149
  | ctrl g => control (denote_unitary g)
  | bit_ctrl g => control (denote_unitary g)
  end.
Instance Denote_Unitary  W: (Denote (Unitary W) (Square (2 ^ \226\159\166 W \226\159\167))) :=
 {| denote := denote_unitary |}.
Lemma unitary_gate_unitary : forall {W} (U : Unitary W), WF_Unitary (\226\159\166 U \226\159\167).
Proof.
(induction U).
+
(apply H_unitary).
+
(apply \207\131x_unitary).
+
(apply \207\131y_unitary).
+
(apply \207\131z_unitary).
+
(apply phase_unitary).
+
(simpl).
(apply control_unitary; assumption).
+
(simpl).
(apply control_unitary; assumption).
Qed.
Open Scope matrix_scope.
Close Scope circ_scope.
Print Scopes.
Lemma denote_unitary_transpose :
  forall {W} (U : Unitary W), \226\159\166 trans U \226\159\167 == (\226\159\166 U \226\159\167) \226\128\160.
Proof.
(induction U; simpl; Msimpl; try reflexivity).
-
(rewrite IHU).
reflexivity.
-
(rewrite IHU).
reflexivity.
Qed.
Instance Denote_Unitary_Correct  W: (Denote_Correct (Denote_Unitary W)) :=
 {|
 correctness := fun A => WF_Unitary A;
 denote_correct := fun U => unitary_gate_unitary U |}.
Definition denote_gate' (safe : bool) n {w1} {w2} (g : Gate w1 w2) :
  Superoperator (2 ^ \226\159\166 w1 \226\159\167 * 2 ^ n) (2 ^ \226\159\166 w2 \226\159\167 * 2 ^ n) :=
  match g with
  | U u => super (\226\159\166 u \226\159\167 \226\138\151 I (2 ^ n))
  | BNOT => super (\207\131x \226\138\151 I (2 ^ n))
  | init0 => super (\226\136\1630\226\159\169 \226\138\151 I (2 ^ n))
  | init1 => super (\226\136\1631\226\159\169 \226\138\151 I (2 ^ n))
  | new0 => super (\226\136\1630\226\159\169 \226\138\151 I (2 ^ n))
  | new1 => super (\226\136\1631\226\159\169 \226\138\151 I (2 ^ n))
  | meas => Splus (super (\226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I (2 ^ n))) (super (\226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I (2 ^ n)))
  | measQ => Splus (super (\226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I (2 ^ n))) (super (\226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I (2 ^ n)))
  | discard => Splus (super (\226\159\1680\226\136\163 \226\138\151 I (2 ^ n))) (super (\226\159\1681\226\136\163 \226\138\151 I (2 ^ n)))
  | assert0 =>
      if safe
      then Splus (super (\226\159\1680\226\136\163 \226\138\151 I (2 ^ n))) (super (\226\159\1681\226\136\163 \226\138\151 I (2 ^ n)))
      else super (\226\159\1680\226\136\163 \226\138\151 I (2 ^ n))
  | assert1 =>
      if safe
      then Splus (super (\226\159\1680\226\136\163 \226\138\151 I (2 ^ n))) (super (\226\159\1681\226\136\163 \226\138\151 I (2 ^ n)))
      else super (\226\159\1681\226\136\163 \226\138\151 I (2 ^ n))
  end.
Definition denote_gate safe {W1} {W2} (g : Gate W1 W2) :
  Superoperator (2 ^ \226\159\166 W1 \226\159\167) (2 ^ \226\159\166 W2 \226\159\167) := denote_gate' safe 0 g.
Lemma pow_gt_0 : forall n, (2 ^ n > O)%nat.
Proof.
(induction n; auto).
(simpl).
(apply gt_trans with (2 ^ n)%nat; auto).
omega.
Qed.
Close Scope circ_scope.
Lemma discard_qubit_correct :
  forall \207\129 : Matrix 2 2,
  Mixed_State \207\129 -> Mixed_State (\226\159\1680\226\136\163 \195\151 \207\129 \195\151 \226\136\1630\226\159\169 .+ \226\159\1681\226\136\163 \195\151 \207\129 \195\151 \226\136\1631\226\159\169).
Proof.
(intros \207\129 M).
(apply mixed_state_compat with (A := \207\129 0%nat 0%nat .* I 1 .+ \207\129 1%nat 1%nat .* I 1);
  try lma).
specialize (mixed_state_diag_real _ _ Nat.lt_0_2 M) as R0.
specialize (mixed_state_diag_real _ _ Nat.lt_1_2 M) as R1.
specialize (mixed_state_diag_in01 _ 0%nat M Nat.lt_0_2) as IN0.
specialize (mixed_state_diag_in01 _ 1%nat M Nat.lt_1_2) as IN1.
specialize (mixed_state_trace_1 _ M) as TR1.
replace (\207\129 0%nat 0%nat) with RtoC (fst (\207\129 0%nat 0%nat)) by lca.
replace (\207\129 1%nat 1%nat) with RtoC (fst (\207\129 1%nat 1%nat)) by lca.
(apply mixed_state_cond; simpl; try lra).
-
(inversion TR1; lca).
-
(constructor; apply pure_id1).
-
(constructor; apply pure_id1).
Qed.
Close Scope circ_scope.
Lemma WF_Unitary_compat :
  forall n (A B : Square n), A == B -> WF_Unitary A <-> WF_Unitary B.
Proof.
(unfold WF_Unitary; split; intros).
-
(rewrite <- H).
assumption.
-
(rewrite H).
assumption.
Qed.
Add Parametric Morphism  n : @WF_Unitary n with signature 
 mat_equiv ==> iff as wfu_mor.
Proof.
(intros; apply WF_Unitary_compat; easy).
Qed.
Lemma kron_1_r' : forall {m n : nat} (A : Matrix m n), A \226\138\151 I 1 = A.
Proof.
(intros m n A).
(unfold I, kron).
(apply functional_extensionality; intros).
(apply functional_extensionality; intros).
(rewrite 2!Nat.div_1_r).
(rewrite 2!Nat.mod_1_r).
(simpl; lca).
Qed.
Lemma kron_assoc' :
  forall {m n p q r s : nat} (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  p <> O -> q <> O -> r <> O -> s <> O -> A \226\138\151 B \226\138\151 C = A \226\138\151 (B \226\138\151 C).
Proof.
(intros).
(apply functional_extensionality; intros).
(apply functional_extensionality; intros).
(remember (A \226\138\151 B \226\138\151 C) as LHS).
(unfold kron).
(rewrite (mult_comm p r)  at 1 2).
(rewrite (mult_comm q s)  at 1 2).
(rewrite <- 2!Nat.div_div by assumption).
(rewrite <- 2!div_mod by assumption).
(rewrite 2!mod_product by assumption).
(rewrite Cmult_assoc).
subst.
reflexivity.
Qed.
Lemma denote_gate_correct :
  forall {W1} {W2} (g : Gate W1 W2), WF_Superoperator (denote_gate true g).
Proof.
(unfold WF_Superoperator).
(intros).
(induction g).
+
(simpl).
(rewrite Nat.mul_1_r).
(apply mixed_unitary; trivial).
(rewrite kron_1_r').
(apply unitary_gate_unitary).
+
(simpl).
(apply mixed_unitary).
lma.
assumption.
+
(simpl in *).
(rewrite (kron_1_r \226\136\1630\226\159\169)).
(unfold super).
(rewrite (mixed_dim1 \207\129); trivial).
(rewrite Mmult_1_r).
(constructor; apply pure0).
+
(simpl in *).
(rewrite (kron_1_r \226\136\1631\226\159\169)).
(unfold super).
(rewrite (mixed_dim1 \207\129); trivial).
(rewrite Mmult_1_r).
(constructor; apply pure1).
+
(simpl in *).
(rewrite (kron_1_r \226\136\1630\226\159\169)).
(unfold super).
(rewrite (mixed_dim1 \207\129); trivial).
(rewrite Mmult_1_r).
(constructor; apply pure0).
+
(simpl in *).
(rewrite (kron_1_r \226\136\1631\226\159\169)).
(unfold super).
(rewrite (mixed_dim1 \207\129); trivial).
(rewrite Mmult_1_r).
(constructor; apply pure1).
+
(simpl in *).
(unfold Splus).
(rewrite (kron_1_r \226\136\1630\226\159\169\226\159\1680\226\136\163)).
(rewrite (kron_1_r \226\136\1631\226\159\169\226\159\1681\226\136\163)).
(unfold super).
Msimpl.
mat_replace \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 \207\129 \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 with \207\129 0%nat 0%nat .* \226\136\1630\226\159\169\226\159\1680\226\136\163 by lma.
mat_replace \226\136\1631\226\159\169\226\159\1681\226\136\163 \195\151 \207\129 \195\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 with \207\129 1%nat 1%nat .* \226\136\1631\226\159\169\226\159\1681\226\136\163 by lma.
specialize (mixed_state_diag_real _ _ Nat.lt_0_2 H) as R0.
specialize (mixed_state_diag_real _ _ Nat.lt_1_2 H) as R1.
specialize (mixed_state_diag_in01 _ 0%nat H Nat.lt_0_2) as IN0.
specialize (mixed_state_diag_in01 _ 1%nat H Nat.lt_1_2) as IN1.
specialize (mixed_state_trace_1 _ H) as TR1.
replace (\207\129 0%nat 0%nat) with RtoC (fst (\207\129 0%nat 0%nat)) by lca.
replace (\207\129 1%nat 1%nat) with RtoC (fst (\207\129 1%nat 1%nat)) by lca.
(apply mixed_state_cond; simpl; try lra).
-
(inversion TR1; lca).
-
(constructor; apply pure0).
-
(constructor; apply pure1).
+
(simpl in *).
(unfold Splus).
(rewrite (kron_1_r \226\136\1630\226\159\169\226\159\1680\226\136\163)).
(rewrite (kron_1_r \226\136\1631\226\159\169\226\159\1681\226\136\163)).
(unfold super).
Msimpl.
mat_replace \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 \207\129 \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 with \207\129 0%nat 0%nat .* \226\136\1630\226\159\169\226\159\1680\226\136\163 by lma.
mat_replace \226\136\1631\226\159\169\226\159\1681\226\136\163 \195\151 \207\129 \195\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 with \207\129 1%nat 1%nat .* \226\136\1631\226\159\169\226\159\1681\226\136\163 by lma.
specialize (mixed_state_diag_real _ _ Nat.lt_0_2 H) as R0.
specialize (mixed_state_diag_real _ _ Nat.lt_1_2 H) as R1.
specialize (mixed_state_diag_in01 _ 0%nat H Nat.lt_0_2) as IN0.
specialize (mixed_state_diag_in01 _ 1%nat H Nat.lt_1_2) as IN1.
specialize (mixed_state_trace_1 _ H) as TR1.
replace (\207\129 0%nat 0%nat) with RtoC (fst (\207\129 0%nat 0%nat)) by lca.
replace (\207\129 1%nat 1%nat) with RtoC (fst (\207\129 1%nat 1%nat)) by lca.
(apply mixed_state_cond; simpl; try lra).
-
(inversion TR1; lca).
-
(constructor; apply pure0).
-
(constructor; apply pure1).
+
(simpl in *).
(unfold Splus).
(rewrite (kron_1_r \226\159\1680\226\136\163)).
(rewrite (kron_1_r \226\159\1681\226\136\163)).
(unfold super).
Msimpl.
(apply mixed_state_trace_1 in H).
(unfold trace in H).
(simpl in H).
(rewrite Cplus_0_l in H).
mat_replace \226\159\1680\226\136\163 \195\151 \207\129 \195\151 \226\136\1630\226\159\169 .+ \226\159\1681\226\136\163 \195\151 \207\129 \195\151 \226\136\1631\226\159\169 with I 1.
2: {
by_cell.
autounfold with U_db.
(simpl).
autorewrite with C_db.
easy.
}
constructor.
(apply pure_id1).
+
(simpl in *).
(unfold Splus).
(rewrite (kron_1_r \226\159\1680\226\136\163)).
(rewrite (kron_1_r \226\159\1681\226\136\163)).
(unfold super).
Msimpl.
(apply mixed_state_trace_1 in H).
(unfold trace in H).
(simpl in H).
(rewrite Cplus_0_l in H).
mat_replace \226\159\1680\226\136\163 \195\151 \207\129 \195\151 \226\136\1630\226\159\169 .+ \226\159\1681\226\136\163 \195\151 \207\129 \195\151 \226\136\1631\226\159\169 with I 1.
2: {
by_cell.
autounfold with U_db.
(simpl).
autorewrite with C_db.
easy.
}
constructor.
(apply pure_id1).
+
(simpl in *).
(unfold Splus).
(rewrite (kron_1_r \226\159\1680\226\136\163)).
(rewrite (kron_1_r \226\159\1681\226\136\163)).
(unfold super).
Msimpl.
(apply mixed_state_trace_1 in H).
(unfold trace in H).
(simpl in H).
(rewrite Cplus_0_l in H).
mat_replace \226\159\1680\226\136\163 \195\151 \207\129 \195\151 \226\136\1630\226\159\169 .+ \226\159\1681\226\136\163 \195\151 \207\129 \195\151 \226\136\1631\226\159\169 with I 1.
2: {
by_cell.
autounfold with U_db.
(simpl).
autorewrite with C_db.
easy.
}
constructor.
(apply pure_id1).
Qed.
Instance Denote_Gate  W1 W2:
 (Denote (Gate W1 W2) (Superoperator (2 ^ \226\159\166 W1 \226\159\167) (2 ^ \226\159\166 W2 \226\159\167))) :=
 {| denote := denote_gate true |}.
Instance Denote_Gate_Correct  W1 W2: (Denote_Correct (Denote_Gate W1 W2)) :=
 {| correctness := WF_Superoperator; denote_correct := denote_gate_correct |}.
Fixpoint swap_list_aux (m n : nat) (l : list (nat * nat)) : 
Square (2 ^ n) :=
  match m with
  | 0 => I (2 ^ n)
  | S m' =>
      match l with
      | nil => I (2 ^ n)
      | cons (a, b) xs =>
          swap_two n a b
          \195\151 swap_list_aux m' n
              (map (fun z => if a =? snd z then (fst z, b) else z) xs)
      end
  end.
Definition zip_to (m n : nat) (l : list nat) := combine (seq m n) l.
Eval vm_compute in zip_to 2 5 [1; 2; 3]%nat.
Definition swap_list (n : nat) (l : list nat) : Square (2 ^ n) :=
  swap_list_aux n n (zip_to 0 n l).
Lemma swap_list_swap : swap_list 2 [S O] == swap.
Proof.
(simpl).
(unfold swap_list, swap_list_aux).
(simpl).
(rewrite Mmult_1_r).
(apply swap_two_base).
Qed.
Definition pad {m} n (A : Square (2 ^ m)) : Square (2 ^ n) := A \226\138\151 I (2 ^ (n - m)).
Require Import Setoid.
Add Parametric Morphism  m n : @pad m n with signature mat_equiv ==> mat_equiv as
 pad_mor.
Proof.
(intros).
(unfold pad).
(unfold kron).
(intros i j Hi Hj).
(rewrite H).
reflexivity.
-
(bdestruct\206\169 (m <=? n)).
(apply Nat.div_lt_upper_bound).
(apply Nat.pow_nonzero; lia).
unify_pows_two.
(rewrite Nat.sub_add; lia).
(rewrite not_le_minus_0 by lia).
(rewrite Nat.div_1_r).
(eapply Nat.lt_trans).
(apply Hi).
(apply Nat.pow_lt_mono_r; lia).
-
(bdestruct\206\169 (m <=? n)).
(apply Nat.div_lt_upper_bound).
(apply Nat.pow_nonzero; lia).
unify_pows_two.
(rewrite Nat.sub_add; lia).
(rewrite not_le_minus_0 by lia).
(rewrite Nat.div_1_r).
(eapply Nat.lt_trans).
(apply Hj).
(apply Nat.pow_lt_mono_r; lia).
Qed.
Lemma pad_nothing : forall m A, @pad m m A == A.
Proof.
(intros).
(unfold pad).
(rewrite Nat.sub_diag).
(simpl).
(unfold kron).
(intros i j _ _).
(rewrite 2!Nat.div_1_r, 2!Nat.mod_1_r).
lca.
Qed.
Hint Resolve Mmult_unitary kron_unitary id_unitary swap_unitary: U_db.
Lemma swap_to_0_aux_unitary :
  forall n i, (i + 1 < n)%nat -> WF_Unitary (swap_to_0_aux n i).
Proof.
(intros n i H).
(induction i; simpl).
-
specialize (kron_unitary swap (I (2 ^ (n - 2))))%nat.
replace (2 * 2 * 2 ^ (n - 2))%nat with (2 ^ 1 * 2 ^ 1 * 2 ^ (n - 2))%nat by easy.
replace (2 ^ 1 * 2 ^ 1 * 2 ^ (n - 2))%nat with (2 ^ n)%nat by unify_pows_two.
(intros KU).
(apply KU).
(apply swap_unitary).
(apply id_unitary).
-
replace (2 ^ n)%nat with ((2 ^ i + (2 ^ i + 0)) * 4 * 2 ^ (n - S i - 2))%nat
 by unify_pows_two.
(repeat
  (try apply Mmult_unitary; try apply kron_unitary; try apply id_unitary;
    try apply swap_unitary)).
replace ((2 ^ i + (2 ^ i + 0)) * 4 * 2 ^ (n - S i - 2))%nat with 
 (2 ^ n)%nat by unify_pows_two.
(apply IHi; lia).
Qed.
Lemma swap_to_0_unitary : forall i n, (i < n)%nat -> WF_Unitary (swap_to_0 n i).
Proof.
(intros i n L).
(unfold swap_to_0).
(destruct i).
(apply id_unitary).
(apply swap_to_0_aux_unitary).
lia.
Qed.
Lemma swap_two_aux_unitary :
  forall n i j, (i < j < n)%nat -> WF_Unitary (swap_two_aux n i j).
Proof.
(intros n i).
gen n.
(induction i).
-
(intros; simpl).
(apply swap_to_0_unitary).
lia.
-
(intros n j [Lij Ljn]).
(simpl).
(destruct n; try lia).
(rewrite <- (Nat.add_1_l n)).
(rewrite minus_plus).
(apply kron_unitary).
(apply id_unitary).
(apply IHi).
lia.
Qed.
Lemma swap_two_unitary :
  forall n i j, (i < n)%nat -> (j < n)%nat -> WF_Unitary (swap_two n i j).
Proof.
(intros n i j Lin Ljn).
(unfold swap_two).
(bdestruct (i =? j)).
(apply id_unitary).
(bdestruct (i <? j)).
(apply swap_two_aux_unitary).
lia.
(apply swap_two_aux_unitary).
lia.
Qed.
Lemma swap_list_aux_unitary :
  forall m n l,
  (forall i j, In (i, j) l -> (i < n)%nat /\ (j < n)%nat) ->
  (m <= n)%nat -> WF_Unitary (swap_list_aux m n l).
Proof.
(intros m n l Lall Lmn).
gen l.
(induction m; intros l Lall).
-
(simpl).
(apply id_unitary).
-
(simpl).
(destruct l).
(apply id_unitary).
(destruct p).
(apply Mmult_unitary).
(destruct (Lall n0 n1); simpl; auto).
(apply swap_two_unitary; easy).
(apply IHm).
omega.
(intros x y IN).
split.
+
(induction l).
easy.
(destruct IN).
(destruct a).
(simpl in *).
(destruct (n0 =? n3)).
(inversion H; subst).
clear H.
(edestruct Lall).
right.
left.
reflexivity.
easy.
(inversion H; subst).
clear H.
(edestruct Lall).
right.
left.
reflexivity.
easy.
(apply IHl).
(intros).
(apply Lall).
(destruct H0).
left.
easy.
right.
right.
easy.
(apply H).
+
(induction l).
easy.
(destruct IN).
(destruct a).
(simpl in *).
(destruct (n0 =? n3)).
(inversion H; subst).
clear H.
(edestruct Lall).
left.
reflexivity.
easy.
(inversion H; subst).
clear H.
(edestruct Lall).
right.
left.
reflexivity.
easy.
(apply IHl).
(intros).
(apply Lall).
(destruct H0).
left.
easy.
right.
right.
easy.
(apply H).
Qed.
Lemma swap_list_unitary :
  forall n l,
  (length l <= n)%nat ->
  (forall x, In x l -> x < n)%nat -> WF_Unitary (swap_list n l).
Proof.
(intros n l len Lall).
(unfold swap_list).
(apply swap_list_aux_unitary; try omega).
(intros i j IN).
split.
-
(unfold zip_to in *).
(apply in_combine_l in IN).
(apply in_seq in IN).
omega.
-
(unfold zip_to in *).
(apply in_combine_r in IN).
auto.
Qed.
Definition dummy_mat {m} {n} : Matrix m n.
exact Zero.
Qed.
Definition dummy_so {m} {n} : Superoperator m n.
exact (fun _ => dummy_mat).
Qed.
Definition super_Zero {m} {n} : Superoperator m n := fun _ => Zero.
Fixpoint ctrls_to_list {W} (lb : list bool) (l : list nat) 
(g : Unitary W) {struct g} : nat * list bool * Unitary Qubit :=
  match g with
  | ctrl g' =>
      match l with
      | n :: l' =>
          let (res, u) := ctrls_to_list lb l' g' in
          let (k, lb') := res in (k, update_at lb' n true, u)
      | _ => (O, [], _X)
      end
  | bit_ctrl g' =>
      match l with
      | n :: l' =>
          let (res, u) := ctrls_to_list lb l' g' in
          let (k, lb') := res in (k, update_at lb' n true, u)
      | _ => (O, [], _X)
      end
  | u => match l with
         | k :: l' => (k, lb, u)
         | _ => (O, [], _X)
         end
  end.
Fixpoint ctrl_list_to_unitary_r (r : list bool) (u : Square 2) :
Square (2 ^ (length r + 1)) :=
  match r with
  | false :: r' => ctrl_list_to_unitary_r r' u \226\138\151 I 2
  | true :: r' => ctrl_list_to_unitary_r r' u \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 .+ I _ \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163
  | [] => u
  end.
Fixpoint ctrl_list_to_unitary (l r : list bool) (u : Square 2) :
Square (2 ^ (length l + length r + 1)) :=
  match l with
  | false :: l' => I 2 \226\138\151 ctrl_list_to_unitary l' r u
  | true :: l' => \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 ctrl_list_to_unitary l' r u .+ \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I _
  | [] => ctrl_list_to_unitary_r r u
  end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition apply_U {W} (n : nat) (U : Unitary W) (l : list nat) :
  Superoperator (2 ^ n) (2 ^ n) := super (apply_unitary n U l).
Lemma id_kron' : forall m n : nat, n <> O -> I m \226\138\151 I n = I (m * n).
Proof.
(intros).
(unfold I, kron).
(apply functional_extensionality; intros i).
(apply functional_extensionality; intros j).
(bdestruct (i =? j)).
-
subst.
(rewrite <- 2!beq_nat_refl).
lca.
-
(bdestruct (i / n =? j / n); simpl; try lca).
(bdestruct (i mod n =? j mod n); simpl; try lca).
(contradict H0).
(rewrite (Nat.div_mod i n) by assumption).
(rewrite (Nat.div_mod j n) by assumption).
(rewrite H1, H2).
reflexivity.
Qed.
Lemma ctrl_list_to_unitary_r_false :
  forall n (u : Matrix 2 2),
  ctrl_list_to_unitary_r (repeat false n) u == u \226\138\151 I (2 ^ n).
Proof.
(induction n; intros).
-
(simpl).
Msimpl.
(rewrite (kron_1_r u)).
reflexivity.
-
(intros).
(simpl).
specialize (IHn u).
(remember (ctrl_list_to_unitary_r (repeat false n) u) as A).
gen A.
(rewrite repeat_length).
(rewrite (plus_comm n)).
(rewrite Nat.pow_add_r).
(intros).
clear HeqA.
restore_dims.
(rewrite IHn).
(rewrite kron_assoc).
(restore_dims; rewrite id_kron).
replace (2 ^ n * 2)%nat with (2 ^ n + (2 ^ n + 0))%nat by unify_pows_two.
reflexivity.
Qed.
Lemma ctrl_list_to_unitary_false :
  forall m n (u : Matrix 2 2),
  ctrl_list_to_unitary (repeat false m) (repeat false n) u ==
  I (2 ^ m) \226\138\151 u \226\138\151 I (2 ^ n).
Proof.
(induction m; intros).
-
(simpl).
(rewrite ctrl_list_to_unitary_r_false).
(rewrite repeat_length).
restore_dims.
(rewrite (kron_1_l u)).
reflexivity.
-
(simpl in *).
(rewrite IHm by easy).
(repeat rewrite repeat_length).
(progress restore_dims).
specialize (pow_gt_0 m) as Gm.
specialize (pow_gt_0 n) as Gn.
(repeat rewrite <- kron_assoc'; try lia).
restore_dims.
(rewrite id_kron).
reflexivity.
Qed.
Lemma ctrls_to_list_empty : forall W lb u, @ctrls_to_list W lb [] u = (O, [], _X).
Proof.
(destruct u; easy).
Qed.
Lemma denote_ctrls_empty :
  forall W (n : nat) (u : Unitary W), denote_ctrls n u [] = \207\131x.
Proof.
(destruct u; compute; easy).
Qed.
Opaque rev skipn.
Lemma denote_ctrls_qubit :
  forall n (u : Unitary Qubit) k,
  (k < n)%nat -> denote_ctrls n u [k] == I (2 ^ k) \226\138\151 \226\159\166 u \226\159\167 \226\138\151 I (2 ^ (n - k - 1)).
Proof.
(intros n u k L).
(remember Qubit as W).
(induction u; try discriminate).
all:
 (unfold denote_ctrls; simpl;
   rewrite firstn_repeat_le, skipn_repeat, rev_repeat by lia; replace
   (n - k - 1)%nat with (n - S k)%nat by lia; restore_dims
   repeat rewrite repeat_length; unify_pows_two; try lia;
   apply ctrl_list_to_unitary_false).
Qed.
Transparent rev skipn.
Lemma ctrl_list_to_unitary_r_unitary :
  forall r (u : Square 2), WF_Unitary u -> WF_Unitary (ctrl_list_to_unitary_r r u).
Proof.
(intros r u Uu).
(induction r; auto).
(simpl).
(destruct a).
-
(simpl).
(assert
  (H :
   forall n (U : Square n), WF_Unitary U -> WF_Unitary (U \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 .+ I n \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163))).
(intros n U UU).
(unfold WF_Unitary in *).
Msimpl.
(rewrite Mmult_plus_dist_r, Mmult_plus_dist_l).
(rewrite Mmult_plus_dist_l).
Msimpl.
(rewrite UU).
mat_replace \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 with @Zero 2 2 by lma.
mat_replace \226\136\1631\226\159\169\226\159\1681\226\136\163 \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 with @Zero 2 2 by lma.
Msimpl.
(rewrite <- kron_plus_dist_l).
mat_replace \226\136\1631\226\159\169\226\159\1681\226\136\163 \195\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 .+ \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 with I 2 by lma.
(rewrite id_kron).
reflexivity.
specialize (H _ (ctrl_list_to_unitary_r r u)).
(rewrite Nat.mul_comm in H).
(apply H).
(apply IHr).
-
specialize (kron_unitary _ (I 2) IHr) as H.
(rewrite Nat.mul_comm in H).
(apply H).
(apply id_unitary).
Qed.
Lemma ctrl_list_to_unitary_unitary :
  forall l r (u : Square 2), WF_Unitary u -> WF_Unitary (ctrl_list_to_unitary l r u).
Proof.
(intros l r u Uu).
(induction l).
-
(simpl).
(apply ctrl_list_to_unitary_r_unitary).
easy.
-
(simpl).
(destruct a).
+
(simpl).
(assert
  (H :
   forall n (U : Square n), WF_Unitary U -> WF_Unitary (\226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 U .+ \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I n))).
(intros n U UU).
(unfold WF_Unitary in *).
Msimpl.
(rewrite Mmult_plus_dist_l, Mmult_plus_dist_r).
(rewrite Mmult_plus_dist_r).
Msimpl.
(rewrite UU).
mat_replace \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 with @Zero 2 2 by lma.
mat_replace \226\136\1631\226\159\169\226\159\1681\226\136\163 \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 with @Zero 2 2 by lma.
Msimpl.
(rewrite <- kron_plus_dist_r).
mat_replace \226\136\1631\226\159\169\226\159\1681\226\136\163 \195\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 .+ \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 with I 2 by lma.
(rewrite id_kron).
reflexivity.
specialize (H _ (ctrl_list_to_unitary l r u)).
(apply H).
(apply IHl).
+
specialize (kron_unitary _ _ (id_unitary 2) IHl) as H.
(apply H).
Qed.
Lemma ctrls_to_list_spec :
  forall W l (g : Unitary W) k lb lb' u,
  (length l = \226\159\166 W \226\159\167)%nat ->
  ctrls_to_list lb l g = (k, lb', u) -> length lb' = length lb /\ In k l.
Proof.
(intros W l g).
gen l.
(induction g; simpl in *; intros l k lb lb' u L H).
-
(destruct l; inversion L).
(inversion H; subst).
(simpl; split; auto).
-
(destruct l; inversion L).
(inversion H; subst).
(simpl; split; auto).
-
(destruct l; inversion L).
(inversion H; subst).
(simpl; split; auto).
-
(destruct l; inversion L).
(inversion H; subst).
(simpl; split; auto).
-
(destruct l; inversion L).
(inversion H; subst).
(simpl; split; auto).
-
(destruct l; inversion L).
(destruct (ctrls_to_list lb l g) as [[k' lb''] u'] eqn:E).
(inversion H; subst).
(rewrite update_length).
specialize (IHg l k lb lb'' u H1 E) as [LE I].
(simpl; split; auto).
-
(destruct l; inversion L).
(destruct (ctrls_to_list lb l g) as [[k' lb''] u'] eqn:E).
(inversion H; subst).
(rewrite update_length).
specialize (IHg l k lb lb'' u H1 E) as [LE I].
(simpl; split; auto).
Qed.
Lemma denote_ctrls_unitary :
  forall W n (g : Unitary W) l,
  (forall x, In x l -> x < n)%nat ->
  (length l = \226\159\166 W \226\159\167)%nat -> WF_Unitary (denote_ctrls n g l).
Proof.
(intros W n g l H H0).
(unfold denote_ctrls).
(simpl).
(destruct (ctrls_to_list (repeat false n) l g) as [[k lb] u] eqn:E).
(apply ctrls_to_list_spec in E as [L I]; trivial).
specialize (H k I).
specialize
 (ctrl_list_to_unitary_unitary (firstn k lb) (rev (skipn (S k) lb)) (\226\159\166 u \226\159\167)) as U.
(assert (E : (length (firstn k lb) + length (rev (skipn (S k) lb)) + 1 = n)%nat)).
(rewrite firstn_length_le).
(rewrite rev_length).
(rewrite skipn_length).
(rewrite L, repeat_length).
omega.
(rewrite L, repeat_length).
omega.
(rewrite E in U).
(apply U).
(apply (unitary_gate_unitary u)).
Qed.
Lemma denote_ctrls_transpose_qubit :
  forall (n : nat) (u : Unitary Qubit) (li : list nat),
  (forall x, In x li -> x < n)%nat ->
  denote_ctrls n (trans u) li == (denote_ctrls n u li) \226\128\160.
Proof.
(intros).
(destruct li as [| k li]).
{
(rewrite 2!denote_ctrls_empty).
autounfold with U_db.
(intros i j _ _).
(rewrite (if_dist _ _ _ Cconj)).
autorewrite with C_db.
(rewrite plus_comm).
easy.
}
specialize (H _ (in_eq _ _)).
dependent destruction u.
all:
 (simpl; unfold denote_ctrls, ctrls_to_list;
   rewrite skipn_repeat, rev_repeat, firstn_repeat; restore_dims
   repeat rewrite repeat_length; unify_pows_two; lia;
   repeat rewrite ctrl_list_to_unitary_false; restore_dims
   repeat rewrite repeat_length; unify_pows_two; lia; simpl; Msimpl; reflexivity).
Qed.
Lemma ctrls_to_list_transpose :
  forall W lb li (u : Unitary W) n lb' u',
  ctrls_to_list lb li u = (n, lb', u') ->
  ctrls_to_list lb li (trans u) = (n, lb', trans u').
Proof.
(induction W; intros lb li u n lb' u' H; try (solve [ inversion u ])).
-
(destruct li as [| k li]).
(rewrite ctrls_to_list_empty in *).
(inversion H; subst).
easy.
(dependent destruction u; simpl in *; inversion H; subst; Msimpl; easy).
-
clear IHW1.
(destruct li as [| k li]).
(rewrite ctrls_to_list_empty in *).
(inversion H; subst).
easy.
dependent destruction u.
+
(simpl in *).
(destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E).
(apply IHW2 in E).
(rewrite E).
(inversion H; subst).
easy.
+
(simpl in *).
(destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E).
(apply IHW2 in E).
(rewrite E).
(inversion H; subst).
easy.
Qed.
Lemma ctrl_list_to_unitary_transpose :
  forall l r u, ctrl_list_to_unitary l r (u) \226\128\160 == (ctrl_list_to_unitary l r u) \226\128\160.
Proof.
(intros l r u).
(induction l).
(simpl).
-
(induction r; try reflexivity).
(simpl).
(destruct a; Msimpl; rewrite IHr; reflexivity).
-
(simpl).
(destruct a; Msimpl; rewrite IHl; reflexivity).
Qed.
Lemma ctrl_list_to_unitary_compat :
  forall l r A A',
  A == A' -> ctrl_list_to_unitary l r A == ctrl_list_to_unitary l r A'.
Proof.
(intros).
(induction l).
(simpl).
-
(induction r; try assumption).
(simpl).
(destruct a; Msimpl; rewrite IHr; reflexivity).
-
(simpl).
(destruct a; Msimpl; rewrite IHl; reflexivity).
Qed.
Add Parametric Morphism  l r : @ctrl_list_to_unitary l r with signature
 mat_equiv ==> mat_equiv as cltu_mor.
Proof.
(intros; apply ctrl_list_to_unitary_compat; easy).
Qed.
Opaque rev skipn.
Lemma denote_ctrls_transpose :
  forall W (n : nat) (u : Unitary W) li,
  (forall x, In x li -> x < n)%nat ->
  (length li = \226\159\166 W \226\159\167)%nat -> denote_ctrls n (trans u) li == (denote_ctrls n u li) \226\128\160.
Proof.
(intros).
(unfold denote_ctrls).
(simpl).
(destruct (ctrls_to_list (repeat false n) li u) as [[j l] v] eqn:E).
(apply ctrls_to_list_transpose in E).
(rewrite E).
specialize (ctrls_to_list_spec _ _ _ _ _ _ _ H0 E) as [L I].
specialize (H _ I).
restore_dims
 repeat rewrite rev_length, skipn_length, firstn_length, L, repeat_length; lia.
(rewrite <- ctrl_list_to_unitary_transpose).
(simpl_rewrite @denote_unitary_transpose).
reflexivity.
Qed.
Transparent rev skipn.
Lemma apply_unitary_unitary :
  forall W n (u : Unitary W) l,
  length l = \226\159\166 W \226\159\167 ->
  (forall x, In x l -> x < n)%nat -> WF_Unitary (apply_unitary n u l).
Proof.
(intros W n u l L LT).
(destruct W; try (solve [ inversion u ])).
-
(simpl).
(destruct l; try (solve [ inversion L ])).
(simpl).
specialize (LT n0 (or_introl eq_refl)).
replace (2 ^ n)%nat with (2 ^ n0 * 2 * 2 ^ (n - n0 - 1))%nat by unify_pows_two.
(repeat apply kron_unitary; try apply id_unitary; try apply unitary_gate_unitary).
specialize (unitary_gate_unitary u) as UU.
(apply UU).
-
(dependent destruction u; apply denote_ctrls_unitary; auto).
Qed.
Lemma apply_U_correct :
  forall W n (U : Unitary W) l,
  length l = \226\159\166 W \226\159\167 ->
  (forall x, In x l -> x < n)%nat -> WF_Superoperator (apply_U n U l).
Proof.
(intros).
(apply super_unitary_correct; trivial).
(apply apply_unitary_unitary; easy).
Qed.
Definition apply_new0 {n} : Superoperator (2 ^ n) (2 ^ (n + 1)) :=
  super (I (2 ^ n) \226\138\151 \226\136\1630\226\159\169).
Definition apply_new1 {n} : Superoperator (2 ^ n) (2 ^ (n + 1)) :=
  super (I (2 ^ n) \226\138\151 \226\136\1631\226\159\169).
Definition apply_discard {n} (k : nat) : Superoperator (2 ^ n) (2 ^ (n - 1)) :=
  Splus (super (I (2 ^ k) \226\138\151 \226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1))))
    (super (I (2 ^ k) \226\138\151 \226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))).
Definition apply_assert0 {n} (k : nat) : Superoperator (2 ^ n) (2 ^ (n - 1)) :=
  super (I (2 ^ k) \226\138\151 \226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1))).
Definition apply_assert1 {n} (k : nat) : Superoperator (2 ^ n) (2 ^ (n - 1)) :=
  super (I (2 ^ k) \226\138\151 \226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1))).
Definition apply_meas {n} (k : nat) : Superoperator (2 ^ n) (2 ^ n) :=
  Splus (super (I (2 ^ k) \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1))))
    (super (I (2 ^ k) \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))).
Definition apply_measQ {n} (k : nat) : Superoperator (2 ^ n) (2 ^ n) :=
  Splus (super (I (2 ^ k) \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1))))
    (super (I (2 ^ k) \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))).
Definition apply_gate {n} {w1} {w2} (safe : bool) (g : Gate w1 w2) 
  (l : list nat) : Superoperator (2 ^ n) (2 ^ (n + \226\159\166 w2 \226\159\167 - \226\159\166 w1 \226\159\167)) :=
  match g with
  | U u => apply_U n u l
  | BNOT => apply_U n _X l
  | init0 | new0 => apply_new0
  | init1 | new1 => apply_new1
  | meas => apply_meas (hd O l)
  | measQ => apply_meas (hd O l)
  | discard => apply_discard (hd O l)
  | assert0 => (if safe then apply_discard else apply_assert0) (hd O l)
  | assert1 => (if safe then apply_discard else apply_assert1) (hd O l)
  end.
Definition operator_sum {m} {n} (l : list (Matrix m n)) : 
  Superoperator n m := fold_left Splus (map (fun A => super A) l) SZero.
Definition outer_sum {m} {n} (l : list (Matrix m n)) :=
  fold_left Mplus (map (fun A => (A) \226\128\160 \195\151 A) l) Zero.
Axiom
  (operator_sum_decomposition :
     forall {m} {n} (l : list (Matrix m n)),
     outer_sum l == I n <-> WF_Superoperator (operator_sum l)).
Lemma discard_superoperator :
  forall (n i j : nat) (\207\129 : Square (2 ^ n)),
  (i * j * 2 = 2 ^ n)%nat ->
  Mixed_State \207\129 ->
  Mixed_State
    (I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1630\226\159\169 \226\138\151 I j)
     .+ I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1631\226\159\169 \226\138\151 I j)).
Proof.
(intros n i j \207\129 E M).
(destruct (operator_sum_decomposition [I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j]) as [WFS _]).
(assert (OS : outer_sum [I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j] == I (i * 2 * j))).
{
(unfold outer_sum).
(simpl).
Msimpl.
(rewrite <- kron_plus_dist_r, <- kron_plus_dist_l).
mat_replace \226\136\1630\226\159\169\226\159\1680\226\136\163 .+ \226\136\1631\226\159\169\226\159\1681\226\136\163 with I 2 by lma.
(repeat rewrite id_kron).
easy.
}
specialize (WFS OS \207\129).
(unfold operator_sum, Splus, SZero, super, WF_Superoperator in WFS).
(simpl in WFS).
autorewrite with M_db_light M_db in WFS.
(apply WFS).
(rewrite <- Nat.mul_assoc, (Nat.mul_comm 2%nat), Nat.mul_assoc).
(rewrite E).
(apply M).
Qed.
Lemma measure_superoperator :
  forall (n i j : nat) (\207\129 : Square (2 ^ n)),
  (i * j * 2 = 2 ^ n)%nat ->
  Mixed_State \207\129 ->
  Mixed_State
    (I i \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I j)
     .+ I i \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I j)).
Proof.
(intros n i j \207\129 E M).
(destruct (operator_sum_decomposition [I i \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I j])
  as [WFS _]).
(assert (OS : outer_sum [I i \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I j] == I (i * 2 * j))).
{
(unfold outer_sum).
(simpl).
Msimpl.
(rewrite <- kron_plus_dist_r, <- kron_plus_dist_l).
mat_replace \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 .+ \226\136\1631\226\159\169\226\159\1681\226\136\163 \195\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 with I 2 by lma.
(repeat rewrite id_kron).
easy.
}
specialize (WFS OS \207\129).
(unfold operator_sum, Splus, SZero, super, WF_Superoperator in WFS).
(simpl in WFS).
autorewrite with M_db_light M_db in WFS.
(apply WFS).
(rewrite <- Nat.mul_assoc, (Nat.mul_comm 2%nat), Nat.mul_assoc).
(rewrite E).
(apply M).
Qed.
Lemma init0_superoperator :
  forall (n i j : nat) (\207\129 : Square (2 ^ n)),
  (i * j = 2 ^ n)%nat ->
  Mixed_State \207\129 -> Mixed_State (I i \226\138\151 \226\136\1630\226\159\169 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j)).
Proof.
(intros n i j \207\129 E M).
(destruct (operator_sum_decomposition [I i \226\138\151 \226\136\1630\226\159\169 \226\138\151 I j]) as [WFS _]).
(assert (OS : outer_sum [I i \226\138\151 \226\136\1630\226\159\169 \226\138\151 I j] == I (i * 1 * j))).
{
(unfold outer_sum).
(simpl).
Msimpl.
mat_replace \226\159\1680\226\136\163 \195\151 \226\136\1630\226\159\169 with I 1 by lma.
(repeat rewrite id_kron).
easy.
}
specialize (WFS OS \207\129).
(unfold operator_sum, Splus, SZero, super, WF_Superoperator in WFS).
(simpl in WFS).
autorewrite with M_db_light M_db in WFS.
(apply WFS).
(rewrite Nat.mul_1_r).
(rewrite E).
(apply M).
Qed.
Lemma init1_superoperator :
  forall (n i j : nat) (\207\129 : Square (2 ^ n)),
  (i * j = 2 ^ n)%nat ->
  Mixed_State \207\129 -> Mixed_State (I i \226\138\151 \226\136\1631\226\159\169 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j)).
Proof.
(intros n i j \207\129 E M).
(destruct (operator_sum_decomposition [I i \226\138\151 \226\136\1631\226\159\169 \226\138\151 I j]) as [WFS _]).
(assert (OS : outer_sum [I i \226\138\151 \226\136\1631\226\159\169 \226\138\151 I j] == I (i * 1 * j))).
{
(unfold outer_sum).
(simpl).
Msimpl.
mat_replace \226\159\1681\226\136\163 \195\151 \226\136\1631\226\159\169 with I 1 by lma.
(repeat rewrite id_kron).
easy.
}
specialize (WFS OS \207\129).
(unfold operator_sum, Splus, SZero, super, WF_Superoperator in WFS).
(simpl in WFS).
autorewrite with M_db_light M_db in WFS.
(apply WFS).
(rewrite Nat.mul_1_r).
(rewrite E).
(apply M).
Qed.
Lemma init0_end_superoperator :
  forall (n i : nat) (\207\129 : Square (2 ^ n)),
  (i = 2 ^ n)%nat -> Mixed_State \207\129 -> Mixed_State (I i \226\138\151 \226\136\1630\226\159\169 \195\151 \207\129 \195\151 (I i \226\138\151 \226\159\1680\226\136\163)).
Proof.
(intros; subst).
(rewrite <- (kron_1_r \207\129)).
Msimpl.
(apply (mixed_state_kron _ _ \207\129 \226\136\1630\226\159\169\226\159\1680\226\136\163)).
easy.
constructor.
(apply pure0).
Qed.
Lemma init1_end_superoperator :
  forall (n i : nat) (\207\129 : Square (2 ^ n)),
  (i = 2 ^ n)%nat -> Mixed_State \207\129 -> Mixed_State (I i \226\138\151 \226\136\1631\226\159\169 \195\151 \207\129 \195\151 (I i \226\138\151 \226\159\1681\226\136\163)).
Proof.
(intros; subst).
(rewrite <- (kron_1_r \207\129)).
Msimpl.
(apply (mixed_state_kron _ _ \207\129 \226\136\1631\226\159\169\226\159\1681\226\136\163)).
easy.
constructor.
(apply pure1).
Qed.
Lemma apply_discard_correct :
  forall n k, (k < n)%nat -> WF_Superoperator (@apply_discard n k).
Proof.
(intros n k L \207\129 M\207\129).
(unfold apply_discard, Splus, super).
remember_differences.
gen \207\129.
subst.
(repeat rewrite Nat.pow_add_r).
(intros).
Msimpl.
(eapply discard_superoperator).
(unify_pows_two; easy).
(restore_dims; easy).
Qed.
Lemma apply_meas_correct :
  forall n k, (k < n)%nat -> WF_Superoperator (@apply_meas n k).
Proof.
(intros n k L \207\129 M\207\129).
(unfold apply_meas).
(unfold Splus, super).
remember_differences.
gen \207\129.
subst.
(repeat rewrite Nat.pow_add_r).
(intros).
Msimpl.
(eapply measure_superoperator).
(unify_pows_two; easy).
(restore_dims; easy).
Qed.
Lemma apply_new0_correct : forall n, WF_Superoperator (@apply_new0 n).
Proof.
(intros n \207\129 M\207\129).
(unfold apply_new0, super).
gen \207\129.
(rewrite <- (Nat.mul_1_r (2 ^ n)%nat)).
(intros).
(rewrite Nat.mul_1_r).
Msimpl.
(eapply init0_end_superoperator; trivial).
(restore_dims; easy).
Qed.
Lemma apply_new1_correct : forall n, WF_Superoperator (@apply_new1 n).
Proof.
(intros n \207\129 M\207\129).
(unfold apply_new1, super).
gen \207\129.
(rewrite <- (Nat.mul_1_r (2 ^ n)%nat)).
(intros).
(rewrite Nat.mul_1_r).
Msimpl.
(eapply init1_end_superoperator; trivial).
(restore_dims; easy).
Qed.
Lemma apply_gate_correct :
  forall W1 W2 n (g : Gate W1 W2) l,
  length l = \226\159\166 W1 \226\159\167 ->
  (length l <= n)%nat ->
  (forall x, In x l -> x < n)%nat -> WF_Superoperator (@apply_gate n W1 W2 true g l).
Proof.
(intros W1 W2 n g l L1 L2 Lt).
(destruct g).
-
(simpl in *).
(rewrite <- L1).
(bdestruct\206\169 (length l <=? n)).
replace (n + length l - length l)%nat with n by omega.
(apply apply_U_correct; easy).
-
(simpl in *).
(destruct n; [ omega |  ]).
replace (S n + 1 - 1)%nat with S n by omega.
(apply apply_U_correct; easy).
-
(simpl).
(rewrite Nat.sub_0_r).
(apply apply_new0_correct).
-
(simpl).
(rewrite Nat.sub_0_r).
(apply apply_new1_correct).
-
(simpl).
(rewrite Nat.sub_0_r).
(apply apply_new0_correct).
-
(simpl).
(rewrite Nat.sub_0_r).
(apply apply_new1_correct).
-
(simpl in *).
(destruct l; simpl).
(inversion L1).
(rewrite Nat.add_sub).
(apply apply_meas_correct).
(apply Lt; simpl; auto).
-
(simpl in *).
(destruct l; simpl).
(inversion L1).
(rewrite Nat.add_sub).
(apply apply_meas_correct).
(apply Lt; simpl; auto).
-
(simpl in *).
(destruct l; simpl).
(inversion L1).
(rewrite Nat.add_0_r).
(apply apply_discard_correct).
(apply Lt; simpl; auto).
-
(simpl in *).
(destruct l; simpl).
(inversion L1).
(rewrite Nat.add_0_r).
(apply apply_discard_correct).
(simpl in Lt).
(apply Lt; simpl; auto).
-
(simpl in *).
(destruct l; simpl).
(inversion L1).
(rewrite Nat.add_0_r).
(apply apply_discard_correct).
(apply Lt; simpl; auto).
Qed.
Lemma map_same_id :
  forall a l,
  map (fun z : nat * nat => if a =? snd z then (fst z, a) else z) (combine l l) =
  combine l l.
Proof.
(intros a l).
(induction l).
reflexivity.
(simpl).
(rewrite IHl).
(destruct (a =? a0) eqn:eq; try reflexivity).
(apply beq_nat_true in eq).
(subst; reflexivity).
Qed.
Lemma swap_list_aux_id : forall m n l, swap_list_aux m n (combine l l) == I (2 ^ n).
Proof.
(intros m n l).
generalize dependent m.
(induction l; intros m).
+
(simpl).
(destruct m; reflexivity).
+
(simpl).
(destruct m; [ reflexivity |  ]).
(simpl).
(rewrite map_same_id).
(rewrite IHl).
(unfold swap_two).
(rewrite <- beq_nat_refl).
Msimpl.
reflexivity.
Qed.
Lemma swap_list_n_id : forall n, swap_list n (seq 0 n) == I (2 ^ n).
Proof.
(intros).
(unfold swap_list).
(unfold zip_to).
(apply swap_list_aux_id).
Qed.
Definition get_var (p : Pat Bit) := match p with
                                    | bit x => x
                                    end.
Definition denote_pat {w} (p : Pat w) : Matrix (2 ^ \226\159\166 w \226\159\167) (2 ^ \226\159\166 w \226\159\167) :=
  swap_list (\226\159\166 w \226\159\167) (pat_to_list p).
Instance Denote_Pat  {w}: (Denote (Pat w) (Matrix (2 ^ \226\159\166 w \226\159\167) (2 ^ \226\159\166 w \226\159\167))) := {
 denote :=denote_pat}.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition denote_db_box {w1} {w2} (safe : bool) (c : DeBruijn_Box w1 w2) :=
  match c with
  | db_box _ c' => denote_db_circuit safe 0 (\226\159\166 w1 \226\159\167) c'
  end.
Definition denote_box (safe : bool) {W1 W2 : WType} (c : Box W1 W2) :
  Superoperator (2 ^ \226\159\166 W1 \226\159\167) (2 ^ \226\159\166 W2 \226\159\167) := denote_db_box safe (hoas_to_db_box c).
Instance Denote_Box  {W1} {W2}:
 (Denote (Box W1 W2) (Superoperator (2 ^ \226\159\166 W1 \226\159\167) (2 ^ \226\159\166 W2 \226\159\167))) :=
 {| denote := denote_box true |}.
Definition denote_circuit (safe : bool) {W : WType} (c : Circuit W) 
  (\206\1470 \206\147 : Ctx) : Superoperator (2 ^ (\226\159\166 \206\1470 \226\159\167 + \226\159\166 \206\147 \226\159\167)) (2 ^ (\226\159\166 \206\1470 \226\159\167 + \226\159\166 W \226\159\167)) :=
  denote_db_circuit safe (\226\159\166 \206\1470 \226\159\167) (\226\159\166 \206\147 \226\159\167) (hoas_to_db \206\147 c).
Notation "\226\159\168 \206\1470 | \206\147 \226\138\169 c \226\159\169" := (denote_circuit true c \206\1470 \206\147) (at level 20).
Notation "\226\159\168! \206\1470 | \206\147 \226\138\169 c !\226\159\169" := (denote_circuit false c \206\1470 \206\147) (at level 20).
Lemma denote_output :
  forall \206\1470 \206\147 {w} (p : Pat w),
  \226\159\168 \206\1470 | \206\147 \226\138\169 output p \226\159\169 = super (pad (\226\159\166 \206\1470 \226\159\167 + \226\159\166 \206\147 \226\159\167) (denote_pat (subst_pat \206\147 p))).
Proof.
(intros).
(simpl).
(unfold subst_pat).
reflexivity.
Qed.
Ltac
 fold_denotation :=
  repeat
   match goal with
   | |- context [ size_octx ?\206\147 ] => replace (size_octx \206\147) with \226\159\166 \206\147 \226\159\167; auto
   end.
Lemma length_fresh_state :
  forall w \206\147 \206\147',
  \206\147' = add_fresh_state w \206\147 -> length \206\147' = (length \206\147 + size_wtype w)%nat.
Proof.
(induction w; intros \206\147 \206\147' H).
-
(unfold add_fresh_state, add_fresh in H).
(simpl in H).
(rewrite H).
(rewrite app_length).
easy.
-
(unfold add_fresh_state, add_fresh in H).
(simpl in H).
(rewrite H).
(rewrite app_length).
easy.
-
(unfold add_fresh_state, add_fresh in H).
(simpl in H).
(rewrite H).
easy.
-
(rewrite H).
clear H.
(unfold add_fresh_state in *).
(simpl).
(destruct (add_fresh w1 \206\147) as [p1 \206\1471] eqn:E1).
(destruct (add_fresh w2 \206\1471) as [p2 \206\1472] eqn:E2).
(simpl).
specialize (IHw1 \206\147 _ eq_refl).
(rewrite E1 in IHw1).
(simpl in IHw1).
specialize (IHw2 \206\1471 _ eq_refl).
(rewrite E2 in IHw2).
(simpl in IHw2).
(rewrite IHw2, IHw1).
omega.
Qed.
Lemma swap_fresh_seq :
  forall w (\206\147 : Ctx),
  pat_to_list (add_fresh_pat w \206\147) = seq (length \206\147) (size_wtype w).
Proof.
(induction w; intros; simpl; auto).
(unfold add_fresh_pat).
(simpl).
(destruct (add_fresh w1 \206\147) as [p1 \206\1471] eqn:E1).
(destruct (add_fresh w2 \206\1471) as [p2 \206\1472] eqn:E2).
(simpl).
(rewrite (surjective_pairing (add_fresh w1 \206\147)) in E1).
(inversion E1).
(rewrite (surjective_pairing (add_fresh w2 \206\1471)) in E2).
(inversion E2).
(unfold add_fresh_pat in *).
(rewrite IHw1, IHw2).
symmetry in H1.
(apply length_fresh_state in H1).
(rewrite H1).
(rewrite <- seq_app).
easy.
Qed.
Lemma denote_pat_fresh_id :
  forall w, denote_pat (add_fresh_pat w []) == I (2 ^ \226\159\166 w \226\159\167).
Proof.
(intros).
(unfold denote_pat).
(simpl).
(rewrite swap_fresh_seq by validate).
(rewrite swap_list_n_id).
reflexivity.
Qed.
Lemma maps_to_app :
  forall \206\147 w, maps_to (length \206\147) (\206\147 ++ [Some w]) = Some (size_ctx \206\147).
Proof.
(intros \206\147 w).
(induction \206\147; simpl; eauto).
(destruct a; simpl).
(rewrite IH\206\147).
easy.
(rewrite IH\206\147).
easy.
Qed.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma no_gaps_size : forall \206\147, no_gaps \206\147 -> size_ctx \206\147 = length \206\147.
Proof.
(induction \206\147; trivial).
(intros NG).
(inversion NG; subst; simpl).
(rewrite IH\206\147; easy).
Qed.
Lemma size_ctx_le_length : forall \206\147, (size_ctx \206\147 <= length \206\147)%nat.
Proof.
(induction \206\147; trivial).
(destruct a; simpl; omega).
Qed.
Lemma size_eq_no_gaps : forall \206\147, size_ctx \206\147 = length \206\147 -> no_gaps \206\147.
Proof.
(induction \206\147).
constructor.
(intros E).
(destruct a).
-
constructor.
(apply IH\206\147).
(simpl in E; omega).
-
(simpl in E).
specialize (size_ctx_le_length \206\147) as LE.
omega.
Qed.
Lemma no_gaps_app : forall \206\147 \206\147', no_gaps \206\147 -> no_gaps \206\147' -> no_gaps (\206\147 ++ \206\147').
Proof.
(intros \206\147 \206\147' NG NG').
(induction \206\147; trivial).
(simpl).
(inversion NG; subst).
constructor.
auto.
Qed.
Lemma add_fresh_state_no_gaps :
  forall W \206\147, no_gaps \206\147 -> no_gaps (add_fresh_state W \206\147).
Proof.
(induction W; intros \206\147 NG).
-
(unfold add_fresh_state; simpl).
(apply no_gaps_app; trivial).
(repeat constructor).
-
(unfold add_fresh_state; simpl).
(apply no_gaps_app; trivial).
(repeat constructor).
-
(unfold add_fresh_state; simpl).
easy.
-
(unfold add_fresh_state; simpl).
(repeat rewrite add_fresh_split).
(simpl).
auto.
Qed.
Lemma bounded_pat_le :
  forall W (p : Pat W) n n', (n <= n')%nat -> Bounded_Pat n p -> Bounded_Pat n' p.
Proof.
(intros W p n n' LT BP).
(induction p).
-
constructor.
-
(inversion BP).
constructor.
omega.
-
(inversion BP).
constructor.
omega.
-
dependent destruction BP.
(constructor; auto).
Qed.
Lemma add_fresh_pat_bounded :
  forall W \206\147,
  no_gaps \206\147 -> Bounded_Pat (length \206\147 + size_wtype W)%nat (add_fresh_pat W \206\147).
Proof.
(induction W; intros \206\147 NG).
-
(unfold add_fresh_pat).
(simpl).
constructor.
omega.
-
(unfold add_fresh_pat).
(simpl).
constructor.
omega.
-
(unfold add_fresh_pat).
(simpl).
constructor.
-
(unfold add_fresh_pat in *).
(simpl in *).
(rewrite 2!add_fresh_split).
(simpl).
constructor.
specialize (IHW1 \206\147 NG).
(eapply bounded_pat_le; [  | apply IHW1 ]).
omega.
specialize (IHW2 _ (add_fresh_state_no_gaps W1 \206\147 NG)).
(apply_with_obligations IHW2).
(erewrite length_fresh_state by reflexivity).
omega.
Qed.
Lemma maps_to_no_gaps :
  forall v \206\147, (v < length \206\147)%nat -> no_gaps \206\147 -> maps_to v \206\147 = Some v.
Proof.
(induction v).
-
(intros \206\147 LT NG).
(inversion NG; subst; easy).
-
(intros \206\147 LT NG).
(inversion NG; subst).
easy.
(simpl).
(rewrite IHv; trivial).
(simpl in LT; omega).
Qed.
Lemma subst_var_no_gaps :
  forall \206\147 v, (v < length \206\147)%nat -> no_gaps \206\147 -> subst_var \206\147 v = v.
Proof.
(intros \206\147 v LT NG).
(unfold subst_var).
(rewrite maps_to_no_gaps; easy).
Qed.
Lemma subst_pat_no_gaps :
  forall w (\206\147 : Ctx) (p : Pat w),
  Bounded_Pat (length \206\147) p -> no_gaps \206\147 -> subst_pat \206\147 p = p.
Proof.
(intros w \206\147 p BP NG).
(induction p; trivial).
-
(inversion BP).
(simpl).
(rewrite subst_var_no_gaps; easy).
-
(inversion BP).
(simpl).
(rewrite subst_var_no_gaps; easy).
-
dependent destruction BP.
(simpl).
(rewrite IHp1, IHp2; easy).
Qed.
Lemma subst_units : forall w (p : Pat w) \206\147, \226\136\133 \226\138\162 p :Pat -> subst_pat \206\147 p = p.
Proof.
(intros w p \206\147 H).
gen \206\147.
dependent induction H.
-
(intros).
reflexivity.
-
(inversion s).
-
(inversion s).
-
(intros \206\147).
symmetry in e.
(apply merge_nil_inversion in e as [E1 E2]).
(simpl).
(rewrite IHTypes_Pat1, IHTypes_Pat2; easy).
Qed.
Lemma subst_pat_fresh :
  forall w \206\147,
  no_gaps \206\147 ->
  subst_pat (add_fresh_state w \206\147) (add_fresh_pat w \206\147) = add_fresh_pat w \206\147.
Proof.
(intros).
(apply subst_pat_no_gaps).
(erewrite length_fresh_state by easy).
(apply add_fresh_pat_bounded).
easy.
(apply add_fresh_state_no_gaps).
easy.
Qed.
Lemma subst_pat_fresh_empty :
  forall w,
  subst_pat (add_fresh_state w []) (add_fresh_pat w []) = add_fresh_pat w [].
Proof.
(intros).
(apply subst_pat_fresh).
constructor.
Qed.
Lemma size_fresh_ctx :
  forall (w : WType) (\206\147 : Ctx),
  size_ctx (add_fresh_state w \206\147) = (size_ctx \206\147 + size_wtype w)%nat.
Proof.
(unfold add_fresh_state; simpl).
(induction w; intros \206\147).
-
(simpl).
(rewrite size_ctx_app; easy).
-
(simpl).
(rewrite size_ctx_app; easy).
-
(simpl; omega).
-
(simpl).
(destruct (add_fresh w1 \206\147) as [p1 \206\1471] eqn:E1).
(destruct (add_fresh w2 \206\1471) as [p2 \206\1472] eqn:E2).
(simpl in *).
(rewrite (surjective_pairing (add_fresh _ _)) in E2).
(inversion E2).
(rewrite IHw2).
(rewrite (surjective_pairing (add_fresh _ _)) in E1).
(inversion E1).
(rewrite IHw1).
omega.
Qed.
Lemma denote_db_unbox :
  forall {w1} {w2} (b : Box w1 w2),
  \226\159\166 b \226\159\167 = \226\159\168 [] | add_fresh_state w1 [] \226\138\169 unbox b (add_fresh_pat w1 []) \226\159\169.
Proof.
(destruct b).
(simpl).
(unfold denote_box).
(unfold denote_circuit).
(simpl).
(rewrite size_fresh_ctx).
(simpl).
(unfold add_fresh_state, add_fresh_pat).
(destruct (add_fresh w1 []) as [p1 \206\1471] eqn:E1).
(simpl).
easy.
Qed.
Lemma denote_index_update_some :
  forall (\206\147 : Ctx) x w w',
  index (Valid \206\147) x = Some w -> \226\159\166 update_at \206\147 x (Some w') \226\159\167 = \226\159\166 \206\147 \226\159\167.
Proof.
(induction \206\147 as [| o \206\147]; intros; auto).
(destruct x; auto).
*
(simpl in *).
subst.
auto.
*
(simpl in *).
(rewrite (IH\206\147 _ w); auto).
Qed.
Lemma denote_index_update_none :
  forall (\206\147 : Ctx) x w,
  index (Valid \206\147) x = Some w -> \226\159\166 update_at \206\147 x None \226\159\167 = (\226\159\166 \206\147 \226\159\167 - 1)%nat.
Proof.
(induction \206\147 as [| o \206\147]; intros; auto).
(destruct x; auto).
*
(simpl in *).
subst.
(simpl).
omega.
*
(simpl in *).
(rewrite (IH\206\147 _ w); trivial).
(destruct o; trivial).
(assert (size_ctx \206\147 > 0)%nat).
clear - H.
gen x.
(induction \206\147).
(destruct x; simpl; intros H; inversion H).
(intros x H).
(destruct a; simpl).
omega.
(destruct x).
(simpl in H; inversion H).
(apply (IH\206\147 x)).
(simpl in H).
(apply H).
omega.
Qed.
Lemma singleton_update :
  forall \206\147 W W' v, SingletonCtx v W \206\147 -> SingletonCtx v W' (update_at \206\147 v (Some W')).
Proof.
(intros \206\147 W W' v H).
(induction H).
+
(simpl).
constructor.
+
(simpl).
constructor.
(apply IHSingletonCtx).
Qed.
Lemma remove_at_singleton :
  forall x w \206\147, SingletonCtx x w \206\147 -> empty_ctx (remove_at x \206\147).
Proof.
(induction 1; simpl).
*
constructor.
*
constructor.
auto.
Qed.
Lemma update_none_singleton :
  forall x w \206\147, SingletonCtx x w \206\147 -> empty_ctx (update_at \206\147 x None).
Proof.
(induction 1; simpl).
*
(repeat constructor).
*
constructor.
assumption.
Qed.
Lemma remove_pat_singleton :
  forall x W (p : Pat W),
  singleton x W \226\138\162 p :Pat -> remove_pat p (singleton x W) = [].
Proof.
(intros x W p H).
dependent induction H.
-
(rewrite <- x).
reflexivity.
-
(unfold remove_pat).
(simpl).
(unfold remove_var).
(simpl).
(rewrite trim_empty; trivial).
(eapply update_none_singleton).
(apply s).
-
(unfold remove_pat).
(simpl).
(unfold remove_var).
(simpl).
(rewrite trim_empty; trivial).
(eapply update_none_singleton).
(apply s).
-
(unfold remove_pat).
(simpl).
Abort.
Proposition process_gate_ctx_size :
  forall w1 w2 (g : Gate w1 w2) p (\206\147 : Ctx),
  (\226\159\166 w1 \226\159\167 <= \226\159\166 \206\147 \226\159\167)%nat ->
  \226\159\166 process_gate_state g p \206\147 \226\159\167 = (\226\159\166 \206\147 \226\159\167 + \226\159\166 w2 \226\159\167 - \226\159\166 w1 \226\159\167)%nat.
Proof.
(destruct g; intros p \206\147 H; try (simpl; rewrite Nat.add_sub; auto; fail);
  try (simpl; rewrite ctx_size_app; simpl; omega)).
-
(simpl).
(rewrite Nat.sub_0_r).
(destruct \206\147).
(simpl in *).
omega.
(simpl).
(destruct o; rewrite size_ctx_app; simpl; omega).
-
(simpl).
(rewrite Nat.sub_0_r).
(destruct \206\147).
(simpl in *).
omega.
(simpl).
(destruct o; rewrite size_ctx_app; simpl; omega).
-
(simpl).
(rewrite Nat.sub_0_r).
(destruct \206\147).
(simpl in *).
omega.
(simpl).
(destruct o; rewrite size_ctx_app; simpl; omega).
-
(simpl).
(rewrite Nat.sub_0_r).
(destruct \206\147).
(simpl in *).
omega.
(simpl).
(destruct o; rewrite size_ctx_app; simpl; omega).
-
dependent destruction p.
(simpl).
(destruct \206\147).
(simpl).
easy.
(simpl).
(destruct o).
(simpl).
(unfold process_gate_state).
(simpl).
admit.
admit.
-
Abort.
Proposition process_gate_state_merge :
  forall w1 w2 (g : Gate w1 w2) p \206\1471 \206\1472 \206\147,
  Types_Pat \206\1471 p ->
  Valid \206\147 = \206\1471 \226\139\147 \206\1472 ->
  Valid (process_gate_state g p \206\147) = process_gate_state g p \206\147 \226\139\147 \206\1472.
Proof.
Abort.
Open Scope circ_scope.
Lemma index_merge_l :
  forall \206\147 \206\1471 \206\1472 n w, \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> index \206\1471 n = Some w -> index \206\147 n = Some w.
Proof.
(intros \206\147 \206\1471 \206\1472 n w H H0).
(apply merge_fun_ind in H).
generalize dependent n.
(induction H).
+
(intros n H).
(destruct n; simpl in H; inversion H).
+
auto.
+
(intros n Hi).
(inversion m; subst).
-
(destruct n).
(simpl in Hi).
(inversion Hi).
(simpl in *).
(rewrite IHmerge_ind).
reflexivity.
assumption.
-
(destruct n).
(simpl in *).
assumption.
(simpl in *).
(rewrite IHmerge_ind).
reflexivity.
assumption.
-
(destruct n).
(simpl in Hi).
(inversion Hi).
(simpl in *).
(rewrite IHmerge_ind).
reflexivity.
assumption.
Qed.
Lemma index_merge_r :
  forall \206\147 \206\1471 \206\1472 n w, \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> index \206\1472 n = Some w -> index \206\147 n = Some w.
Proof.
(intros \206\147 \206\1471 \206\1472 n w H H0).
(apply (index_merge_l \206\147 \206\1472 \206\1471)).
(destruct H).
constructor.
assumption.
(rewrite merge_comm; assumption).
assumption.
Qed.
Lemma remove_at_merge :
  forall (\206\147 \206\1471 \206\1472 : Ctx) n,
  \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 ->
  Valid (remove_at n \206\147) \226\169\181 Valid (remove_at n \206\1471) \226\136\153 Valid (remove_at n \206\1472).
Proof.
(intros \206\147 \206\1471 \206\1472 n H).
(apply merge_fun_ind in H).
generalize dependent n.
dependent induction H.
+
(intros n).
constructor.
(apply valid_valid).
replace (remove_at n []) with @nil (option WType).
(rewrite merge_nil_l).
reflexivity.
(destruct n; reflexivity).
+
(intros n).
constructor.
(apply valid_valid).
replace (remove_at n []) with @nil (option WType).
(rewrite merge_nil_r).
reflexivity.
(destruct n; reflexivity).
+
(intros n).
constructor.
(apply valid_valid).
(destruct n).
(simpl).
(apply merge_ind_fun in H).
(destruct H).
(apply pf_merge).
unlock_merge.
(simpl).
(edestruct IHmerge_ind with (n := n); try reflexivity).
unlock_merge.
(simpl in pf_merge).
(rewrite <- pf_merge).
(apply merge_o_ind_fun in m).
(rewrite m).
reflexivity.
Qed.
Lemma update_none_merge :
  forall (\206\147 \206\1471 \206\1472 : Ctx) n,
  \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 ->
  Valid (update_at \206\147 n None) \226\169\181 Valid (update_at \206\1471 n None)
  \226\136\153 Valid (update_at \206\1472 n None).
Proof.
(intros \206\147 \206\1471 \206\1472 n H).
(apply merge_fun_ind in H).
generalize dependent n.
dependent induction H.
-
(intros n).
constructor.
(apply valid_valid).
replace (update_at [] n None) with @nil (option WType).
(rewrite merge_nil_l).
reflexivity.
(destruct n; reflexivity).
-
(intros n).
constructor.
(apply valid_valid).
replace (update_at [] n None) with @nil (option WType).
(rewrite merge_nil_r).
reflexivity.
(destruct n; reflexivity).
-
(intros n).
constructor.
(apply valid_valid).
(destruct n).
+
(simpl).
(apply merge_ind_fun in H).
(destruct H).
unlock_merge.
(simpl).
(rewrite <- pf_merge).
reflexivity.
+
(simpl).
(edestruct IHmerge_ind with (n := n); try reflexivity).
unlock_merge.
(simpl in *).
(rewrite <- pf_merge).
(apply merge_o_ind_fun in m).
(rewrite m).
reflexivity.
Qed.
Lemma remove_at_collision :
  forall n W (\206\147 \206\1471 \206\1472 : Ctx),
  SingletonCtx n W \206\1471 -> \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> size_ctx (remove_at n \206\1472) = size_ctx \206\1472.
Proof.
(intros n).
(induction n).
+
(intros W \206\147 \206\1471 \206\1472 H H0).
(simpl).
(destruct \206\1472).
reflexivity.
(inversion H; subst).
(destruct o).
(destruct H0).
(simpl in pf_merge).
(rewrite pf_merge in pf_valid).
(apply not_valid in pf_valid).
contradiction.
reflexivity.
+
(intros W \206\147 \206\1471 \206\1472 H H0).
(simpl).
(destruct \206\1472).
reflexivity.
(simpl).
(inversion H; subst).
(apply merge_fun_ind in H0).
(inversion H0; subst).
(erewrite IHn).
reflexivity.
(apply H2).
(apply merge_ind_fun).
(apply H8).
Qed.
Lemma update_none_collision :
  forall n W (\206\147 \206\1471 \206\1472 : Ctx),
  SingletonCtx n W \206\1471 -> \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> size_ctx (update_at \206\1472 n None) = size_ctx \206\1472.
Proof.
(intros n).
(induction n).
+
(intros W \206\147 \206\1471 \206\1472 H H0).
(simpl).
(destruct \206\1472).
reflexivity.
(inversion H; subst).
(destruct o).
(destruct H0).
(simpl in pf_merge).
(rewrite pf_merge in pf_valid).
(apply not_valid in pf_valid).
contradiction.
reflexivity.
+
(intros W \206\147 \206\1471 \206\1472 H H0).
(simpl).
(destruct \206\1472).
reflexivity.
(simpl).
(inversion H; subst).
(apply merge_fun_ind in H0).
(inversion H0; subst).
(erewrite IHn).
reflexivity.
(apply H2).
(apply merge_ind_fun).
(apply H8).
Qed.
Lemma process_gate_ctx_size :
  forall w1 w2 (\206\147 \206\1471 \206\1472 : Ctx) (g : Gate w1 w2) (p1 : Pat w1),
  \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 ->
  \206\1471 \226\138\162 p1 :Pat ->
  size_ctx (process_gate_state g p1 \206\147) = (size_ctx \206\147 + \226\159\166 w2 \226\159\167 - \226\159\166 w1 \226\159\167)%nat.
Proof.
(intros w1 w2 \206\147 \206\1471 \206\1472 g p1 M TP).
(unfold process_gate_state).
(destruct g; simpl).
-
(rewrite Nat.add_sub).
easy.
-
(rewrite Nat.add_sub).
easy.
-
(rewrite Nat.sub_0_r).
(rewrite size_ctx_app).
easy.
-
(rewrite Nat.sub_0_r).
(rewrite size_ctx_app).
easy.
-
(rewrite Nat.sub_0_r).
(rewrite size_ctx_app).
easy.
-
(rewrite Nat.sub_0_r).
(rewrite size_ctx_app).
easy.
-
dependent destruction p1.
(simpl).
(rewrite Nat.add_sub).
(unfold change_type).
(rewrite denote_index_update_some with (w := Qubit)).
easy.
(eapply index_merge_l).
(apply M).
(apply singleton_index).
dependent destruction TP.
easy.
-
(rewrite Nat.add_sub).
easy.
-
dependent destruction p1.
(unfold remove_pat).
(simpl).
(unfold remove_var).
(rewrite size_ctx_trim).
(rewrite Nat.add_0_r).
(rewrite denote_index_update_none with (w := Bit)).
easy.
(eapply index_merge_l).
(apply M).
(apply singleton_index).
dependent destruction TP.
easy.
-
dependent destruction p1.
(unfold remove_pat).
(simpl).
(unfold remove_var).
(rewrite size_ctx_trim).
(rewrite Nat.add_0_r).
(rewrite denote_index_update_none with (w := Qubit)).
easy.
(eapply index_merge_l).
(apply M).
(apply singleton_index).
dependent destruction TP.
easy.
-
dependent destruction p1.
(unfold remove_pat).
(simpl).
(unfold remove_var).
(rewrite size_ctx_trim).
(rewrite Nat.add_0_r).
(rewrite denote_index_update_none with (w := Qubit)).
easy.
(eapply index_merge_l).
(apply M).
(apply singleton_index).
dependent destruction TP.
easy.
Qed.
replace (process_gate g p1 \206\147) with
 Datatypes.pair (process_gate_pat g p1 \206\147) (process_gate_state g p1 \206\147)
 by (symmetry; apply surjective_pairing).
(simpl; fold_denotation).
(rewrite process_gate_ctx_size with (\206\1471 := \206\1471) (\206\1472 := \206\1472); easy).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqP91LGg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma lookup_maybe_S : forall x l, lookup_maybe (S x) (map S l) = lookup_maybe x l.
Proof.
(intros x l).
(induction l; auto).
(simpl).
(destruct (x =? a)).
easy.
(rewrite IHl).
easy.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqCeat7c"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma subst_qubit_bounded :
  forall v (\206\147 \206\147v \206\147o : Ctx),
  \206\147v \226\138\162 qubit v :Pat -> \206\147 \226\169\181 \206\147v \226\136\153 \206\147o -> (subst_var \206\147 v < size_octx \206\147)%nat.
Proof.
(induction v; intros \206\147 \206\147v \206\147o TP M).
-
(inversion TP; subst).
(apply singleton_equiv in H1).
(rewrite H1 in M).
(apply merge_fun_ind in M).
(inversion M; subst).
(simpl).
(unfold subst_var).
(simpl).
omega.
(unfold subst_var).
(simpl).
(destruct o; simpl).
omega.
(inversion H4).
-
(inversion TP; subst).
(apply singleton_equiv in H1).
(rewrite H1 in M).
(apply merge_fun_ind in M).
(inversion M; subst).
+
(unfold subst_var).
(simpl).
(rewrite maps_to_singleton).
(rewrite singleton_size).
omega.
+
(assert (TP' : singleton v Qubit \226\138\162 qubit v :Pat)).
constructor.
(apply singleton_singleton).
(apply merge_ind_fun in H5).
specialize (IHv _ _ _ TP' H5).
(destruct o; simpl in *).
*
(unfold subst_var in *).
(simpl).
(destruct (maps_to v \206\1470); simpl; auto).
omega.
*
(unfold subst_var in *).
(simpl).
(destruct (maps_to v \206\1470); simpl; auto).
Qed.
Lemma subst_bit_bounded :
  forall v (\206\147 \206\147v \206\147o : Ctx),
  \206\147v \226\138\162 bit v :Pat -> \206\147 \226\169\181 \206\147v \226\136\153 \206\147o -> (subst_var \206\147 v < size_octx \206\147)%nat.
Proof.
(induction v; intros \206\147 \206\147v \206\147o TP M).
-
(inversion TP; subst).
(apply singleton_equiv in H1).
(rewrite H1 in M).
(apply merge_fun_ind in M).
(inversion M; subst).
(simpl).
(unfold subst_var).
(simpl).
omega.
(unfold subst_var).
(simpl).
(destruct o; simpl).
omega.
(inversion H4).
-
(inversion TP; subst).
(apply singleton_equiv in H1).
(rewrite H1 in M).
(apply merge_fun_ind in M).
(inversion M; subst).
+
(unfold subst_var).
(simpl).
(rewrite maps_to_singleton).
(rewrite singleton_size).
omega.
+
(assert (TP' : singleton v Bit \226\138\162 bit v :Pat)).
constructor.
(apply singleton_singleton).
(apply merge_ind_fun in H5).
specialize (IHv _ _ _ TP' H5).
(destruct o; simpl in *).
*
(unfold subst_var in *).
(simpl).
(destruct (maps_to v \206\1470); simpl; auto).
omega.
*
(unfold subst_var in *).
(simpl).
(destruct (maps_to v \206\1470); simpl; auto).
Qed.
Lemma pat_to_list_bounded :
  forall W (\206\147 \206\147p \206\147o : Ctx) (p : Pat W) x,
  \206\147 \226\169\181 \206\147p \226\136\153 \206\147o ->
  \206\147p \226\138\162 p :Pat -> In x (pat_to_list (subst_pat \206\147 p)) -> (x < size_ctx \206\147)%nat.
Proof.
(intros W \206\147 \206\147p \206\147o p).
gen \206\147 \206\147p \206\147o.
(induction p; intros \206\147 \206\147p \206\147o x M TP IN).
-
(simpl in *).
easy.
-
(simpl in *).
(destruct IN; try easy).
(rewrite <- H).
(eapply subst_qubit_bounded).
(apply TP).
(apply M).
-
(simpl in *).
(destruct IN; try easy).
(rewrite <- H).
(eapply subst_bit_bounded).
(apply TP).
(apply M).
-
(simpl in IN).
(apply in_app_or in IN).
(destruct IN as [IN1| IN2]).
+
dependent destruction TP.
(destruct M).
(rewrite e in pf_merge).
(rewrite <- merge_assoc in pf_merge).
(destruct \206\1471 as [| \206\1471], (\206\1472 \226\139\147 \206\147o) as [| \206\147']; try invalid_contradiction).
(eapply IHp1; trivial).
(split; trivial).
(apply pf_merge).
easy.
+
dependent destruction TP.
(destruct M).
(rewrite e in pf_merge).
(rewrite (merge_comm \206\1471) in pf_merge).
(rewrite <- merge_assoc in pf_merge).
(destruct \206\1472 as [| \206\1472], (\206\1471 \226\139\147 \206\147o) as [| \206\147']; try invalid_contradiction).
(eapply IHp2; trivial).
(split; trivial).
(apply pf_merge).
easy.
Qed.
Lemma update_at_singleton :
  forall v W W' \206\147 \206\147',
  SingletonCtx v W \206\147 -> SingletonCtx v W' \206\147' -> update_at \206\147 v (Some W') = \206\147'.
Proof.
(intros v W W' \206\147 \206\147' H H').
(apply singleton_equiv in H).
(apply singleton_equiv in H').
subst.
(induction v; auto).
(simpl).
(rewrite IHv).
easy.
Qed.
Lemma update_at_merge :
  forall v W W' \206\147 \206\1471 \206\1471' \206\1472,
  SingletonCtx v W \206\1471 ->
  SingletonCtx v W' \206\1471' ->
  Valid \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 -> Valid (update_at \206\147 v (Some W')) \226\169\181 \206\1471' \226\136\153 \206\1472.
Proof.
(induction v; intros W W' \206\147 \206\1471 \206\1471' \206\1472 H H0 H1).
-
(apply singleton_equiv in H).
subst.
(apply singleton_equiv in H0).
subst.
(simpl in *).
(destruct H1).
split.
validate.
(destruct \206\1472 as [| \206\1472]).
invalid_contradiction.
(destruct \206\147).
Search -merge -\226\136\133.
symmetry in pf_merge.
(apply merge_nil_inversion in pf_merge as [L R]).
(inversion L).
(simpl).
(destruct \206\1472).
(destruct \206\147).
easy.
(rewrite merge_nil_r in pf_merge).
(inversion pf_merge).
(destruct o0).
(inversion pf_merge).
unlock_merge.
(simpl in *).
(inversion pf_merge; subst).
easy.
-
(apply merge_fun_ind in H1).
(inversion H1; subst).
(inversion H).
split.
validate.
(rewrite merge_nil_r).
f_equal.
(eapply update_at_singleton; trivial).
(apply H).
(inversion H; subst).
(inversion H0; subst).
(simpl).
(apply merge_ind_fun in H6).
specialize (IHv _ _ _ _ _ _ H7 H3 H6).
(destruct IHv).
split.
validate.
(simpl).
unlock_merge.
(simpl in *).
(rewrite <- pf_merge).
(inversion H4; subst; easy).
Qed.
Lemma types_pat_no_trail : forall \206\147 W (p : Pat W), Valid \206\147 \226\138\162 p :Pat -> trim \206\147 = \206\147.
Proof.
(intros \206\147 W).
gen \206\147.
(induction W; intros \206\147 p H; dependent destruction p; dependent destruction H).
-
(apply singleton_equiv in s; subst).
(induction v; trivial).
(simpl).
(rewrite IHv).
(destruct v; easy).
-
(apply singleton_equiv in s; subst).
(induction v; trivial).
(simpl).
(rewrite IHv).
(destruct v; easy).
-
easy.
-
(destruct \206\1471 as [| \206\1471], \206\1472 as [| \206\1472]; try invalid_contradiction).
(assert (otrim (Valid \206\147) = Valid \206\147)).
(rewrite e  at 2).
(rewrite <- (IHW1 \206\1471 p1); trivial).
(rewrite <- (IHW2 \206\1472 p2); trivial).
(destruct (trim_merge \206\147 \206\1471 \206\1472)).
solve_merge.
assumption.
(apply pf_merge).
(simpl in H1).
(rewrite ctx_octx in H1).
easy.
Qed.
Lemma remove_bit_merge' :
  forall (\206\147 \206\147' : Ctx) v, \206\147' \226\169\181 singleton v Bit \226\136\153 \206\147 -> remove_pat (bit v) \206\147' = trim \206\147.
Proof.
(intros \206\147 \206\147' v H).
(apply merge_fun_ind in H).
dependent induction H.
-
(destruct v; inversion x).
-
(induction v).
+
(simpl).
(unfold remove_pat).
(simpl).
easy.
+
(simpl).
(unfold remove_pat in *).
(unfold remove_var in *).
(simpl in *).
(rewrite IHv).
easy.
-
(destruct v).
+
(inversion x; subst).
(inversion m; subst).
(unfold remove_pat).
(simpl in *).
(inversion H; subst; easy).
+
(inversion x; subst).
(inversion m; subst).
(unfold remove_pat, remove_var in *).
(simpl in *).
(erewrite IHmerge_ind; easy).
replace (remove_pat (bit (S v)) (Some w :: \206\1470)) with Some w :: remove_pat (bit v) \206\1470
 by easy.
(simpl).
(erewrite IHmerge_ind; easy).
Qed.
Lemma remove_bit_merge :
  forall (\206\147 \206\147' : Ctx) W (p : Pat W) v,
  \206\147 \226\138\162 p :Pat -> \206\147' \226\169\181 singleton v Bit \226\136\153 \206\147 -> remove_pat (bit v) \206\147' = \206\147.
Proof.
(intros \206\147 \206\147' W p v H H0).
(erewrite <- (types_pat_no_trail \206\147) by apply H).
(simpl).
(assert (remove_pat (bit v) \206\147' = trim \206\147)).
(apply remove_bit_merge'; easy).
(inversion H1).
easy.
Qed.
Lemma remove_qubit_merge' :
  forall (\206\147 \206\147' : Ctx) v,
  \206\147' \226\169\181 singleton v Qubit \226\136\153 \206\147 -> remove_pat (qubit v) \206\147' = trim \206\147.
Proof.
(intros \206\147 \206\147' v H).
(apply merge_fun_ind in H).
dependent induction H.
-
(destruct v; inversion x).
-
(induction v).
+
(simpl).
(unfold remove_pat).
(simpl).
easy.
+
(simpl).
(unfold remove_pat, remove_var in *).
(simpl in *).
(inversion IHv).
(rewrite H0).
easy.
-
(destruct v).
+
(inversion x; subst).
(inversion m; subst).
(unfold remove_pat).
(simpl in *).
(inversion H; subst; easy).
+
(inversion x; subst).
(inversion m; subst).
(unfold remove_pat, remove_var in *).
(simpl in *).
(erewrite IHmerge_ind; easy).
replace (remove_pat (qubit (S v)) (Some w :: \206\1470)) with
 Some w :: remove_pat (qubit v) \206\1470 by easy.
(simpl).
(erewrite IHmerge_ind; easy).
Qed.
Lemma remove_qubit_merge :
  forall (\206\147 \206\147' : Ctx) W (p : Pat W) v,
  \206\147 \226\138\162 p :Pat -> \206\147' \226\169\181 singleton v Qubit \226\136\153 \206\147 -> remove_pat (qubit v) \206\147' = \206\147.
Proof.
(intros \206\147 \206\147' W p v H H0).
(erewrite <- (types_pat_no_trail \206\147) by apply H).
(simpl).
(assert (remove_pat (bit v) \206\147' = trim \206\147)).
(apply remove_qubit_merge'; easy).
(inversion H1).
easy.
Qed.
Lemma remove_bit_pred :
  forall (\206\147 \206\147' : Ctx) v,
  \206\147' \226\169\181 singleton v Bit \226\136\153 \206\147 ->
  size_ctx (remove_pat (bit v) \206\147') = (size_ctx \206\147' - 1)%nat.
Proof.
(intros \206\147 \206\147' v H).
(rewrite (remove_bit_merge' \206\147 \206\147'); trivial).
(destruct H).
replace (size_ctx \206\147') with size_octx \206\147' by easy.
(rewrite pf_merge in *).
(rewrite size_octx_merge by easy).
(simpl).
(rewrite singleton_size).
(rewrite size_ctx_trim).
omega.
Qed.
Lemma remove_qubit_pred :
  forall (\206\147 \206\147' : Ctx) v,
  \206\147' \226\169\181 singleton v Qubit \226\136\153 \206\147 ->
  size_ctx (remove_pat (qubit v) \206\147') = (size_ctx \206\147' - 1)%nat.
Proof.
(intros \206\147 \206\147' v H).
(rewrite (remove_qubit_merge' \206\147 \206\147'); trivial).
(destruct H).
replace (size_ctx \206\147') with size_octx \206\147' by easy.
(rewrite pf_merge in *).
(rewrite size_octx_merge by easy).
(simpl).
(rewrite singleton_size).
(rewrite size_ctx_trim).
omega.
Qed.
Lemma maps_to_trim : forall \206\147 v, maps_to v (trim \206\147) = maps_to v \206\147.
Proof.
(intros \206\147 v).
gen \206\147.
(induction v; intros \206\147).
-
(destruct \206\147; trivial).
(destruct o; trivial).
(simpl).
(destruct (trim \206\147); easy).
-
(destruct \206\147; trivial).
(simpl).
(destruct o).
(rewrite IHv; easy).
(rewrite <- IHv).
(destruct (trim \206\147) eqn:E; trivial).
(destruct v; easy).
Qed.
Lemma subst_pat_trim : forall W \206\147 (p : Pat W), subst_pat (trim \206\147) p = subst_pat \206\147 p.
Proof.
(intros W \206\147 p).
(induction p).
-
(simpl).
easy.
-
(simpl).
(unfold subst_var).
(rewrite maps_to_trim).
easy.
-
(simpl).
(unfold subst_var).
(rewrite maps_to_trim).
easy.
-
(simpl).
(rewrite IHp1, IHp2).
easy.
Qed.
Lemma trim_types_circ :
  forall W (c : Circuit W) (\206\147 : Ctx), \206\147 \226\138\162 c :Circ -> trim \206\147 \226\138\162 c :Circ.
Proof.
(intros W c).
(induction c).
-
(intros \206\147 WT).
dependent destruction WT.
(erewrite types_pat_no_trail by apply t).
(econstructor; easy).
-
(intros \206\147 WT).
dependent destruction WT.
(destruct \206\1470 as [| \206\1470], \206\1471 as [| \206\1471]; try invalid_contradiction).
specialize (types_pat_no_trail _ _ _ t) as NT1.
econstructor.
(rewrite <- NT1 in t).
(apply t).
2: (apply (trim_merge \206\147 \206\1471 \206\1470 pf1)).
(simpl).
(intros \206\1471' \206\147' p2 M' t').
(destruct \206\1471' as [| \206\1471']; try invalid_contradiction).
(assert (M'' : (\206\1471' \226\139\147 \206\1470) \226\169\181 \206\1471' \226\136\153 \206\1470)).
(split; trivial).
(apply trim_valid).
(destruct M').
(apply types_pat_no_trail in t').
(rewrite <- t' in pf_merge).
(rewrite <- trim_merge_dist).
(simpl).
(rewrite <- pf_merge).
easy.
specialize (t0 \206\1471' (\206\1471' \226\139\147 \206\1470) p2 M'' t').
(destruct M').
(rewrite pf_merge).
(apply types_pat_no_trail in t').
(rewrite <- t').
(simpl_rewrite (trim_merge_dist \206\1471' \206\1470)).
(destruct (\206\1471' \226\139\147 \206\1470) as [| \206\147'']; try invalid_contradiction).
(simpl).
(apply H).
(apply t0).
-
(intros \206\147 H0).
dependent destruction H0.
(destruct \206\1471 as [| \206\1471], \206\1472 as [| \206\1472]; try invalid_contradiction).
econstructor.
(apply t).
(intros b).
(apply H).
(apply t0).
(apply types_pat_no_trail in t).
(rewrite <- t).
(apply (trim_merge \206\147 \206\1471 \206\1472)).
easy.
Qed.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Theorem denote_static_circuit_correct :
  forall W (\206\1470 \206\147 : Ctx) (c : Circuit W),
  Static_Circuit c -> \206\147 \226\138\162 c :Circ -> WF_Superoperator (\226\159\168 \206\1470 | \206\147 \226\138\169 c \226\159\169).
Proof.
(intros W \206\1470 \206\147 c).
gen \206\1470 \206\147.
(induction c; intros \206\1470 \206\147 STAT WT).
-
dependent destruction WT.
(unfold denote_circuit).
(simpl).
(unfold denote_pat).
(unfold pad).
subst.
(rewrite (ctx_wtype_size w p \206\147 t)).
(apply super_unitary_correct).
(rewrite Nat.add_sub).
(match goal with
 | |- WF_Unitary (?A \226\138\151 ?B) => specialize (kron_unitary A B) as KU
 end).
unify_pows_two.
(simpl in *).
(rewrite (ctx_wtype_size w p \206\147 t) in *).
replace (2 ^ (size_ctx \206\1470 + size_ctx \206\147))%nat with
 (2 ^ size_ctx \206\147 * 2 ^ size_ctx \206\1470)%nat by (simpl; unify_pows_two).
(apply KU).
(apply swap_list_unitary).
(rewrite size_wtype_length).
(rewrite (ctx_wtype_size w p \206\147 t)).
omega.
(intros x).
(eapply pat_to_list_bounded).
split.
validate.
(rewrite merge_nil_r).
easy.
easy.
(apply id_unitary).
-
dependent destruction WT.
rename p into p1.
rename \206\1471 into \206\1473.
rename \206\1472 into \206\1471.
rename \206\1473 into \206\1472.
dependent destruction STAT.
rename H0 into STAT.
rename H into IH.
(unfold denote_circuit; simpl).
(destruct g).
+
(simpl).
(destruct pf1).
replace (size_ctx \206\147) with size_octx \206\147 by easy.
(rewrite pf_merge in *).
(rewrite size_octx_merge by easy).
