Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqXz0NhE"
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
(rewrite <- (Nat.mul_1_r (2 ^ n)%nat)).
