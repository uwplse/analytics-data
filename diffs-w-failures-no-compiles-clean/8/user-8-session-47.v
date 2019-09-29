Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqCAHRMa"
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
