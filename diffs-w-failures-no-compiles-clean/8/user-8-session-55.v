Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqVQNm49"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Psatz.
Require Import Reals.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqguDqJO"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Import Setoid.
Require Export Matrix.
Definition qubit0 : Vector 2 := fun i j => if i =? 0 then 1 else 0.
Definition qubit1 : Vector 2 := fun i j => if i =? 1 then 1 else 0.
Notation "\226\136\1630\226\159\169" := qubit0.
Notation "\226\136\1631\226\159\169" := qubit1.
Notation "\226\159\1680\226\136\163" := (qubit0) \226\128\160.
Notation "\226\159\1681\226\136\163" := (qubit1) \226\128\160.
Notation "\226\136\1630\226\159\169\226\159\1680\226\136\163" := (\226\136\1630\226\159\169 \195\151 \226\159\1680\226\136\163).
Notation "\226\136\1631\226\159\169\226\159\1681\226\136\163" := (\226\136\1631\226\159\169 \195\151 \226\159\1681\226\136\163).
Notation "\226\136\1631\226\159\169\226\159\1680\226\136\163" := (\226\136\1631\226\159\169 \195\151 \226\159\1680\226\136\163).
Notation "\226\136\1630\226\159\169\226\159\1681\226\136\163" := (\226\136\1630\226\159\169 \195\151 \226\159\1681\226\136\163).
Definition bra (x : nat) : Matrix 1 2 := if x =? 0 then \226\159\1680\226\136\163 else \226\159\1681\226\136\163.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then \226\136\1630\226\159\169 else \226\136\1631\226\159\169.
Notation "'\226\136\163' x '\226\159\169'" := (ket x).
Notation "'\226\159\168' x '\226\136\163'" := (bra x).
Notation "\226\136\163 x , y , .. , z \226\159\169" := (kron .. (kron \226\136\163 x \226\159\169 \226\136\163 y \226\159\169) .. \226\136\163 z \226\159\169) (at level 0).
Definition bool_to_ket (b : bool) : Matrix 2 1 := if b then \226\136\1631\226\159\169 else \226\136\1630\226\159\169.
Definition bool_to_matrix (b : bool) : Matrix 2 2 := if b then \226\136\1631\226\159\169\226\159\1681\226\136\163 else \226\136\1630\226\159\169\226\159\1680\226\136\163.
Definition bool_to_matrix' (b : bool) : Matrix 2 2 :=
  fun i j =>
  if negb b && (i =? 0) && (j =? 0)
  then 1
  else if b && (i =? 1) && (j =? 1) then 1 else 0.
Lemma bool_to_matrix_eq : forall b, bool_to_matrix b == bool_to_matrix' b.
Proof.
(destruct b; lma).
Qed.
Lemma bool_to_ket_matrix_eq :
  forall b, outer_product (bool_to_ket b) (bool_to_ket b) == bool_to_matrix b.
Proof.
(destruct b; lma).
Qed.
Definition bools_to_matrix (l : list bool) : Square (2 ^ length l) :=
  big_kron (map bool_to_matrix l).
Definition hadamard : Square 2 :=
  fun i j => if (i =? 1) && (j =? 1) then - / \226\136\154 2 else / \226\136\154 2.
Fixpoint hadamard_k (k : nat) : Matrix (2 ^ k) (2 ^ k) :=
  match k with
  | 0 => I 1
  | S k' => hadamard \226\138\151 hadamard_k k'
  end.
Lemma hadamard_1 : hadamard_k 1 == hadamard.
Proof.
(apply kron_1_r).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqyqMySW"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Definition \207\131x : Square 2 := fun i j => if i + j =? 1 then 1 else 0.
Definition \207\131y : Square 2 := fun i j => if i + j =? 1 then (- 1) ^ i * Ci else 0.
Definition \207\131z : Square 2 := fun i j => if i =? j then (- 1) ^ i else 0.
Definition phase_shift (\207\149 : R) : Square 2 :=
  fun i j =>
  if (i =? 0) && (j =? 0) then 1 else if (i =? 1) && (j =? 1) then Cexp \207\149 else 0.
Lemma MmultX1 : \207\131x \195\151 \226\136\1631\226\159\169 == \226\136\1630\226\159\169.
Proof.
lma.
Qed.
Lemma Mmult1X : \226\159\1681\226\136\163 \195\151 \207\131x == \226\159\1680\226\136\163.
Proof.
lma.
Qed.
Lemma MmultX0 : \207\131x \195\151 \226\136\1630\226\159\169 == \226\136\1631\226\159\169.
Proof.
lma.
Qed.
Lemma Mmult0X : \226\159\1680\226\136\163 \195\151 \207\131x == \226\159\1681\226\136\163.
Proof.
lma.
Qed.
Hint Rewrite Mmult0X Mmult1X MmultX0 MmultX1 : M_db.
Definition control {n : nat} (A : Matrix n n) : Matrix (2 * n) (2 * n) :=
  fun x y =>
  if (x <? n) && (y =? x)
  then 1
  else if (n <=? x) && (n <=? y) then A (x - n)%nat (y - n)%nat else 0.
Definition cnot : Matrix (2 * 2) (2 * 2) :=
  fun i j => if (i =? j) && (i <? 2) || (i + j =? 5) then 1 else 0.
Lemma cnot_eq : cnot == control \207\131x.
Proof.
lma.
Qed.
Definition notc : Matrix (2 * 2) (2 * 2) :=
  fun i j => if (i + j =? 0) || (i + j =? 4) then 1 else 0.
Lemma control_compat : forall n (A B : Matrix n n), A == B -> control A == control B.
Proof.
(intros n A B H i j Hi Hj).
(unfold control).
(destruct ((i <? n) && (j =? i)), ((n <=? i) && (n <=? j)); trivial).
(rewrite H; trivial; lia).
Qed.
Add Parametric Morphism  n : @control n with signature mat_equiv ==> mat_equiv as
 control_mor.
Proof.
(intros).
(apply control_compat; easy).
Qed.
Definition swap : Matrix (2 * 2) (2 * 2) :=
  fun i j => if (i + j =? 0) || (i * j =? 2) || (i + j =? 6) then 1 else 0.
Hint Unfold qubit0 qubit1 hadamard \207\131x \207\131y \207\131z phase_shift control cnot notc swap bra
  ket: U_db.
Lemma swap_swap : swap \195\151 swap == I (2 * 2).
Proof.
lma.
Qed.
Lemma swap_swap_r : forall A : Matrix (2 * 2) (2 * 2), A \195\151 swap \195\151 swap == A.
Proof.
lma.
Qed.
Fixpoint swap_to_0_aux (n i : nat) {struct i} : Matrix (2 ^ n) (2 ^ n) :=
  match i with
  | O => swap \226\138\151 I (2 ^ (n - 2))
  | S i' =>
      I (2 ^ i) \226\138\151 swap \226\138\151 I (2 ^ (n - i - 2)) \195\151 swap_to_0_aux n i'
      \195\151 (I (2 ^ i) \226\138\151 swap \226\138\151 I (2 ^ (n - i - 2)))
  end.
Definition swap_to_0 (n i : nat) : Matrix (2 ^ n) (2 ^ n) :=
  match i with
  | O => I (2 ^ n)
  | S i' => swap_to_0_aux n i'
  end.
Fixpoint swap_two_aux (n i j : nat) : Matrix (2 ^ n) (2 ^ n) :=
  match i with
  | O => swap_to_0 n j
  | S i' => I 2 \226\138\151 swap_two_aux (n - 1) i' (j - 1)
  end.
Definition swap_two (n i j : nat) : Matrix (2 ^ n) (2 ^ n) :=
  if i =? j
  then I (2 ^ n)
  else if i <? j then swap_two_aux n i j else swap_two_aux n j i.
Fixpoint move_to_0_aux (n i : nat) {struct i} : Matrix (2 ^ n) (2 ^ n) :=
  match i with
  | O => swap \226\138\151 I (2 ^ (n - 2))
  | S i' => move_to_0_aux n i' \195\151 (I (2 ^ i) \226\138\151 swap \226\138\151 I (2 ^ (n - i - 2)))
  end.
Definition move_to_0 (n i : nat) : Matrix (2 ^ n) (2 ^ n) :=
  match i with
  | O => I (2 ^ n)
  | S i' => move_to_0_aux n i'
  end.
Fixpoint move_to (n i k : nat) : Matrix (2 ^ n) (2 ^ n) :=
  match k with
  | O => move_to_0 n i
  | S k' => I 2 \226\138\151 move_to (n - 1) (i - 1) k'
  end.
Definition WF_Unitary {n : nat} (U : Matrix n n) : Prop := (U) \226\128\160 \195\151 U == I n.
Hint Unfold WF_Unitary: U_db.
Lemma H_unitary : WF_Unitary hadamard.
Proof.
(by_cell; autounfold with U_db; simpl; group_radicals; lca).
Qed.
Lemma \207\131x_unitary : WF_Unitary \207\131x.
Proof.
lma.
Qed.
Lemma \207\131y_unitary : WF_Unitary \207\131y.
Proof.
lma.
Qed.
Lemma \207\131z_unitary : WF_Unitary \207\131z.
Proof.
lma.
Qed.
Lemma phase_unitary : forall \207\149, @WF_Unitary 2 (phase_shift \207\149).
Proof.
(by_cell; autounfold with U_db; simpl; try lca).
(apply c_proj_eq; simpl; try lra).
autorewrite with R_db.
replace (cos \207\149 * cos \207\149)%R with (cos \207\149)\194\178 by easy.
replace (sin \207\149 * sin \207\149)%R with (sin \207\149)\194\178 by easy.
(rewrite Rplus_comm).
(rewrite sin2_cos2).
reflexivity.
Qed.
Lemma control_unitary :
  forall n (A : Matrix n n), WF_Unitary A -> WF_Unitary (control A).
Proof.
(intros n A U).
(unfold WF_Unitary in *).
(unfold control, adjoint, Mmult, I).
(intros x y Hx Hy).
(simpl).
(bdestruct\206\169 (x =? y)).
-
(subst; simpl).
(rewrite Csum_sum).
(bdestruct\206\169 (y <? n + (n + 0))).
+
(bdestruct\206\169 (n <=? y)).
*
(rewrite Csum_0_bounded).
Csimpl.
(rewrite (Csum_eq_bounded _ (fun x => (A x (y - n)%nat) ^* * A x (y - n)%nat))).
++
(unfold control, adjoint, Mmult, I in U).
(rewrite Nat.add_0_r).
(rewrite U by lia).
(rewrite Nat.eqb_refl).
easy.
++
(intros x L).
(bdestruct\206\169 (n + x <? n)).
(bdestruct\206\169 (n <=? n + x)).
(rewrite minus_plus).
easy.
++
(intros x L).
(bdestruct\206\169 (y =? x)).
(rewrite andb_false_r).
(bdestruct\206\169 (n <=? x)).
lca.
*
(rewrite (Csum_unique _ 1 _ y); try lia).
(rewrite Csum_0_bounded; try lca).
++
(intros).
(rewrite andb_false_r).
(bdestruct\206\169 (n + x <? n)).
(simpl).
lca.
++
(rewrite Nat.eqb_refl).
(bdestruct\206\169 (y <? n)).
lca.
++
(intros).
(bdestruct\206\169 (y =? x')).
(repeat rewrite andb_false_r).
lca.
-
(simpl).
(rewrite Csum_sum).
(bdestruct\206\169 (y <? n + (n + 0))).
+
(bdestruct\206\169 (n <=? y)).
*
(rewrite Csum_0_bounded).
Csimpl.
(bdestruct\206\169 (n <=? x)).
(rewrite (Csum_eq_bounded _ (fun z => (A z (x - n)%nat) ^* * A z (y - n)%nat))).
++
(unfold control, adjoint, Mmult, I in U).
(rewrite Nat.add_0_r).
(rewrite U by lia).
(bdestruct\206\169 (x - n =? y - n)).
(simpl).
easy.
++
(intros z L).
(bdestruct\206\169 (n + z <? n)).
(bdestruct\206\169 (n <=? n + z)).
(rewrite minus_plus).
easy.
++
(rewrite Nat.add_0_r).
(rewrite Csum_0_bounded; trivial).
(intros z L).
(bdestruct\206\169 (n + z <? n)).
(rewrite andb_false_r).
Csimpl.
easy.
++
(intros z L).
(bdestruct\206\169 (z <? n)).
(bdestruct\206\169 (n <=? z)).
(bdestruct\206\169 (x =? z); bdestruct\206\169 (y =? z); try lca).
*
(bdestruct\206\169 (n <=? x)).
++
(rewrite Csum_0_bounded).
(rewrite Csum_0_bounded).
lca.
**
(intros z L).
(bdestruct\206\169 (n + z <? n)).
(rewrite andb_false_r).
lca.
**
(intros z L).
(bdestruct\206\169 (z <? n)).
(rewrite andb_false_r).
(bdestruct\206\169 (x =? z); bdestruct\206\169 (y =? z); try lca).
(bdestruct\206\169 (n <=? z)).
lca.
++
(rewrite 2!Csum_0_bounded; [ lca |  |  ]).
**
(intros z L).
(rewrite andb_false_r).
(bdestruct\206\169 (x =? n + z); bdestruct\206\169 (y =? n + z); rewrite andb_false_r; lca).
**
(intros z L).
(rewrite andb_false_r).
(bdestruct\206\169 (x =? z); bdestruct\206\169 (y =? z); rewrite andb_false_r; lca).
Qed.
Lemma transpose_unitary :
  forall n (A : Matrix n n), WF_Unitary A -> WF_Unitary (A) \226\128\160.
Proof.
(intros).
(unfold WF_Unitary in *).
(rewrite adjoint_involutive).
(apply Minv_left in H as [_ S]).
assumption.
Qed.
Lemma cnot_unitary : WF_Unitary cnot.
Proof.
lma.
Qed.
Lemma id_unitary : forall n, WF_Unitary (I n).
Proof.
(intros n).
(unfold WF_Unitary).
(rewrite id_adjoint_eq).
(apply Mmult_1_l).
Qed.
Lemma swap_unitary : WF_Unitary swap.
Proof.
lma.
Qed.
Lemma zero_not_unitary : forall n, ~ WF_Unitary (@Zero (2 ^ n) (2 ^ n)).
Proof.
(intros n).
(assert (2 <> 0)%nat by lia).
specialize (pow_positive 2 n H) as P.
clear H.
(intros U).
specialize (U _ _ P P).
revert U.
(rewrite Mmult_0_r; trivial).
(unfold I, Zero).
(simpl).
(intros U).
(inversion U).
lra.
Qed.
Lemma kron_unitary :
  forall {m} {n} (A : Matrix m m) (B : Matrix n n),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary (A \226\138\151 B).
Proof.
(intros m n A B UA UB).
(unfold WF_Unitary in *).
(rewrite kron_adjoint).
(rewrite kron_mixed_product).
(rewrite UA, UB).
(rewrite id_kron).
easy.
Qed.
Lemma Mmult_unitary :
  forall (n : nat) (A : Square n) (B : Square n),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary (A \195\151 B).
Proof.
(intros n A B UA UB).
(unfold WF_Unitary in *).
restore_dims.
Msimpl.
(rewrite Mmult_assoc).
(rewrite <- (Mmult_assoc (A) \226\128\160)).
(rewrite UA).
Msimpl.
(apply UB).
Qed.
Definition id_adj := @id_adjoint_eq.
Lemma hadamard_adj : (hadamard) \226\128\160 == hadamard.
Proof.
lma.
Qed.
Lemma \207\131x_adj : (\207\131x) \226\128\160 == \207\131x.
Proof.
lma.
Qed.
Lemma \207\131y_adj : (\207\131y) \226\128\160 == \207\131y.
Proof.
lma.
Qed.
Lemma \207\131z_adj : (\207\131z) \226\128\160 == \207\131z.
Proof.
lma.
Qed.
Lemma cnot_adj : (cnot) \226\128\160 == cnot.
Proof.
lma.
Qed.
Lemma swap_adj : (swap) \226\128\160 == swap.
Proof.
lma.
Qed.
Lemma control_adj : forall n (U : Square n), (control U) \226\128\160 == control (U) \226\128\160.
Proof.
(intros n U i j Hi Hj).
(unfold control, adjoint).
(rewrite Nat.eqb_sym).
(bdestruct (j =? i)).
-
subst.
(bdestruct (i <? n); bdestruct (n <=? i); try lia; simpl; lca).
-
(rewrite 2!andb_false_r).
(rewrite andb_comm).
(rewrite (if_dist _ _ _ Cconj)).
(rewrite Cconj_0).
reflexivity.
Qed.
Lemma phase_adj : forall \207\149, (phase_shift \207\149) \226\128\160 == phase_shift (- \207\149).
Proof.
(intros \207\149).
(unfold phase_shift, adjoint).
(by_cell; try lca).
(unfold Cexp, Cconj).
(rewrite cos_neg, sin_neg).
easy.
Qed.
Lemma braqubit0_adj : (\226\136\1630\226\159\169\226\159\1680\226\136\163) \226\128\160 == \226\136\1630\226\159\169\226\159\1680\226\136\163.
Proof.
lma.
Qed.
Lemma braqubit1_adj : (\226\136\1631\226\159\169\226\159\1681\226\136\163) \226\128\160 == \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
lma.
Qed.
Hint Rewrite
 hadamard_adj \207\131x_adj \207\131y_adj \207\131z_adj cnot_adj swap_adj braqubit1_adj braqubit0_adj
 control_adj phase_adj : M_db.
Lemma cnot_decomposition : \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 \207\131x .+ \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I 2 == cnot.
Proof.
lma.
Qed.
Lemma notc_decomposition : \207\131x \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 .+ I 2 \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 == notc.
Proof.
lma.
Qed.
Definition positive_semidefinite {n} (A : Square n) : Prop :=
  forall z : Vector n, fst (((z) \226\128\160 \195\151 A \195\151 z) O O) >= 0.
Lemma mat_equiv_element_property :
  forall {m} {n} (P : C -> Prop) (A B : Matrix m n) (i j : nat),
  A == B -> lt i m -> lt j n -> P (A i j) -> P (B i j).
Proof.
(intros).
(rewrite <- H; easy).
Qed.
Lemma positive_semidefinite_compat :
  forall {n} (A B : Square n),
  A == B -> positive_semidefinite A -> positive_semidefinite B.
Proof.
(intros).
(unfold positive_semidefinite in *).
(intros z).
(eapply mat_equiv_element_property; try lia).
(rewrite <- H).
reflexivity.
(apply H0).
Qed.
Lemma pure_psd : forall (n : nat) (\207\149 : Vector n), positive_semidefinite (\207\149 \195\151 (\207\149) \226\128\160).
Proof.
(intros).
(unfold positive_semidefinite in *).
(intros z).
(eapply mat_equiv_element_property; try lia).
-
(repeat rewrite Mmult_assoc by lia).
(remember ((\207\149) \226\128\160 \195\151 z) as \207\136).
(repeat rewrite <- Mmult_assoc by lia).
(rewrite <- (adjoint_involutive \207\149)).
(rewrite <- Mmult_adjoint).
(rewrite <- Heq\207\136).
(unfold Mmult).
(simpl).
(intros i j Hi Hj).
(rewrite Cplus_0_l).
(destruct i, j; try lia).
(unfold adjoint).
subst.
reflexivity.
-
(remember ((\207\149) \226\128\160 \195\151 z) as \207\136).
(simpl).
autorewrite with R_db.
replace (fst (z 1%nat 0%nat) * fst (z 1%nat 0%nat))%R with 
 (fst (z 1%nat 0%nat))\194\178 by easy.
replace (snd (z 1%nat 0%nat) * snd (z 1%nat 0%nat))%R with 
 (snd (z 1%nat 0%nat))\194\178 by easy.
(apply Rle_ge).
(apply Rplus_le_le_0_compat; apply Rle_0_sqr).
Qed.
Lemma braket0_psd : positive_semidefinite \226\136\1630\226\159\169\226\159\1680\226\136\163.
Proof.
(apply pure_psd).
Qed.
Lemma braket1_psd : positive_semidefinite \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
(apply pure_psd).
Qed.
Lemma H0_psd : positive_semidefinite (hadamard \195\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \195\151 hadamard).
Proof.
(eapply positive_semidefinite_compat).
-
(repeat rewrite Mmult_assoc).
(rewrite <- hadamard_adj  at 2).
(rewrite <- Mmult_adjoint).
(repeat rewrite <- Mmult_assoc).
reflexivity.
-
(apply pure_psd).
Qed.
Notation Density n:= (Matrix n n) (only parsing).
Definition Classical {n} (\207\129 : Density n) := forall i j, i <> j -> \207\129 i j = 0.
Definition Pure_State_Vector {n} (\207\134 : Vector n) : Prop := (\207\134) \226\128\160 \195\151 \207\134 == I 1.
Definition Pure_State {n} (\207\129 : Density n) : Prop :=
  exists \207\134, Pure_State_Vector \207\134 /\ \207\129 == \207\134 \195\151 (\207\134) \226\128\160.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma pure_state_compat :
  forall {n} (A B : Density n), A == B -> Pure_State A -> Pure_State B.
Proof.
(intros).
(unfold Pure_State in *).
(destruct H0 as [v HA]).
exists v.
(rewrite <- H).
assumption.
Qed.
Add Parametric Morphism  n : @Pure_State n with signature 
 mat_equiv ==> iff as pure_state_mor.
Proof.
(intros; split; apply pure_state_compat; easy).
Qed.
Lemma mixed_state_compat :
  forall {n} (A B : Density n), A == B -> Mixed_State A -> Mixed_State B.
Proof.
(intros n A B E MA).
gen B.
(induction MA as [A| r A A1 A2]).
-
(intros).
(apply Pure_S).
(apply (pure_state_compat A); assumption).
-
(intros).
(apply (Mix_S r _ A1 A2); trivial).
(rewrite <- E; assumption).
Qed.
Add Parametric Morphism  n : @Mixed_State n with signature 
 mat_equiv ==> iff as mixed_state_mor.
Proof.
(intros; split; apply mixed_state_compat; easy).
Qed.
Lemma mixed_state_cond :
  forall {n} (a b : R) (A B : Square n),
  0 <= a ->
  0 <= b ->
  a + b = 1 -> Mixed_State A -> Mixed_State B -> Mixed_State (a .* A .+ b .* B).
Proof.
(intros n a b A B Pa Pb Sab MA MB).
(destruct Pa; [ destruct Pb |  ]).
-
(eapply (Mix_S (RtoC a) _ A B); trivial).
+
(simpl).
(inversion Sab).
lra.
+
replace (1 - a) with RtoC b by (rewrite <- Sab; lca).
reflexivity.
-
(rewrite <- H0 in *).
(rewrite Cplus_0_r in Sab).
(rewrite Sab).
(rewrite Mscale_0_l, Mplus_0_r, Mscale_1_l).
easy.
-
(rewrite <- H in *).
(rewrite Cplus_0_l in Sab).
(rewrite Sab).
(rewrite Mscale_0_l, Mplus_0_l, Mscale_1_l).
easy.
Qed.
Lemma pure0 : Pure_State \226\136\1630\226\159\169\226\159\1680\226\136\163.
Proof.
exists \226\136\1630\226\159\169.
(split; lma).
Qed.
Lemma pure1 : Pure_State \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
exists \226\136\1631\226\159\169.
(split; lma).
Qed.
Lemma pure_id1 : Pure_State (I 1).
Proof.
exists (I 1).
(split; lma).
Qed.
Lemma pure_dim1 : forall \207\129 : Square 1, Pure_State \207\129 -> \207\129 == I 1.
Proof.
(intros \207\129 [\207\134 [IP1 E]]).
(apply Minv_flip in IP1).
(rewrite E; easy).
Qed.
Lemma pure_state_kron :
  forall m n (\207\129 : Square m) (\207\134 : Square n),
  Pure_State \207\129 -> Pure_State \207\134 -> Pure_State (\207\129 \226\138\151 \207\134).
Proof.
(intros m n \207\129 \207\134 [u [Pu E\207\129]] [v [Pv E\207\134]]).
exists (u \226\138\151 v).
split.
-
(unfold Pure_State_Vector in *).
restore_dims.
Msimpl.
(rewrite Pu, Pv).
lma.
-
(rewrite E\207\129, E\207\134).
restore_dims.
Msimpl.
reflexivity.
Qed.
Lemma mixed_state_kron :
  forall m n (\207\129 : Square m) (\207\134 : Square n),
  Mixed_State \207\129 -> Mixed_State \207\134 -> Mixed_State (\207\129 \226\138\151 \207\134).
Proof.
(intros m n \207\129 \207\134 M\207\129 M\207\134).
(induction M\207\129).
(induction M\207\134).
-
(apply Pure_S).
(apply pure_state_kron; easy).
-
(rewrite H2).
(rewrite kron_plus_dist_l).
(rewrite 2!Mscale_kron_dist_r).
(eapply (Mix_S p); easy).
-
(rewrite H1).
(rewrite kron_plus_dist_r).
(rewrite 2!Mscale_kron_dist_l).
(eapply (Mix_S p); easy).
Qed.
Lemma pure_state_trace_1 : forall {n} (\207\129 : Density n), Pure_State \207\129 -> trace \207\129 = 1.
Proof.
(intros n \207\129 [u [Uu E]]).
(unfold Pure_State_Vector in Uu).
subst.
(rewrite E).
clear - Uu.
(unfold trace).
(unfold Mmult, adjoint in *).
(simpl in *).
(erewrite Csum_eq_bounded; intros).
(rewrite (Uu O O) by lia).
easy.
(simpl; lca).
Qed.
Lemma mixed_state_trace_1 : forall {n} (\207\129 : Density n), Mixed_State \207\129 -> trace \207\129 = 1.
Proof.
(intros n \207\129 M).
(induction M).
-
(apply pure_state_trace_1).
easy.
-
(rewrite H1).
(rewrite trace_plus_dist).
(rewrite 2!trace_mult_dist).
(rewrite IHM1, IHM2).
lca.
Qed.
Lemma mixed_state_diag_in01 :
  forall {n} (\207\129 : Density n) i, Mixed_State \207\129 -> lt i n -> 0 <= fst (\207\129 i i) <= 1.
Proof.
(intros n \207\129 i M L).
(induction M).
-
(destruct H as [\207\134 [IP1 E\207\129]]).
(rewrite E\207\129; trivial).
(unfold Mmult, adjoint in *).
(simpl in *).
(rewrite Rplus_0_l).
(unfold Pure_State_Vector in IP1).
specialize (IP1 O O Nat.lt_0_1 Nat.lt_0_1).
(unfold I in IP1).
(simpl in IP1).
(apply f_equal with (f := fst) in IP1).
(simpl in IP1).
(rewrite <- IP1).
split.
+
(unfold Rminus).
(rewrite <- Ropp_mult_distr_r).
(rewrite Ropp_involutive).
(rewrite <- Rplus_0_r  at 1).
(apply Rplus_le_compat; apply Rle_0_sqr).
+
(unfold Mmult).
(match goal with
 | |- ?x <= fst (Csum ?f ?m) => specialize (Csum_member_le f n) as res
 end).
(simpl in *).
(unfold Rminus in *).
(rewrite <- Ropp_mult_distr_r).
(rewrite Ropp_mult_distr_l).
(apply res with (x := i); trivial).
(intros x).
(unfold Rminus).
(rewrite <- Ropp_mult_distr_l).
(rewrite Ropp_involutive).
(rewrite <- Rplus_0_r  at 1).
(apply Rplus_le_compat; apply Rle_0_sqr).
-
split.
+
(assert (0 <= fst p * fst (\207\1291 i i))).
(apply Rmult_le_pos; lra).
(assert (0 <= (1 - fst p) * fst (\207\1292 i i))).
(apply Rmult_le_pos; lra).
specialize (H1 i i L L).
(rewrite H1).
(unfold Mplus, scale).
(simpl).
(rewrite H; lra).
+
(assert (fst p * fst (\207\1291 i i) <= fst p)).
(rewrite <- Rmult_1_r).
(apply Rmult_le_compat_l; lra).
(assert ((1 - fst p) * fst (\207\1292 i i) <= 1 - fst p)).
(rewrite <- Rmult_1_r).
(apply Rmult_le_compat_l; lra).
specialize (H1 i i L L).
(rewrite H1).
(unfold Mplus, scale).
(simpl).
(rewrite H; lra).
Qed.
Lemma mixed_state_diag_real :
  forall {n} (\207\129 : Density n) i, lt i n -> Mixed_State \207\129 -> snd (\207\129 i i) = 0.
Proof.
(intros n \207\129 i L M).
(induction M).
-
(unfold Pure_State in H).
(destruct H as [\207\134 [IP1 E\207\129]]).
(rewrite E\207\129 by lia).
(simpl; lra).
-
(simpl).
(rewrite H1 by lia).
(unfold Mplus; simpl).
(rewrite IHM1, IHM2).
(rewrite H; lra).
Qed.
Lemma mixed_dim1 : forall \207\129 : Square 1, Mixed_State \207\129 -> \207\129 == I 1.
Proof.
(intros \207\129 M).
(induction M).
-
(apply pure_dim1; trivial).
-
(rewrite H1).
(rewrite IHM1, IHM2).
lma.
Qed.
Definition Superoperator m n := Density m -> Density n.
Definition WF_Superoperator {m} {n} (f : Superoperator m n) :=
  forall \207\129, Mixed_State \207\129 -> Mixed_State (f \207\129).
Definition super {m} {n} (M : Matrix m n) : Superoperator n m :=
  fun \207\129 => M \195\151 \207\129 \195\151 (M) \226\128\160.
Lemma super_I : forall n \207\129, super (I n) \207\129 == \207\129.
Proof.
(intros).
(unfold super).
Msimpl.
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqfxxyML"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Parametric Morphism  m n : @super m n with signature
 mat_equiv ==> mat_equiv ==> mat_equiv as super_mor.
Proof.
(intros).
(unfold super).
(rewrite H, H0).
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq3FYT6X"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma super_outer_product :
  forall m (\207\134 : Matrix m 1) (U : Matrix m m),
  super U (outer_product \207\134 \207\134) == outer_product (U \195\151 \207\134) (U \195\151 \207\134).
Proof.
(intros).
(unfold super, outer_product).
Msimpl.
(repeat rewrite Mmult_assoc).
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq7dZmLo"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition compose_super {m} {n} {p} (g : Superoperator n p) 
  (f : Superoperator m n) : Superoperator m p := fun \207\129 => g (f \207\129).
Lemma compose_super_correct :
  forall {m} {n} {p} (g : Superoperator n p) (f : Superoperator m n),
  WF_Superoperator g -> WF_Superoperator f -> WF_Superoperator (compose_super g f).
Proof.
(intros m n p g f pf_g pf_f).
(unfold WF_Superoperator).
(intros \207\129 mixed).
(unfold compose_super).
(apply pf_g).
(apply pf_f).
auto.
Qed.
Definition sum_super {m} {n} (f g : Superoperator m n) : 
  Superoperator m n := fun \207\129 => 1 / 2 .* f \207\129 .+ (1 - 1 / 2) .* g \207\129.
Lemma sum_super_correct :
  forall m n (f g : Superoperator m n),
  WF_Superoperator f -> WF_Superoperator g -> WF_Superoperator (sum_super f g).
Proof.
(intros m n f g wf_f wf_g \207\129 pf_\207\129).
(unfold sum_super).
(set (wf_f' := wf_f _ pf_\207\129)).
(set (wf_g' := wf_g _ pf_\207\129)).
(eapply (Mix_S (1 / 2) _ (f \207\129) (g \207\129)); auto).
(simpl; lra).
(simpl; lra).
reflexivity.
Qed.
Definition SZero {m} {n} : Superoperator m n := fun \207\129 => Zero.
Definition Splus {m} {n} (S T : Superoperator m n) : Superoperator m n :=
  fun \207\129 => S \207\129 .+ T \207\129.
Definition new0_op : Superoperator 1 2 := super \226\136\1630\226\159\169.
Definition new1_op : Superoperator 1 2 := super \226\136\1631\226\159\169.
Definition meas_op : Superoperator 2 2 := Splus (super \226\136\1630\226\159\169\226\159\1680\226\136\163) (super \226\136\1631\226\159\169\226\159\1681\226\136\163).
Definition discard_op : Superoperator 2 1 := Splus (super \226\159\1680\226\136\163) (super \226\159\1681\226\136\163).
Lemma pure_unitary :
  forall {n} (U \207\129 : Matrix n n),
  WF_Unitary U -> Pure_State \207\129 -> Pure_State (super U \207\129).
Proof.
(intros n U \207\129 H [\207\134 [IP1 E\207\129]]).
(eapply pure_state_compat).
(unfold super).
(rewrite E\207\129).
easy.
exists (U \195\151 \207\134).
split.
-
(unfold Pure_State_Vector in *).
(rewrite (Mmult_adjoint U \207\134)).
(rewrite Mmult_assoc).
(rewrite <- (Mmult_assoc (U) \226\128\160)).
(unfold WF_Unitary in H).
(rewrite H, Mmult_1_l, IP1; easy).
-
(unfold super).
(rewrite (Mmult_adjoint U \207\134)).
(repeat rewrite Mmult_assoc).
reflexivity.
Qed.
Lemma mixed_unitary :
  forall {n} (U \207\129 : Matrix n n),
  WF_Unitary U -> Mixed_State \207\129 -> Mixed_State (super U \207\129).
Proof.
(intros n U \207\129 H M).
(induction M).
+
(apply Pure_S).
(apply pure_unitary; trivial).
+
(unfold WF_Unitary, super in *).
(rewrite H2).
(rewrite Mmult_plus_dist_l).
(rewrite Mmult_plus_dist_r).
(rewrite 2!Mscale_mult_dist_r).
(rewrite 2!Mscale_mult_dist_l).
(eapply (Mix_S p); easy).
Qed.
Lemma super_unitary_correct :
  forall {n} (U : Matrix n n), WF_Unitary U -> WF_Superoperator (super U).
Proof.
(intros n U H \207\129 M\207\129).
(apply mixed_unitary; easy).
Qed.
Lemma compose_super_assoc :
  forall {m} {n} {p} {q} (f : Superoperator m n) (g : Superoperator n p)
    (h : Superoperator p q),
  compose_super (compose_super f g) h = compose_super f (compose_super g h).
Proof.
easy.
Qed.
Lemma swap_spec : forall q q' : Vector 2, swap \195\151 (q \226\138\151 q') == q' \226\138\151 q.
Proof.
lma.
Qed.
Hint Rewrite swap_spec : M_db.
Example swap_to_0_test_24 :
  forall q0 q1 q2 q3 : Vector 2,
  swap_to_0 4 2 \195\151 (q0 \226\138\151 q1 \226\138\151 q2 \226\138\151 q3) == q2 \226\138\151 q1 \226\138\151 q0 \226\138\151 q3.
Proof.
(intros q0 q1 q2 q3).
(unfold swap_to_0, swap_to_0_aux).
(simpl).
(rewrite Mmult_assoc).
(repeat rewrite Mmult_assoc).
(rewrite (kron_assoc q0 q1)).
Msimpl.
(repeat rewrite kron_assoc).
restore_dims.
(rewrite <- (kron_assoc q0 q2)).
Msimpl.
(rewrite (kron_assoc q2 q0)).
Msimpl.
(rewrite <- (kron_assoc q0)).
Msimpl.
(rewrite (kron_assoc q1 q0)).
reflexivity.
Qed.
Lemma swap_two_base : swap_two 2 1 0 == swap.
Proof.
lma.
Qed.
Lemma swap_second_two : swap_two 3 1 2 == I 2 \226\138\151 swap.
Proof.
(unfold swap_two).
(simpl).
(rewrite (kron_1_r swap)).
reflexivity.
Qed.
Lemma swap_0_2 : swap_two 3 0 2 == I 2 \226\138\151 swap \195\151 (swap \226\138\151 I 2) \195\151 (I 2 \226\138\151 swap).
Proof.
(unfold swap_two).
(simpl).
(rewrite (kron_1_r (I 2 \226\138\151 swap))).
reflexivity.
Qed.
Example move_to_0_test_24 :
  forall q0 q1 q2 q3 : Vector 2,
  move_to_0 4 2 \195\151 (q0 \226\138\151 q1 \226\138\151 q2 \226\138\151 q3) == q2 \226\138\151 q0 \226\138\151 q1 \226\138\151 q3.
Proof.
(intros q0 q1 q2 q3 WF0 WF1 WF2 WF3).
(unfold move_to_0, move_to_0_aux).
(repeat rewrite Mmult_assoc).
(rewrite (kron_assoc q0 q1)).
