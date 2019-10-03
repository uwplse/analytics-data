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
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqZYfXX9"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
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
(* Auto-generated comment: Succeeded. *)

