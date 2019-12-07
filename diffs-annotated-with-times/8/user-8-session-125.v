Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqnNPFXM"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Require Import TypeChecking.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqyNKPug"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Bullet Behavior Strict Subproofs.
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.
Lemma init_qubit1 : (\226\159\166 init true \226\159\167) (I 1) == \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
matrix_denote.
Msimpl.
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqjhuybc"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma unitary_transpose_id_qubit :
  forall U : Unitary Qubit, unitary_transpose U \226\137\161 id_circ.
Proof.
(unfold HOAS_Equiv).
(intros U \207\129 safe).
Timeout 1 About unitary_gate_unitary.
Timeout 1 Print unitary_gate_unitary.
specialize (unitary_gate_unitary U) as inv.
(unfold WF_Unitary in inv).
(simpl in *).
matrix_denote.
setoid_rewrite denote_unitary_transpose.
(simpl in *; Msimpl).
(repeat rewrite Mmult_assoc; try rewrite inv).
(repeat rewrite <- Mmult_assoc; try rewrite inv).
Msimpl.
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqllH2jR"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma unitary_transpose_id : forall W (U : Unitary W), unitary_transpose U \226\137\161 id_circ.
Proof.
(intros W U \207\129 safe).
matrix_denote.
(rewrite add_fresh_split).
(rewrite subst_pat_fresh by constructor).
(unfold denote_db_box).
(simpl).
(unfold compose_super, super, pad).
(repeat rewrite Nat.add_sub).
(rewrite Nat.sub_diag).
Msimpl.
(destruct W; try (solve [ inversion U ])).
-
(simpl).
(unfold denote_pat; simpl).
(unfold swap_list; simpl).
(unfold swap_two; simpl).
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-15 15:13:43.030000.*)

