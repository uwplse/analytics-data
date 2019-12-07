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
Arguments WF_Unitary {n} U /.
Lemma unitary_transpose_id_qubit :
  forall U : Unitary Qubit, unitary_transpose U \226\137\161 id_circ.
Proof.
(unfold HOAS_Equiv).
(intros U \207\129 safe).
specialize (unitary_gate_unitary U) as inv.
(simpl in *).
matrix_denote.
setoid_rewrite denote_unitary_transpose.
(simpl in *; Msimpl).
(repeat rewrite Mmult_assoc; try rewrite inv).
(repeat rewrite <- Mmult_assoc; try rewrite inv).
Msimpl.
reflexivity.
Qed.
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
matrix_denote.
Msimpl.
(rewrite Mmult_assoc).
specialize (unitary_gate_unitary U) as inv.
(simpl_rewrite @denote_unitary_transpose).
(simpl in *).
Msimpl.
(repeat rewrite Mmult_assoc).
(rewrite inv).
(repeat rewrite <- Mmult_assoc).
(rewrite inv).
Msimpl.
easy.
-
(simpl).
(unfold denote_pat; simpl).
Msimpl.
(rewrite Mmult_assoc).
(unfold super).
(simpl).
(remember (W1 \226\138\151 W2) as W).
(remember (pat_to_list (add_fresh_pat W [])) as li).
(assert (inv : WF_Unitary (denote_ctrls (\226\159\166 W \226\159\167) U li))).
{
(apply denote_ctrls_unitary).
(intros).
(rewrite Heqli in H).
(simpl).
(rewrite (ctx_wtype_size _ (add_fresh_pat W []) (add_fresh_state W []))).
(eapply pat_to_list_bounded).
split.
validate.
(rewrite merge_nil_r).
easy.
(eapply get_fresh_typed).
(rewrite get_fresh_split).
specialize (add_fresh_state_merge W [] _ eq_refl) as AFE.
(rewrite merge_nil_l in AFE).
(inversion AFE).
(rewrite <- H1).
easy.
(rewrite <- add_fresh_pat_eq).
(rewrite subst_pat_fresh by constructor).
easy.
(apply add_fresh_typed_empty).
(rewrite add_fresh_split).
easy.
subst.
(rewrite size_wtype_length).
easy.
}
(* Auto-generated comment: Succeeded. *)

