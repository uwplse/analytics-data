Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqnNPFXM"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 85.
Set Silent.
Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import DBCircuits.
Unset Silent.
Require Import TypeChecking.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqyNKPug"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Silent.
Set Bullet Behavior Strict Subproofs.
Global Unset Asymmetric Patterns.
Delimit Scope matrix_scope with M.
Lemma init_qubit1 : (\226\159\166 init true \226\159\167) (I 1) == \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
Unset Silent.
Show.
Set Printing Width 85.
Show.
matrix_denote.
Msimpl.
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqjhuybc"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Unset Silent.
Set Printing Width 85.
Set Silent.
Lemma unitary_transpose_id_qubit :
  forall U : Unitary Qubit, unitary_transpose U \226\137\161 id_circ.
Proof.
(unfold HOAS_Equiv).
Unset Silent.
Show.
Set Printing Width 85.
Show.
Set Silent.
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
Unset Silent.
Show.
Set Printing Width 85.
Show.
Unset Silent.
Show.
Unset Silent.
Show.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(assert (L : forall x : nat, List.In x li -> (x < \226\159\166 W \226\159\167)%nat)).
Set Silent.
{
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
Unset Silent.
Show.
Set Printing Width 85.
Show.
}
Timeout 1 About denote_ctrls_unitary.
Timeout 1 Print denote_ctrls_unitary.
Unset Silent.
Show.
Set Printing Width 85.
Show.
specialize (denote_ctrls_unitary W _ U _ L) as inv.
replace (size_wtype W1 + size_wtype W2)%nat with \226\159\166 W \226\159\167 by (subst; easy).
Set Silent.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(destruct W; inversion HeqW).
Unset Silent.
Show.
Set Printing Width 85.
Show.
Unset Silent.
Show.
Set Printing Width 85.
Show.
Unset Silent.
Show.
Set Printing Width 85.
Show.
Unset Silent.
Show.
Set Printing Width 85.
Show.
clear H0 H1 HeqW.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(rewrite denote_ctrls_transpose).
