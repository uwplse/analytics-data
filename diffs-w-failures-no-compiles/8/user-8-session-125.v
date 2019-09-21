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
(rewrite denote_ctrls_transpose by (subst; try rewrite size_wtype_length; easy)).
(remember (denote_ctrls (\226\159\166 W3 \226\138\151 W4 \226\159\167) U li) as A).
(remember (swap_list (\226\159\166 W3 \226\138\151 W4 \226\159\167) li) as S).
(rewrite <- (Mmult_assoc _ (A \195\151 \207\129) _)).
(rewrite <- (Mmult_assoc _ A \207\129)).
(simpl in inv).
(rewrite inv by (subst; rewrite size_wtype_length; easy)).
Msimpl.
Set Silent.
Set Silent.
Set Silent.
(rewrite (Mmult_assoc \207\129 _ A)).
(rewrite inv by (subst; rewrite size_wtype_length; easy)).
Unset Silent.
Msimpl.
Set Silent.
(rewrite Mmult_assoc).
Unset Silent.
easy.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqSfBpFq"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Definition fair_coin : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => 1 / 2
             | 1, 1 => 1 / 2
             | _, _ => 0
             end.
Definition biased_coin (c : C) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => 1 - c
             | 1, 1 => c
             | _, _ => 0
             end.
Definition uniform (n : nat) : Matrix n n :=
  fun x y => if (x =? y) && (x <? n) then 1 / INR n else 0.
Unset Silent.
Set Printing Width 85.
Lemma bias1 : biased_coin 1 == \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
Unset Silent.
Show.
Set Printing Width 85.
Show.
Set Silent.
lma.
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqvIAyK0"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 85.
Lemma even_bias : biased_coin (1 / 2) == fair_coin.
Proof.
lma.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqSb2JHl"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 85.
Lemma fair_toss : (\226\159\166 coin_flip \226\159\167) (I 1) == fair_coin.
Proof.
matrix_denote.
Msimpl.
solve_matrix.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqi1digG"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Hint Unfold super_Zero: den_db.
Set Silent.
Proposition flips_lift_correct :
  forall n, (\226\159\166 coin_flips_lift n \226\159\167) (I 1) == biased_coin (1 / 2 ^ n).
Proof.
(induction n).
+
matrix_denote.
Msimpl.
solve_matrix.
+
(simpl).
Unset Silent.
Show.
Set Printing Width 85.
Show.
matrix_denote.
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
restore_dims.
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
(repeat rewrite Mmult_1_l).
restore_dims.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(rewrite (kron_1_l \226\136\1630\226\159\169)).
