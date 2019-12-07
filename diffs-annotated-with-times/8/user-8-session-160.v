Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coquwDFyZ"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export Quantum.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqGXs1Wa"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Notation "\226\136\163 + \226\159\169" := (/ \226\136\154 2 .* \226\136\163 0 \226\159\169 .+ / \226\136\154 2 .* \226\136\163 1 \226\159\169).
Notation "\226\136\163 - \226\159\169" := (/ \226\136\154 2 .* \226\136\163 0 \226\159\169 .+ - / \226\136\154 2 .* \226\136\163 1 \226\159\169).
Lemma bra0_equiv : \226\159\1680\226\136\163 == bra 0.
Proof.
reflexivity.
Qed.
Lemma bra1_equiv : \226\159\1681\226\136\163 == bra 1.
Proof.
reflexivity.
Qed.
Lemma ket0_equiv : \226\136\1630\226\159\169 == ket 0.
Proof.
reflexivity.
Qed.
Lemma ket1_equiv : \226\136\1631\226\159\169 == ket 1.
Proof.
reflexivity.
Qed.
Lemma bra0ket0 : bra 0 \195\151 ket 0 == I 1.
Proof.
lma.
Qed.
Lemma bra0ket1 : bra 0 \195\151 ket 1 == Zero.
Proof.
lma.
Qed.
Lemma bra1ket0 : bra 1 \195\151 ket 0 == Zero.
Proof.
lma.
Qed.
Lemma bra1ket1 : bra 1 \195\151 ket 1 == I 1.
Proof.
lma.
Qed.
Lemma H0_spec : hadamard \195\151 \226\136\163 0 \226\159\169 == \226\136\163 + \226\159\169.
Proof.
lma.
Qed.
Lemma H1_spec : hadamard \195\151 \226\136\163 1 \226\159\169 == \226\136\163 - \226\159\169.
Proof.
lma.
Qed.
Lemma Hplus_spec : hadamard \195\151 \226\136\163 + \226\159\169 == \226\136\163 0 \226\159\169.
Proof.
solve_matrix.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqzgMAmi"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma Hminus_spec : hadamard \195\151 \226\136\163 - \226\159\169 == \226\136\163 1 \226\159\169.
Proof.
solve_matrix.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqr6af0U"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma X0_spec : \207\131x \195\151 \226\136\163 0 \226\159\169 == \226\136\163 1 \226\159\169.
Proof.
lma.
Qed.
Lemma X1_spec : \207\131x \195\151 \226\136\163 1 \226\159\169 == \226\136\163 0 \226\159\169.
Proof.
lma.
Qed.
Lemma Y0_spec : \207\131y \195\151 \226\136\163 0 \226\159\169 == Ci .* \226\136\163 1 \226\159\169.
Proof.
lma.
Qed.
Lemma Y1_spec : \207\131y \195\151 \226\136\163 1 \226\159\169 == - Ci .* \226\136\163 0 \226\159\169.
Proof.
lma.
Qed.
Lemma Z0_spec : \207\131z \195\151 \226\136\163 0 \226\159\169 == \226\136\163 0 \226\159\169.
Proof.
lma.
Qed.
Lemma Z1_spec : \207\131z \195\151 \226\136\163 1 \226\159\169 == - 1 .* \226\136\163 1 \226\159\169.
Proof.
lma.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqO8xaVB"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma CNOT_spec :
  forall x y : nat,
  (x < 2)%nat -> (y < 2)%nat -> cnot \195\151 \226\136\163 x, y \226\159\169 == \226\136\163 x, (x + y) mod 2 \226\159\169.
Proof.
(intros; destruct x as [| [| x]], y as [| [| y]]; try lia; lma).
Qed.
Lemma CNOT00_spec : cnot \195\151 \226\136\163 0, 0 \226\159\169 == \226\136\163 0, 0 \226\159\169.
Proof.
lma.
Qed.
Lemma CNOT01_spec : cnot \195\151 \226\136\163 0, 1 \226\159\169 == \226\136\163 0, 1 \226\159\169.
Proof.
crunch_matrix.
Qed.
Lemma CNOT10_spec : cnot \195\151 \226\136\163 1, 0 \226\159\169 == \226\136\163 1, 1 \226\159\169.
Proof.
lma.
Qed.
Lemma CNOT11_spec : cnot \195\151 \226\136\163 1, 1 \226\159\169 == \226\136\163 1, 0 \226\159\169.
Proof.
lma.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqrNTc4T"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma SWAP_spec : forall x y, swap \195\151 \226\136\163 x, y \226\159\169 == \226\136\163 y, x \226\159\169.
Proof.
(intros).
(destruct x, y; lma).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqRp6m05"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
(* Auto-generated comment: Succeeded. *)

