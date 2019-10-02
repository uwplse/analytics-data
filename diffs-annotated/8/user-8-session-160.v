Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coquwDFyZ"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export Quantum.
Notation "\226\136\163 + \226\159\169" := (/ \226\136\154 2 .* \226\136\163 0 \226\159\169 .+ / \226\136\154 2 .* \226\136\163 1 \226\159\169).
Notation "\226\136\163 - \226\159\169" := (/ \226\136\154 2 .* \226\136\163 0 \226\159\169 .+ - / \226\136\154 2 .* \226\136\163 1 \226\159\169).
Lemma bra0_equiv : \226\159\1680\226\136\163 = bra 0.
Proof.
reflexivity.
Qed.
Lemma bra1_equiv : \226\159\1681\226\136\163 = bra 1.
Proof.
reflexivity.
Qed.
Lemma ket0_equiv : \226\136\1630\226\159\169 = ket 0.
Proof.
reflexivity.
Qed.
Lemma ket1_equiv : \226\136\1631\226\159\169 = ket 1.
Proof.
reflexivity.
Qed.
Lemma bra0ket0 : bra 0 \195\151 ket 0 = I 1.
Proof.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq1NRMuL"
Print Ltac Signatures.
