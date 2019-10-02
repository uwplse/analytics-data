Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqgmJjIR"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqo9sLpI"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Program.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq701yPz"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Import Arith.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqHx786X"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Import Omega.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqSSx1yH"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Import Monad.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqoq3PJ3"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqZL5ChX"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Export Quantum.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqPmkW1h"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqToWrV3"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
(simpl; Msimpl).
(dependent destruction u; simpl; Msimpl; reflexivity).
Timeout 1 About restore_dims.
Timeout 1 About trans.
Timeout 1 About ctrls_to_list.
(simpl_rewrite @denote_unitary_transpose).
Lemma apply_unitary_unitary :
  forall W n (u : Unitary W) l, length l = \226\159\166 W \226\159\167 -> (forall x, In x l -> x < n)%nat -> WF_Unitary (apply_unitary n u l).
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
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqU73lTe" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
