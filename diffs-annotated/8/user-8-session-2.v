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
Axiom
  (operator_sum_decomposition : forall {m} {n} (l : list (Matrix m n)), outer_sum l == I n <-> WF_Superoperator (operator_sum l)).
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqZu7SSe" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma discard_superoperator :
  forall (n i j : nat) (\207\129 : Square (2 ^ n)),
  (i * j * 2 = 2 ^ n)%nat ->
  Mixed_State \207\129 -> Mixed_State (I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1630\226\159\169 \226\138\151 I j) .+ I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1631\226\159\169 \226\138\151 I j)).
Proof.
(intros n i j \207\129 E M).
(destruct (operator_sum_decomposition [I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j]) as [WFS _]).
(assert (OS : outer_sum [I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j] == I (i * 2 * j))).
{
(unfold outer_sum).
(simpl).
Msimpl.
(rewrite <- kron_plus_dist_r, <- kron_plus_dist_l).
mat_replace \226\136\1630\226\159\169\226\159\1680\226\136\163 .+ \226\136\1631\226\159\169\226\159\1681\226\136\163 with I 2 by lma.
(repeat rewrite id_kron).
easy.
}
specialize (WFS OS \207\129).
(unfold operator_sum, Splus, SZero, super, WF_Superoperator in WFS).
(simpl in WFS).
