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
(simpl).
(destruct a; Msimpl; rewrite IHr; reflexivity).
-
(simpl).
(destruct a; Msimpl; rewrite IHl; reflexivity).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqoQ4Vef"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma denote_ctrls_transpose :
  forall W (n : nat) (u : Unitary W) li,
  denote_ctrls n (trans u) li = (denote_ctrls n u li) \226\128\160.
Proof.
(intros).
(unfold denote_ctrls).
(destruct (ctrls_to_list (repeat false n) li u) as [[j l] v] eqn:E).
(apply ctrls_to_list_transpose in E).
