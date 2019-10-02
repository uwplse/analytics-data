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
Lemma ctrls_to_list_transpose_fst :
  forall W lb li (u : Unitary W),
  fst (ctrls_to_list lb li u) = fst (ctrls_to_list lb li (trans u)).
Proof.
(induction W; intros lb li u; try (solve [ inversion u ])).
-
(destruct li as [| k li]).
(repeat rewrite ctrls_to_list_empty).
reflexivity.
(dependent destruction u; simpl; reflexivity).
-
dependent destruction u.
+
(simpl).
(destruct li as [| k li]; trivial).
specialize (IHW2 lb li u).
(destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E).
(destruct (ctrls_to_list lb li (trans u)) as [[j' l'] v'] eqn:E').
(inversion IHW2; subst).
reflexivity.
+
(simpl).
(destruct li as [| k li]; trivial).
specialize (IHW2 lb li u).
(destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E).
(destruct (ctrls_to_list lb li (trans u)) as [[j' l'] v'] eqn:E').
(inversion IHW2; subst).
reflexivity.
Qed.
Lemma ctrls_to_list_transpose_snd :
  forall W lb li (u : Unitary W),
  (snd (ctrls_to_list lb li u)) \226\128\160 == snd (ctrls_to_list lb li (trans u)).
Proof.
(induction W; intros lb li u; try (solve [ inversion u ])).
-
