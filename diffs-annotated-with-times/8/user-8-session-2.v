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
(destruct li as [| k li]).
(repeat rewrite ctrls_to_list_empty).
(simpl; Msimpl).
reflexivity.
(dependent destruction u; simpl; Msimpl; reflexivity).
-
dependent destruction u.
+
(simpl).
(destruct li as [| k li]; simpl; try lma).
specialize (IHW2 lb li u).
(destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E).
(destruct (ctrls_to_list lb li (trans u)) as [[j' l'] v'] eqn:E').
(simpl in *).
(apply IHW2).
+
(simpl).
(destruct li as [| k li]; simpl; try lma).
specialize (IHW2 lb li u).
(destruct (ctrls_to_list lb li u) as [[j l] v] eqn:E).
(destruct (ctrls_to_list lb li (trans u)) as [[j' l'] v'] eqn:E').
(simpl in *).
(apply IHW2).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqVILhGU"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma ctrl_list_to_unitary_transpose :
  forall l r u, ctrl_list_to_unitary l r (u) \226\128\160 == (ctrl_list_to_unitary l r u) \226\128\160.
Proof.
(intros l r u).
(induction l).
(simpl).
-
(induction r; try reflexivity).
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
  denote_ctrls n (trans u) li == (denote_ctrls n u li) \226\128\160.
Proof.
(intros).
(unfold denote_ctrls).
Search -fst -snd.
(rewrite (surjective_pairing (ctrls_to_list (repeat false n) li (trans u)))).
(rewrite (surjective_pairing (ctrls_to_list (repeat false n) li u))).
(rewrite <- ctrls_to_list_transpose_fst).
(destruct (ctrls_to_list (repeat false n) li u) as [[j l] v] eqn:E).
Opaque skipn.
(simpl).
Timeout 1 About restore_dims.
Timeout 1 Print restore_dims.
Timeout 1 Print Ltac restore_dims.
(match goal with
 | |- ?A => let A' := restore_dims_rec idtac A in
            replace
            A
            with
            A'
 end).
(rewrite <- ctrl_list_to_unitary_transpose).
Timeout 1 About trans.
Timeout 1 Print trans.
Timeout 1 About ctrls_to_list.
Timeout 1 Print ctrls_to_list.
Timeout 1 Print Ltac ctrls_to_list.
(* Auto-generated comment: Succeeded. *)

