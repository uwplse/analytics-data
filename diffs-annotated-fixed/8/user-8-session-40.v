Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqz5gwxg"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import HOASLib.
Require Import Denotation.
Require Import TypeChecking.
Open Scope matrix_scope.
Lemma id_circ_spec :
  forall W \207\129 safe, WF_Matrix \207\129 -> denote_box safe (@id_circ W) \207\129 == \207\129.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqjrEZQ5"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Proof.
(intros W \207\129 safe H).
(simpl).
(unfold denote_box).
(simpl).
autorewrite with proof_db.
(rewrite add_fresh_split).
(simpl).
(unfold pad).
(rewrite Nat.sub_diag).
(rewrite kron_1_r').
(rewrite subst_pat_fresh_empty).
(rewrite denote_pat_fresh_id).
(rewrite super_I; easy).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqcAMjSv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma X_spec :
  forall b safe : bool,
  denote_box safe (boxed_gate _X) (bool_to_matrix b) == bool_to_matrix (\194\172 b).
Hint Rewrite @kron_1_r' : M_db.
Hint Rewrite @kron_1_r' : M_db.
Lemma X_spec :
  forall b safe : bool,
  denote_box safe (boxed_gate _X) (bool_to_matrix b) == bool_to_matrix (\194\172 b).
Proof.
(intros).
vector_denote.
(destruct b; unfold bool_to_ket; simpl; Msimpl; easy).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqYJshKs"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma init0_spec : forall safe, denote_box safe init0 (I (2 ^ 0)) == \226\136\1630\226\159\169\226\159\1680\226\136\163.
Proof.
(intros).
matrix_denote.
Msimpl.
reflexivity.
Qed.
Lemma init1_spec : forall safe, denote_box safe init1 (I (2 ^ 0)) == \226\136\1631\226\159\169\226\159\1681\226\136\163.
Proof.
(intros).
matrix_denote.
Msimpl.
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqeKDbME"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma assert0_spec : forall safe, denote_box safe assert0 \226\136\1630\226\159\169\226\159\1680\226\136\163 == I 1.
Proof.
(destruct safe).
-
matrix_denote.
Msimpl.
(* Auto-generated comment: Succeeded. *)

