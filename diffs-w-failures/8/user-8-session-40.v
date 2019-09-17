Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqz5gwxg"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 85.
Set Silent.
Require Import HOASLib.
Require Import Denotation.
Require Import TypeChecking.
Open Scope matrix_scope.
Unset Silent.
Lemma id_circ_spec :
  forall W \207\129 safe, WF_Matrix \207\129 -> denote_box safe (@id_circ W) \207\129 == \207\129.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqjrEZQ5"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Silent.
Proof.
(intros W \207\129 safe H).
(simpl).
(unfold denote_box).
(simpl).
autorewrite with proof_db.
(rewrite add_fresh_split).
(simpl).
(unfold pad).
(simpl).
(rewrite Nat.sub_diag).
Unset Silent.
Show.
Set Printing Width 85.
Show.
(rewrite Nat.sub_diag).
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
(rewrite kron_1_r').
(rewrite subst_pat_fresh_empty).
(rewrite denote_pat_fresh_id).
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
(rewrite super_I; easy).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqcAMjSv"
Print Ltac Signatures.
Unset Silent.
Set Printing Width 85.
Unset Silent.
Unset Silent.
Set Printing Width 85.
Hint Rewrite @kron_1_r' : M_db.
Lemma X_spec :
  forall b safe : bool,
  denote_box safe (boxed_gate _X) (bool_to_matrix b) == bool_to_matrix (\194\172 b).
Set Silent.
Proof.
(intros).
vector_denote.
(destruct b; unfold bool_to_ket; simpl; Msimpl; easy).
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqYJshKs"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 85.
Set Silent.
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
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqeKDbME"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 85.
Set Silent.
Lemma assert0_spec : forall safe, denote_box safe assert0 \226\136\1630\226\159\169\226\159\1680\226\136\163 == I 1.
Proof.
Unset Silent.
(destruct safe; matrix_denote; Msimpl; lma).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqc9vsnQ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Lemma assert1_spec : forall safe, denote_box safe assert1 \226\136\1631\226\159\169\226\159\1681\226\136\163 == I 1.
Proof.
(destruct safe; matrix_denote; Msimpl; lma).
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqMkmEId"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Lemma init_spec :
  forall b safe, denote_box safe (init b) (I (2 ^ 0)) == bool_to_matrix b.
Proof.
(destruct b; [ apply init1_spec | apply init0_spec ]).
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq4RZyDk"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Lemma assert_spec :
  forall b safe, denote_box safe (assert b) (bool_to_matrix b) == I 1.
Proof.
(destruct b; [ apply assert1_spec | apply assert0_spec ]).
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq8NsR6J"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 85.
Set Silent.
Lemma SWAP_spec : forall \207\129 safe, denote_box safe SWAP \207\129 == swap \195\151 \207\129 \195\151 swap.
Proof.
(intros).
matrix_denote.
Unset Silent.
Show.
Set Printing Width 85.
Show.
Msimpl.
setoid_rewrite swap_sa.
