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
(simpl).
(rewrite Nat.sub_diag).
(rewrite super_I; easy).
(destruct b; unfold bool_to_ket; simpl; Msimpl).
