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
Hint Rewrite @kron_1_r'.
Lemma X_spec :
  forall b safe : bool,
  denote_box safe (boxed_gate _X) (bool_to_matrix b) == bool_to_matrix (\194\172 b).
Proof.
(intros).
vector_denote.
Unset Silent.
Show.
Set Printing Width 85.
Show.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(destruct b; unfold bool_to_ket; simpl; Msimpl).
Unset Silent.
Show.
