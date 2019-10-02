Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqgc2zwA"
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
Lemma id_circ_spec : forall W \207\129 safe, denote_box safe (@id_circ W) \207\129 == \207\129.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqVoxw9J"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
(intros W \207\129 safe).
(simpl).
(unfold denote_box).
(simpl).
autorewrite with proof_db.
(rewrite add_fresh_split).
(simpl).
(unfold pad).
(simpl).
(rewrite Nat.sub_diag).
(rewrite kron_1_r').
(rewrite subst_pat_fresh_empty).
(rewrite denote_pat_fresh_id).
(rewrite super_I).
(* Auto-generated comment: Succeeded. *)

