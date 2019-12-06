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
(rewrite kron_1_r').
(rewrite subst_pat_fresh_empty).
(rewrite denote_pat_fresh_id).
(rewrite super_I; easy).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqcAMjSv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
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
(destruct safe; matrix_denote; Msimpl; lma).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqc9vsnQ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma assert1_spec : forall safe, denote_box safe assert1 \226\136\1631\226\159\169\226\159\1681\226\136\163 == I 1.
Proof.
(destruct safe; matrix_denote; Msimpl; lma).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqMkmEId"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma init_spec :
  forall b safe, denote_box safe (init b) (I (2 ^ 0)) == bool_to_matrix b.
Proof.
(destruct b; [ apply init1_spec | apply init0_spec ]).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq4RZyDk"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma assert_spec :
  forall b safe, denote_box safe (assert b) (bool_to_matrix b) == I 1.
Proof.
(destruct b; [ apply assert1_spec | apply assert0_spec ]).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq8NsR6J"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma SWAP_spec : forall \207\129 safe, denote_box safe SWAP \207\129 == swap \195\151 \207\129 \195\151 swap.
Proof.
(intros).
matrix_denote.
Msimpl.
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqp0IENJ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma SWAP_spec_sep :
  forall (\207\1291 \207\1292 : Density 2) safe,
  WF_Matrix \207\1291 -> WF_Matrix \207\1292 -> denote_box safe SWAP (\207\1291 \226\138\151 \207\1292) == \207\1292 \226\138\151 \207\1291.
Proof.
(intros).
(rewrite SWAP_spec).
lma.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqW0sORO"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma fresh_wtype :
  forall (w : WType) (\206\147 : Ctx), add_fresh_state w \206\147 = \206\147 ++ add_fresh_state w [].
Proof.
(intros).
generalize dependent \206\147.
(induction w; unfold add_fresh_state; simpl; try reflexivity; intros).
-
(induction \206\147; simpl; try reflexivity).
(rewrite <- IH\206\147).
reflexivity.
-
(repeat rewrite add_fresh_split).
(simpl).
replace (add_fresh_state w2 (add_fresh_state w1 [])) with
 add_fresh_state w1 [] ++ add_fresh_state w2 [] by (rewrite <- IHw2; reflexivity).
(rewrite IHw2).
(rewrite IHw1).
(rewrite app_assoc).
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqRyItMx"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma SWAP_GEN_spec_same_sep :
  forall W (\207\1291 \207\1292 : Density (2 ^ \226\159\166 W \226\159\167)) safe,
  denote_box safe (@SWAP_GEN W W) (\207\1291 \226\138\151 \207\1292) == \207\1292 \226\138\151 \207\1291.
Proof.
matrix_denote.
(repeat rewrite add_fresh_split).
(unfold hoas_to_db).
(simpl).
Search -subst_pat.
(rewrite subst_pat_fresh).
(rewrite pad_nothing).
(unfold denote_pat).
(simpl).
(rewrite subst_pat_no_gaps).
2: {
(rewrite fresh_wtype).
(rewrite app_length).
Search -Bounded_Pat.
(apply bounded_pat_le with (length (add_fresh_state W []))).
lia.
(rewrite length_fresh_state with (w := W) (\206\147' := (add_fresh_state W [])) (
  \206\147 := []) by easy).
(apply add_fresh_pat_bounded).
constructor.
}
all: (repeat apply add_fresh_state_no_gaps; try constructor).
Search -pat_to_list -add_fresh_pat.
(repeat rewrite swap_fresh_seq).
(simpl).
Search -length -add_fresh_state.
(erewrite length_fresh_state by reflexivity).
(simpl).
Abort.
Lemma CNOT_spec :
  forall b1 b2 safe : bool,
  denote_box safe CNOT (bool_to_matrix b1 \226\138\151 bool_to_matrix b2) ==
  bool_to_matrix b1 \226\138\151 bool_to_matrix (b1 \226\138\149 b2).
Proof.
vector_denote.
(destruct b1, b2; unfold bool_to_ket; simpl; Msimpl; lma).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqdOHO0k"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma TRUE_spec :
  forall z safe,
  denote_box safe TRUE (bool_to_matrix z) == bool_to_matrix (true \226\138\149 z).
Proof.
vector_denote.
(destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity).
Qed.
Lemma FALSE_spec :
  forall z safe,
  denote_box safe FALSE (bool_to_matrix z) == bool_to_matrix (false \226\138\149 z).
Proof.
vector_denote.
(destruct z; unfold bool_to_ket; simpl; Msimpl; reflexivity).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqHPDlh3"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma NOT_spec :
  forall x z : bool,
  forall safe,
  denote_box safe NOT (bool_to_matrix x \226\138\151 bool_to_matrix z) ==
  bool_to_matrix x \226\138\151 bool_to_matrix (\194\172 x \226\138\149 z).
Proof.
vector_denote.
(destruct x, z; unfold bool_to_ket; simpl; Msimpl; lma).
Qed.
Lemma XOR_spec :
  forall x y z safe : bool,
  denote_box safe XOR (bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix z) ==
  bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix ((x \226\138\149 y) \226\138\149 z).
Proof.
vector_denote.
Msimpl.
(destruct x, y, z; simpl; lma).
Qed.
Lemma AND_spec :
  forall x y z safe : bool,
  denote_box safe AND (bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix z) ==
  bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix ((x && y) \226\138\149 z).
Proof.
vector_denote.
Msimpl.
(destruct x, y, z; simpl; Msimpl; lma).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq7zG7mX"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
(* Auto-generated comment: Succeeded. *)

