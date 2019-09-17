Require Import HOASLib.
Require Import Denotation.
Require Import TypeChecking.
Open Scope matrix_scope.
Lemma id_circ_spec : forall W \207\129 safe, denote_box safe (@id_circ W) \207\129 == \207\129.
Proof.
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
easy.
Qed.
Lemma X_spec :
  forall b safe : bool,
  denote_box safe (boxed_gate _X) (bool_to_matrix b) == bool_to_matrix (\194\172 b).
Proof.
(intros).
vector_denote.
(destruct b; unfold bool_to_ket; simpl; Msimpl; easy).
Qed.
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
Lemma assert0_spec : forall safe, denote_box safe assert0 \226\136\1630\226\159\169\226\159\1680\226\136\163 == I 1.
Proof.
(destruct safe; matrix_denote; Msimpl; lma).
Qed.
Lemma assert1_spec : forall safe, denote_box safe assert1 \226\136\1631\226\159\169\226\159\1681\226\136\163 == I 1.
Proof.
(destruct safe; matrix_denote; Msimpl; lma).
Qed.
Lemma init_spec :
  forall b safe, denote_box safe (init b) (I (2 ^ 0)) == bool_to_matrix b.
Proof.
(destruct b; [ apply init1_spec | apply init0_spec ]).
Qed.
Lemma assert_spec :
  forall b safe, denote_box safe (assert b) (bool_to_matrix b) == I 1.
Proof.
(destruct b; [ apply assert1_spec | apply assert0_spec ]).
Qed.
Lemma SWAP_spec : forall \207\129 safe, denote_box safe SWAP \207\129 == swap \195\151 \207\129 \195\151 swap.
Proof.
(intros).
matrix_denote.
Msimpl.
reflexivity.
Qed.
Lemma SWAP_spec_sep :
  forall (\207\1291 \207\1292 : Density 2) safe,
  WF_Matrix \207\1291 -> WF_Matrix \207\1292 -> denote_box safe SWAP (\207\1291 \226\138\151 \207\1292) == \207\1292 \226\138\151 \207\1291.
Proof.
(intros).
(rewrite SWAP_spec).
lma.
Qed.
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
(rewrite length_fresh_state with (w := W) (\206\147' := (add_fresh_state W []))
  (\206\147 := []) by easy).
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
  denote_box safe XOR
    (bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix z) ==
  bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix ((x \226\138\149 y) \226\138\149 z).
Proof.
vector_denote.
Msimpl.
(destruct x, y, z; simpl; lma).
Qed.
Lemma AND_spec :
  forall x y z safe : bool,
  denote_box safe AND
    (bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix z) ==
  bool_to_matrix x \226\138\151 bool_to_matrix y \226\138\151 bool_to_matrix ((x && y) \226\138\149 z).
Proof.
vector_denote.
Msimpl.
(destruct x, y, z; simpl; Msimpl; lma).
Qed.
