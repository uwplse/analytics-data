Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqiolSfM"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Denotation.
Open Scope matrix_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition Unitary_Box {W} (b : Box W W) : Prop :=
  match b with
  | box c => forall p, Unitary_Circuit (c p)
  end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition Unitary_DB_Box {W} (b : DeBruijn_Box W W) : Prop :=
  match b with
  | db_box _ c => Unitary_DB_Circuit c
  end.
Fixpoint denote_u_db_circuit {W} (c : DeBruijn_Circuit W) : 
Square (2 ^ \226\159\166 W \226\159\167) :=
  match c with
  | db_output p => \226\159\166 p \226\159\167
  | db_gate g p c =>
      match g with
      | U u => denote_u_db_circuit c \195\151 apply_unitary (\226\159\166 W \226\159\167) u (pat_to_list p)
      | _ => dummy_mat
      end
  | _ => dummy_mat
  end.
Definition denote_u_db_box {W} (c : DeBruijn_Box W W) : 
  Square (2 ^ \226\159\166 W \226\159\167) := match c with
                        | db_box _ c' => denote_u_db_circuit c'
                        end.
Lemma unitary_to_db :
  forall W \206\147 (c : Circuit W),
  Unitary_Circuit c -> Unitary_DB_Circuit (hoas_to_db \206\147 c).
Proof.
(intros W \206\147 c U).
gen \206\147.
(induction c; intros).
-
(simpl).
constructor.
-
(simpl).
(destruct (process_gate g p \206\147) eqn:E).
dependent destruction U.
constructor.
(apply H).
(apply H0).
-
(inversion U).
Qed.
Lemma unitary_box_to_db :
  forall W (c : Box W W), Unitary_Box c -> Unitary_DB_Box (hoas_to_db_box c).
Proof.
(intros W c U).
(unfold Unitary_Box, Unitary_DB_Box in *).
(destruct c; simpl in *).
(destruct (add_fresh W [])).
(apply unitary_to_db).
(apply U).
Qed.
Definition denote_unitary_box {W} (c : Box W W) : Square (2 ^ \226\159\166 W \226\159\167) :=
  denote_u_db_box (hoas_to_db_box c).
Lemma denote_unitary_box_eq :
  forall W safe (c : Box W W) \207\129,
  Unitary_Box c ->
  denote_box safe c \207\129 == denote_unitary_box c \195\151 \207\129 \195\151 (denote_unitary_box c) \226\128\160.
Proof.
(intros W safe [c] \207\129 pf).
(simpl in pf).
(unfold denote_unitary_box, denote_box).
(unfold denote_db_box).
(unfold hoas_to_db_box).
(destruct (add_fresh W []) as [p \206\147]).
specialize (pf p).
gen \207\129.
(induction (c p)).
-
(intros \207\129).
(unfold denote_u_db_box).
(simpl).
(rewrite pad_nothing).
reflexivity.
-
(intros \207\129).
(simpl).
dependent destruction pf.
(simpl).
(unfold compose_super, super).
(rewrite Nat.add_sub).
(rewrite H0 by auto).
(unfold denote_u_db_box).
(simpl).
(unfold apply_U, super).
(rewrite Mmult_adjoint).
(repeat rewrite Mmult_assoc).
reflexivity.
-
(inversion pf).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqHeNv7f"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition HZH : Box Qubit Qubit := box_ q \226\135\146 _H $ _Z $ _H $ q.
Lemma U_HZH : Unitary_Box HZH.
Proof.
(repeat constructor).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqKz7ech"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma Unitary_Circuit_is_Isometry :
  forall W (c : Circuit W), Unitary_Circuit c -> Isometry_Circuit c.
Proof.
(intros).
(induction c as [p| W1 W2 g p c IH| ]).
-
constructor.
-
dependent destruction H.
constructor.
constructor.
(intros p').
(apply IH).
(apply H).
-
(inversion H).
Qed.
Definition Isometry_Box {W} {W'} (b : Box W W') : Prop :=
  match b with
  | box c => forall p, Isometry_Circuit (c p)
  end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition Isometry_DB_Box {W} {W'} (b : DeBruijn_Box W W') : Prop :=
  match b with
  | db_box _ c => Isometry_DB_Circuit c
  end.
Definition denote_init0 (n : nat) : Matrix (2 ^ (n + 1)) (2 ^ n) := I (2 ^ n) \226\138\151 \226\136\1630\226\159\169.
Definition denote_init1 (n : nat) : Matrix (2 ^ (n + 1)) (2 ^ n) := I (2 ^ n) \226\138\151 \226\136\1631\226\159\169.
Definition denote_assert0 (n k : nat) : Matrix (2 ^ (n - 1)) (2 ^ n) :=
  I (2 ^ k) \226\138\151 \226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1)).
Definition denote_assert1 (n k : nat) : Matrix (2 ^ (n - 1)) (2 ^ n) :=
  I (2 ^ k) \226\138\151 \226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1)).
Fixpoint denote_iso_db_circuit {W} (n : nat) (c : DeBruijn_Circuit W) :
Matrix (2 ^ \226\159\166 W \226\159\167) (2 ^ n) :=
  match c with
  | db_output p => pad n (\226\159\166 p \226\159\167)
  | db_gate g p c =>
      match g with
      | U u => denote_iso_db_circuit n c \195\151 apply_unitary n u (pat_to_list p)
      | init0 => denote_iso_db_circuit (S n) c \195\151 denote_init0 n
      | init1 => denote_iso_db_circuit (S n) c \195\151 denote_init1 n
      | assert0 =>
          denote_iso_db_circuit (n - 1)%nat c
          \195\151 denote_assert0 n (hd O (pat_to_list p))
      | assert1 =>
          denote_iso_db_circuit (n - 1)%nat c
          \195\151 denote_assert1 n (hd O (pat_to_list p))
      | _ => dummy_mat
      end
  | _ => dummy_mat
  end.
Definition denote_iso_db_box {W} {W'} (c : DeBruijn_Box W W') :
  Matrix (2 ^ \226\159\166 W' \226\159\167) (2 ^ \226\159\166 W \226\159\167) :=
  match c with
  | db_box _ c' => denote_iso_db_circuit (\226\159\166 W \226\159\167) c'
  end.
Lemma isometry_to_db :
  forall W \206\147 (c : Circuit W),
  Isometry_Circuit c -> Isometry_DB_Circuit (hoas_to_db \206\147 c).
Proof.
(intros W \206\147 c U).
gen \206\147.
(induction c; intros).
-
(simpl).
constructor.
-
(simpl).
(destruct (process_gate g p \206\147) eqn:E).
dependent destruction U.
(constructor; trivial).
(apply H).
(apply H1).
-
(inversion U).
Qed.
Lemma isometry_box_to_db :
  forall W W' (c : Box W W'), Isometry_Box c -> Isometry_DB_Box (hoas_to_db_box c).
Proof.
(intros W W' c U).
(unfold Isometry_Box, Isometry_DB_Box in *).
(destruct c; simpl in *).
(destruct (add_fresh W [])).
(apply isometry_to_db).
(apply U).
Qed.
Definition denote_isometry_box {W} {W'} (c : Box W W') :=
  denote_iso_db_box (hoas_to_db_box c).
Lemma denote_unitary_isometry_box_eq :
  forall W (c : Box W W),
  Unitary_Box c -> denote_unitary_box c = denote_isometry_box c.
Proof.
(intros W [f] pf).
(unfold Unitary_Box in pf).
(unfold denote_unitary_box, denote_isometry_box).
(unfold hoas_to_db_box).
(destruct (add_fresh W []) as [p \206\147]).
specialize (pf p).
(remember (f p) as c).
clear Heqc f p.
(induction c).
-
(unfold denote_iso_db_box, denote_u_db_box).
(simpl).
(rewrite pad_nothing).
(* Auto-generated comment: Succeeded. *)

