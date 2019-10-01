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
(unfold denote_u_db_box).
(simpl).
(rewrite pad_nothing).
