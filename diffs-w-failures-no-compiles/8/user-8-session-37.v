Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqP3zR22"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 85.
Set Silent.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Denotation.
Require Import Composition.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Unset Silent.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqLxBZpd"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqJ4AsTz"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 85.
Unset Silent.
Set Printing Width 85.
Set Silent.
Unset Silent.
Set Printing Width 85.
Definition valid_ancillae_box {W1} {W2} (c : Box W1 W2) :=
  forall \207\129, Typed_Box c -> denote_box true c \207\129 == denote_box false c \207\129.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqjMNFPS"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition valid_ancillae' {W} (c : Circuit W) :=
  forall (\206\147 \206\1470 : Ctx) \207\129,
  \206\147 \226\138\162 c :Circ -> Mixed_State \207\129 -> trace ((\226\159\168! \206\1470 | \206\147 \226\138\169 c !\226\159\169) \207\129) = 1.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqRFmcai"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Definition valid_ancillae_box' {W1} {W2} (c : Box W1 W2) : Prop :=
  forall \207\129, Typed_Box c -> Mixed_State \207\129 -> trace (denote_box false c \207\129) = 1.
Proposition valid_ancillae_equal :
  forall W (c : Circuit W), valid_ancillae c <-> valid_ancillae' c.
Proof.
(intros).
(unfold valid_ancillae, valid_ancillae').
split.
-
(intros H \206\147 \206\1470 \207\129 H0 H1).
(rewrite <- H; trivial).
(apply mixed_state_trace_1).
admit.
-
(induction c as [| W' W0 g p c IH| IH]).
+
reflexivity.
+
Unset Silent.
(intros H \206\147 \206\1470 \207\129 H').
replace (gate g p c) with compose (gate g p (fun p' => output p')) c by auto.
dependent destruction H'.
(destruct \206\1471 as [| \206\1471]; try invalid_contradiction).
(erewrite denote_compose with (\206\1471 := []); trivial).
Focus 3.
(intros \206\1473 \206\1470' p0 H0 H1).
(destruct H0).
(rewrite merge_nil_r in pf_merge).
subst.
(apply (t0 \206\1473); trivial).
Abort.
Fact valid_ancillae_box_equal :
  forall W1 W2 (c : Box W1 W2), valid_ancillae_box c <-> valid_ancillae_box' c.
Proof.
(intros).
(destruct c).
Admitted.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqSdZ1Lg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fact valid_ancillae_unbox :
  forall W W' (c : Pat W -> Circuit W'),
  (forall p, valid_ancillae (c p)) <-> valid_ancillae_box (box (fun p => c p)).
Proof.
(intros).
(unfold valid_ancillae, valid_ancillae_box).
(unfold denote_box).
(unfold denote_circuit).
(unfold denote_db_box).
(unfold hoas_to_db_box).
split.
-
Unset Silent.
Show.
Set Printing Width 85.
Show.
(intros H \207\129 T).
Set Silent.
specialize (H (add_fresh_pat W []) (add_fresh_state W []) []).
(simpl in *).
(rewrite size_fresh_ctx in H).
(simpl in H).
(unfold add_fresh_state, add_fresh_pat in *).
(destruct (add_fresh W []) as [p \206\147] eqn:E).
(simpl in *).
(rewrite H).
Unset Silent.
easy.
(unfold Typed_Box in T).
(simpl in T).
(apply T).
admit.
-
(intros H p \206\147 \206\1470 T).
(simpl in *).
Admitted.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq9u3YT1"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Proposition valid_ancillae_unbox' :
  forall W W' (c : Box W W') (p : Pat W),
  valid_ancillae (unbox c p) <-> valid_ancillae_box c.
Proof.
(intros W W' c p).
(unfold valid_ancillae, valid_ancillae_box).
(unfold denote_box).
(unfold denote_db_box).
(destruct c).
(simpl).
(unfold denote_circuit).
(simpl).
split.
-
(intros H).
admit.
Abort.
Lemma id_correct : forall W p, valid_ancillae (@output W p).
Proof.
(intros W p).
(unfold valid_ancillae).
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqyFPGK4"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma update_merge :
  forall (\206\147 \206\147' : Ctx) W W' v,
  \206\147' \226\169\181 singleton v W \226\136\153 \206\147 -> Valid (update_at \206\147' v (Some W')) \226\169\181 singleton v W' \226\136\153 \206\147.
Set Silent.
Proof.
(intros \206\147 \206\147' W W' v H).
generalize dependent \206\147.
generalize dependent \206\147'.
(induction v).
-
(intros \206\147' \206\147 H).
(simpl in *).
(apply merge_fun_ind in H).
(inversion H; subst).
(simpl).
constructor.
(apply valid_valid).
reflexivity.
(inversion H5; subst).
(inversion H4; subst).
constructor.
(apply valid_valid).
reflexivity.
(inversion H4; subst).
constructor.
(apply valid_valid).
reflexivity.
-
(intros \206\147' \206\147 H).
(simpl).
(destruct \206\147).
+
(destruct H).
(rewrite merge_nil_r in pf_merge).
(inversion pf_merge).
(simpl).
(edestruct IHv).
constructor.
2: (rewrite merge_nil_r; easy).
(apply valid_valid).
(rewrite merge_nil_r in pf_merge0).
(inversion pf_merge0).
constructor.
(apply valid_valid).
(rewrite merge_nil_r).
easy.
+
(destruct H).
constructor.
(apply valid_valid).
unlock_merge.
(simpl in *).
(destruct (merge' (singleton v W) \206\147) eqn:E).
(rewrite pf_merge in pf_valid).
invalid_contradiction.
(simpl).
(edestruct IHv).
constructor.
2: (symmetry in E; unlock_merge; apply E).
(apply valid_valid).
unlock_merge.
(rewrite <- pf_merge0).
(inversion pf_merge).
(simpl).
easy.
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqxL0sFY"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Lemma change_type_singleton :
  forall v W W', change_type v W' (singleton v W) = singleton v W'.
Proof.
(intros v W W').
(unfold change_type).
(erewrite update_at_singleton).
reflexivity.
(apply singleton_singleton).
(apply singleton_singleton).
Unset Silent.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq6fTVwn"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Lemma ancilla_free_valid :
  forall W (c : Circuit W), ancilla_free c -> valid_ancillae c.
Proof.
(intros W c AF).
(induction c).
+
(unfold valid_ancillae).
reflexivity.
+
(assert (VA : forall p : Pat w2, valid_ancillae (c p))).
(intros p').
(apply H).
dependent destruction AF.
(apply H1).
clear H.
(unfold valid_ancillae in *).
Unset Silent.
Show.
Set Printing Width 85.
Show.
(intros \206\1470 \206\1471 \207\129 WT).
dependent destruction WT.
Set Silent.
(destruct \206\147 as [| \206\147], \206\1472 as [| \206\1472]; try invalid_contradiction).
(erewrite 2!denote_gate_circuit; try apply pf1; try apply t).
Unset Silent.
(destruct g).
-
Unset Silent.
Show.
Set Printing Width 85.
Show.
(simpl).
(unfold compose_super).
Unset Silent.
Show.
Set Printing Width 85.
Show.
(erewrite VA).
Unset Silent.
Show.
Set Printing Width 85.
Show.
easy.
(eapply t0; [ apply pf1 | apply t ]).
Set Silent.
-
(simpl).
(unfold compose_super).
(erewrite VA).
easy.
Unset Silent.
(eapply t0; [ apply pf1 | apply t ]).
-
(simpl).
(unfold compose_super).
(erewrite VA).
easy.
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
(eapply t0; [  | constructor; apply singleton_singleton ]).
dependent destruction p.
dependent destruction t.
(destruct pf1).
(rewrite merge_nil_l in pf_merge).
(inversion pf_merge).
subst.
(unfold process_gate_state).
(simpl).
split.
validate.
(rewrite merge_comm, merge_singleton_append).
easy.
-
(simpl).
(unfold compose_super).
(erewrite VA).
reflexivity.
(eapply t0).
2: (constructor; apply singleton_singleton).
dependent destruction p.
dependent destruction t.
(destruct pf1).
(rewrite merge_nil_l in pf_merge).
Set Silent.
(inversion pf_merge).
subst.
(unfold process_gate_state).
(simpl).
split.
validate.
(rewrite merge_comm, merge_singleton_append).
Unset Silent.
easy.
Set Silent.
-
(simpl).
(unfold compose_super).
(erewrite VA).
easy.
Unset Silent.
(eapply t0; [  | constructor; apply singleton_singleton ]).
dependent destruction p.
Set Silent.
dependent destruction t.
(destruct pf1).
(rewrite merge_nil_l in pf_merge).
(inversion pf_merge).
subst.
(unfold process_gate_state).
(simpl).
split.
validate.
(rewrite merge_comm, merge_singleton_append).
easy.
-
(simpl).
(unfold compose_super).
(erewrite VA).
easy.
Unset Silent.
(eapply t0; [  | constructor; apply singleton_singleton ]).
Set Silent.
dependent destruction p.
dependent destruction t.
(destruct pf1).
(rewrite merge_nil_l in pf_merge).
(inversion pf_merge).
subst.
(unfold process_gate_state).
(simpl).
split.
validate.
(rewrite merge_comm, merge_singleton_append).
Unset Silent.
easy.
Unset Silent.
Show.
Set Printing Width 85.
Show.
Set Silent.
-
Unset Silent.
Show.
Set Printing Width 85.
Show.
Set Silent.
dependent destruction p.
dependent destruction t.
(simpl).
(unfold compose_super).
(erewrite VA).
easy.
Unset Silent.
(eapply t0; [  | constructor; apply singleton_singleton ]).
(apply singleton_equiv in s; subst).
Set Silent.
(unfold process_gate_state).
(simpl).
split.
validate.
(unfold change_type).
(eapply update_merge).
(apply pf1).
Unset Silent.
-
Unset Silent.
Show.
Set Printing Width 85.
Show.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(erewrite VA).
easy.
(eapply t0; [ apply pf1 | apply t ]).
-
dependent destruction p.
dependent destruction t.
(simpl).
Set Silent.
(unfold compose_super).
(erewrite VA).
reflexivity.
(unfold process_gate_state).
(simpl).
(unfold process_gate_pat).
Unset Silent.
(simpl).
Set Silent.
(apply singleton_equiv in s).
subst.
(erewrite remove_bit_merge').
Unset Silent.
(apply trim_types_circ).
(eapply t0; [  | constructor ]).
split.
validate.
(rewrite merge_nil_l).
easy.
easy.
-
dependent destruction AF.
(inversion H).
-
dependent destruction AF.
(inversion H).
+
Unset Silent.
Show.
Set Printing Width 85.
Show.
dependent destruction AF.
(assert (VA : forall b, valid_ancillae (c b))).
(intros; apply H; apply H0).
clear H.
(unfold valid_ancillae in *).
Unset Silent.
Show.
Set Printing Width 85.
Show.
(intros \206\147 \206\1470 \207\129 WT).
(unfold denote_circuit in *).
(simpl in *).
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
Unset Silent.
Show.
Set Printing Width 85.
Show.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(unfold compose_super, Splus).
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
(erewrite 2!VA).
reflexivity.
Set Silent.
*
dependent destruction WT.
dependent destruction p.
dependent destruction t.
(apply singleton_equiv in s).
subst.
(destruct \206\1472 as [| \206\1472]; try invalid_contradiction).
(erewrite remove_bit_merge').
(apply trim_types_circ).
(apply t0).
easy.
*
dependent destruction WT.
dependent destruction p.
dependent destruction t.
(apply singleton_equiv in s).
subst.
(destruct \206\1472 as [| \206\1472]; try invalid_contradiction).
(erewrite remove_bit_merge').
(apply trim_types_circ).
(apply t0).
easy.
*
dependent destruction WT.
dependent destruction p.
dependent destruction t.
(apply singleton_equiv in s).
subst.
(destruct \206\1472 as [| \206\1472]; try invalid_contradiction).
(rewrite (remove_bit_pred \206\1472 \206\147)).
easy.
Unset Silent.
easy.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqSngkDQ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Lemma ancilla_free_box_valid :
  forall W W' (c : Box W W'), ancilla_free_box c -> valid_ancillae_box c.
Proof.
(intros).
(destruct H).
(apply valid_ancillae_unbox).
(intros p).
(apply ancilla_free_valid).
(apply H).
Qed.
Unset Silent.
Unset Silent.
Set Printing Width 85.
Lemma valid_denote_true :
  forall W W' (c : Box W W') (\207\129 : Square (2 ^ \226\159\166 W \226\159\167)) (\207\129' : Square (2 ^ \226\159\166 W \226\159\167))
    (safe : bool),
  Typed_Box c ->
  valid_ancillae_box c -> denote_box true c \207\129 == \207\129' -> denote_box safe c \207\129 == \207\129'.
Set Silent.
Proof.
Unset Silent.
Show.
Set Printing Width 85.
Show.
(destruct safe; trivial).
Timeout 1 Check @valid_ancillae.
Timeout 1 Check @valid_ancillae.
Timeout 1 Check @valid_ancillae.
Timeout 1 Check @valid_ancillae'.
Timeout 1 Check @valid_ancillae_box.
(unfold valid_ancillae_box in H).
(rewrite <- H; assumption).
