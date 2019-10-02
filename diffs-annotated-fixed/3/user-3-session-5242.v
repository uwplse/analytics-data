Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqDZKW25"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Require Import VariablesAPI.
Require Import StatDbAPI.
Module StatDB (v: VarsAPI)<: StatDbAPI.
Import ListNotations.
Definition add (v : nat) : proc unit :=
  sum <- v.read VarSum;
  count <- v.read VarCount;
  _ <- v.write VarSum (sum + v); _ <- v.write VarCount (count + 1); Ret tt.
Definition mean : proc (option nat) :=
  count <- v.read VarCount;
  (if count == 0
   then Ret None
   else sum <- v.read VarSum; Ret (Some (sum / count))).
Definition init' : proc InitResult :=
  _ <- v.write VarCount 0; _ <- v.write VarSum 0; Ret Initialized.
Definition init := then_init v.init init'.
Definition recover : proc unit := v.recover.
Definition statdb_abstraction (vars_state : VariablesAPI.State)
  (statdb_state : StatDbAPI.State) : Prop :=
  StateCount vars_state = length statdb_state /\
  StateSum vars_state = fold_right plus 0 statdb_state.
Definition abstr : Abstraction StatDbAPI.State :=
  abstraction_compose v.abstr {| abstraction := statdb_abstraction |}.
Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 0 0) nil.
Proof.
(unfold statdb_abstraction; auto).
Qed.
Example abstr_2_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) nil.
Proof.
(unfold statdb_abstraction; simpl).
lia.
Qed.
Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 2 3) [1; 2].
Proof.
(unfold statdb_abstraction; simpl).
lia.
Qed.
Theorem init_ok : init_abstraction init recover abstr inited.
Proof.
(eapply then_init_compose; eauto).
(unfold init').
(step_proc_basic; intros).
exists tt.
(simpl; intuition idtac).
(step_proc_basic; intros).
exists tt.
(simpl; intuition idtac).
(step_proc_basic; intros).
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0DzuHt"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
{
eauto.
}
(simpl in *; intuition subst).
exists nil.
(unfold statdb_abstraction, inited).
intuition auto.
Qed.
Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
Proof.
(unfold add).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
(destruct a'; simpl in *; intuition idtac).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
eauto.
(* Auto-generated comment: Failed. *)

