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
{
eauto.
}
(simpl in *; intuition subst).
{
(exists (v :: s); intuition auto).
(unfold statdb_abstraction in *; simpl in *).
intuition lia.
}
(autounfold in *; intuition).
Qed.
Theorem mean_ok : proc_spec mean_spec mean recover abstr.
Proof.
(unfold mean).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
(destruct a'; simpl in *; intuition idtac).
(exists tt; simpl; intuition idtac).
(destruct (r == 0)).
-
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
2: (autounfold in *; intuition).
(unfold statdb_abstraction in *).
(destruct s; intuition; simpl in *; try congruence).
(exists nil; intuition auto).
-
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
2: (autounfold in *; intuition).
(unfold statdb_abstraction in *).
(destruct s; intuition).
(exists (n0 :: s); intuition auto).
(right; intuition congruence).
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_crash.
Proof.
(unfold rec_wipe).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
{
eauto.
}
(destruct a; simpl in *).
intuition eauto.
Qed.
End StatDB.
Require Import VariablesImpl.
Module StatDBImpl:=  StatDB Vars.
Print Assumptions StatDBImpl.abstr_2_nok.
Print Assumptions StatDBImpl.abstr_3_ok.
Print Assumptions StatDBImpl.add_ok.
Print Assumptions StatDBImpl.mean_ok.
