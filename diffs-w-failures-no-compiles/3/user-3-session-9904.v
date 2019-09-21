Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqe9riH3"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
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
Unset Silent.
Definition abstr : Abstraction StatDbAPI.State :=
  abstraction_compose v.abstr {| abstraction := statdb_abstraction |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coquLjIgs"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqa1Kl19"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Theorem init_ok : init_abstraction init recover abstr inited.
Proof.
(eapply then_init_compose; eauto).
(unfold init').
step_proc.
step_proc.
step_proc.
exists nil.
(unfold statdb_abstraction, inited).
Unset Silent.
intuition.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqeWdxbn"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
Unset Silent.
Proof.
(unfold add).
(intros).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(apply spec_abstraction_compose; simpl).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
step_proc.
(destruct a'; simpl in *; intuition).
Timeout 1 Check @Ascii.nat_ascii_embedding.
(step_proc; intuition).
(step_proc; intuition).
(step_proc; intuition).
(step_proc; intuition).
{
(exists (v :: s); intuition auto).
(unfold statdb_abstraction in *; simpl in *).
intuition lia.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqNjwiwf"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
}
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqDsSWTC"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
Theorem mean_ok : proc_spec mean_spec mean recover abstr.
Proof.
(unfold mean).
(intros).
(apply spec_abstraction_compose; simpl).
Unset Silent.
step_proc.
(destruct a'; simpl in *; intuition idtac).
(destruct (r == 0)).
-
Timeout 1 Check @Ascii.nat_ascii_embedding.
(step_proc; intuition).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
2: (autounfold in *; intuition).
