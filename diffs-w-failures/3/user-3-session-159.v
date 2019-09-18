Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0oM8Ug"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
Require Import Examples.StatDb.Impl.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @True.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Transitive.
Timeout 1 Check @Ret.
Timeout 1 Check @SReqe_Reqe.
Timeout 1 Check @readNone.
Set Printing Width 78.
From Transitions Require Import NonError.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq4Wt8Ur"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgwakKd"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Instance absr_non_error : (NonError absr).
Unset Silent.
Proof.
Timeout 1 Check @compile_exec_ok.
Timeout 1 Check @compile_exec_ok.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @unit.
Timeout 1 Check @rexec_unfold.
Timeout 1 Check @rexec_unfold.
Timeout 1 Check @rexec_unfold.
Timeout 1 Check @readNone.
Timeout 1 Check @NonError.
Timeout 1 Check @NonError.
Timeout 1 Check @NonError.
Timeout 1 Check @NonError.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(compute; auto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq7QyU3R"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZVTrXv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqteqYWo"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
Definition init_hspec : Specification InitStatus unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' _ => state' = (0, 0);
  alternate := fun state' (_ : unit) => True |}.
Definition add_hspec n : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\ snd state' = S (snd state);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Definition add_rspec n : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\ snd state' = S (snd state);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Definition avg_hspec : Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => state = state' /\ v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition avg_rspec : Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => state = state' /\ v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition recover_spec : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' (_ : unit) => state' = (0, 0);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Lemma read_op_ok :
  forall i,
  proc_hspec Var.dynamics (read i) (op_spec Var.dynamics (Var.Read i)).
Proof.
(intros).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(eapply op_spec_sound).
