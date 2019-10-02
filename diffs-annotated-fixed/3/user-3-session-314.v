Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqiK6yJO"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Examples.StatDb.Impl.
From Transitions Require Import NonError.
Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.
Definition absr :
  relation DB.l.(State) Var.l.(State) unit :=
  fun l res =>
  match res with
  | Val s _ =>
      fst s = fold_right plus 0 l /\
      snd s = length l
  | Err _ _ => False
  end.
Instance absr_non_error : (NonError absr).
Proof.
(compute; auto).
Qed.
Definition init_hspec :
  Specification InitStatus unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' _ => state' = (0, 0);
  alternate := fun state' (_ : unit) => True |}.
Definition add_hspec n :
  Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\
          snd state' = S (snd state);
  alternate := fun state' (_ : unit) =>
               state' = (0, 0) |}.
Definition add_rspec n :
  Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\
          snd state' = S (snd state);
  alternate := fun state' (_ : unit) =>
               state' = (0, 0) |}.
Definition avg_hspec :
  Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v =>
          state = state' /\
          v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition avg_rspec :
  Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v =>
          state = state' /\
          v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition recover_spec :
  Specification unit unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' (_ : unit) => state' = (0, 0);
  alternate := fun state' (_ : unit) =>
               state' = (0, 0) |}.
Lemma read_op_ok :
  forall i,
  proc_hspec Var.dynamics (read i)
    (op_spec Var.dynamics (Var.Read i)).
Proof.
(intros).
(eapply op_spec_sound).
typeclasses eauto.
typeclasses eauto.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqkIbtLI"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtLGi9O"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgqHz0E"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Lemma write_op_ok :
  forall i v,
  proc_hspec Var.dynamics (write i v)
    (op_spec Var.dynamics (Var.Write i v)).
Proof.
(intros).
(eapply op_spec_sound).
Qed.
(* Auto-generated comment: Succeeded. *)

