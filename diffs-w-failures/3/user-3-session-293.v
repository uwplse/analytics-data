Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqi6gkwo"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
From Coq Require Import List.
From Transitions Require Import NonError.
Unset Silent.
Set Printing Width 51.
From RecoveryRefinement Require Export Lib.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq1GghPx"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2MzcJR"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
Module Var.
Inductive id :=
  | Sum : _
  | Count : _.
Inductive Op : Type -> Type :=
  | Read : forall i : id, Op nat
  | Write : forall (i : id) (v : nat), Op unit.
Definition State := (nat * nat)%type.
Definition get (i : id) : State -> nat :=
  match i with
  | Sum => fun '(x, _) => x
  | Count => fun '(_, y) => y
  end.
Definition set (i : id) (v : nat) :
  State -> State :=
  match i with
  | Sum => fun '(_, y) => (v, y)
  | Count => fun '(x, _) => (x, v)
  end.
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Read i => reads (get i)
          | Write i v => puts (set i v)
          end;
  crash_step := puts (fun _ => (0, 0)) |}.
Definition l : Layer Op :=
  {|
  Layer.State := State;
  sem := dynamics;
  initP := fun s => s = (0, 0) |}.
End Var.
Instance var_crash_step_nonerror :
 (NonError Var.dynamics.(crash_step)).
Proof.
(simpl).
Unset Silent.
Set Diffs "off".
Set Printing Width 51.
Show.
typeclasses eauto.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbheUZM"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
