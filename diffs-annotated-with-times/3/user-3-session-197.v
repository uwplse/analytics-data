Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKyYjNJ"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import List.
From RecoveryRefinement Require Export Lib.
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
Definition set (i : id) (v : nat) : State -> State :=
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqEmd1Hh"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq217bs5"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Definition l : Layer Op :=
  {| Layer.State := State; sem := dynamics; initP := fun s => s = (0, 0) |}.
End Var.
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-07 14:02:45.050000.*)

