Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqi6gkwo"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import List.
From Transitions Require Import NonError.
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
 (NonError Var.dynamics.(crash_step)) := _.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqswQCfn"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqHvv4Ps"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Module DB.
Inductive Op : Type -> Type :=
  | Add : forall n : nat, Op unit
  | Avg : Op nat.
Definition State := list nat.
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Add n => puts (cons n)
          | Avg =>
              reads
                (fun l =>
                 fold_right plus 0 l / length l)
          end;
  crash_step := puts (fun _ => nil) |}.
Definition l : Layer Op :=
  {|
  Layer.State := State;
  sem := dynamics;
  initP := fun s => s = nil |}.
End DB.
Instance db_crash_step_nonerror :
 (NonError DB.dynamics.(crash_step)) := _.
Definition read i := Call (Var.Read i).
Definition write i v := Call (Var.Write i v).
Definition impl : LayerImpl Var.Op DB.Op :=
  {|
  compile_op := fun T (op : DB.Op T) =>
                match op with
                | DB.Add n =>
                    (sum <- read Var.Sum;
                     _ <-
                     write Var.Sum (n + sum)%nat;
                     count <- read Var.Count;
                     _ <-
                     write Var.Count
                       (1 + count)%nat; 
                     Ret tt)%proc
                | DB.Avg =>
                    (sum <- read Var.Sum;
                     count <- read Var.Count;
                     Ret (sum / count)%nat)%proc
                end;
  recover := Ret tt;
  init := Ret Initialized |}.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqzs4AF1"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQkeBjJ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
(* Auto-generated comment: Succeeded. *)

