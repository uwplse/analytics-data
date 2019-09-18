Time From RecordUpdate Require Import RecordUpdate.
Time From Transitions Require Import Relations.
Time From Perennial Require Import Spec.Proc.
Time From Perennial Require Import Spec.InjectOp.
Time From Perennial.Goose Require Import Machine.
Time Set Implicit Arguments.
Time Module Globals.
Time Section GoModel.
Time Context `{model_wf : GoModelWf}.
Time Context {G : Type}.
Time
Inductive Op : Type -> Type :=
  | SetX : forall x : G, Op unit
  | GetX : Op G.
Time Definition State := option G.
Time Definition init : State := None.
Time Import RelationNotations.
Time
Definition step T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | SetX x => s <- reads id;
      match s with
      | Some _ => error
      | None => puts (fun _ => Some x)
      end
  | GetX => readSome id
  end.
Time Section OpWrappers.
Time Context {Op'} {i : Injectable Op Op'}.
Time Notation proc := (proc Op').
Time Notation "'Call' op" := (Call (inject op) : proc _) (at level 0).
Time
Notation "'Call!' op" := (Call (op) : proc _) (at level 0, op  at level 200).
Time Definition setX x := Call! SetX x.
Time Definition getX := Call! GetX.
Time End OpWrappers.
Time End GoModel.
Time End Globals.
Time Arguments Globals.Op G : clear implicits.
Time Arguments Globals.State G : clear implicits.
