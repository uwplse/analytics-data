Require Import POCS.
Require Import POCS.
Inductive var :=
  | VarCount : _
  | VarSum : _.
Record State := mkState {StateCount : nat; StateSum : nat}.
Definition read_spec v : Specification _ _ unit _ :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          state' = state /\
          match v with
          | VarCount => r = StateCount state
          | VarSum => r = StateSum state
          end;
  recovered := fun _ _ => False |}.
Definition write_spec v val : Specification _ _ unit _ :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          r = tt /\
          match v with
          | VarCount => state' = mkState val (StateSum state)
          | VarSum => state' = mkState (StateCount state) val
          end;
  recovered := fun _ _ => False |}.
Module Type VarsAPI.
Axiom (init : proc InitResult).
Axiom (read : var -> proc nat).
Axiom (write : var -> nat -> proc unit).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (read_ok : forall v, proc_spec (read_spec v) (read v) recover abstr).
Axiom
  (write_ok :
     forall v val, proc_spec (write_spec v val) (write v val) recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_crash).
Hint Resolve init_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve recover_wipe: core.
End VarsAPI.
Inductive var :=
  | VarX : _
  | VarY : _
  | VarZ : _.
Instance var_eq : (EqualDec var).
Proof.
(hnf).
(destruct x, y; simpl; (left; congruence) || (right; congruence)).
Defined.
Record State := mkState {StateX : nat; StateY : nat; StateZ : nat}.
Definition StateVar (v : var) (state : State) : nat :=
  match v with
  | VarX => StateX state
  | VarY => StateY state
  | VarZ => StateZ state
  end.
Definition read_spec v : Specification _ _ unit _ :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ r = StateVar v state;
  recovered := fun _ _ => False |}.
Definition write_spec v val : Specification _ _ unit _ :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          r = tt /\
          match v with
          | VarX => state' = mkState val (StateY state) (StateZ state)
          | VarY => state' = mkState (StateX state) val (StateZ state)
          | VarZ => state' = mkState (StateX state) (StateY state) val
          end;
  recovered := fun _ _ => False |}.
Module Type VarsAPI.
Axiom (init : proc InitResult).
Axiom (read : var -> proc nat).
Axiom (write : var -> nat -> proc unit).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (read_ok : forall v, proc_spec (read_spec v) (read v) recover abstr).
Axiom
  (write_ok :
     forall v val, proc_spec (write_spec v val) (write v val) recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_crash).
Hint Resolve init_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve recover_wipe: core.
End VarsAPI.
