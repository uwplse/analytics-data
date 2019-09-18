Require Import POCS.
Require Import POCS.
Require Import POCS.
Definition State := list nat.
Definition inited (s : State) : Prop := s = nil.
Definition add_spec v : Specification unit unit unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = tt /\ state' = v :: state;
  recovered := fun _ _ => False |}.
Definition mean_spec : Specification unit (option nat) unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          state' = state /\
          (state = nil /\ r = None \/
           state <> nil /\ r = Some (fold_right plus 0 state / length state));
  recovered := fun _ _ => False |}.
Module Type StatDbAPI.
Axiom (init : proc InitResult).
Axiom (add : nat -> proc unit).
Axiom (mean : proc (option nat)).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited).
Axiom (add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr).
Axiom (mean_ok : proc_spec mean_spec mean recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_crash).
Inductive var :=
  | VarCount : _
  | VarSum : _.
Inductive var :=
  | VarX : _
  | VarY : _
  | VarZ : _.
Hint Resolve init_ok: core.
Hint Resolve add_ok: core.
Hint Resolve mean_ok: core.
Hint Resolve recover_wipe: core.
End StatDbAPI.
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
Instance var_eq : (EqualDec var).
Proof.
(hnf).
(destruct x, y; simpl; (left; reflexivity) || (right; inversion 1)).
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
Defined.
Hint Resolve init_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve recover_wipe: core.
End VarsAPI.
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
