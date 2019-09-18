Require Import POCS.
Require Import POCS.
Record State := mkState {stateDisk : disk; stateBadBlock : addr}.
Definition read_spec a : Specification _ block unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          state' = state /\
          (a <> stateBadBlock state -> diskGet (stateDisk state) a =?= r);
  recovered := fun _ state' => state' = state |}.
Definition write_spec a v : Specification _ _ unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          r = tt /\
          state' =
          mkState (diskUpd (stateDisk state) a v) (stateBadBlock state);
  recovered := fun _ state' =>
               state' = state \/
               state' =
               mkState (diskUpd (stateDisk state) a v) (stateBadBlock state) |}.
Inductive var :=
  | VarCount : _
  | VarSum : _.
Definition getBadBlock_spec : Specification _ addr unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ r = stateBadBlock state;
  recovered := fun _ state' => state' = state |}.
Definition size_spec : Specification _ nat unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ r = diskSize (stateDisk state);
  recovered := fun _ state' => state' = state |}.
Module Type BadBlockAPI.
Axiom (init : proc InitResult).
Axiom (read : addr -> proc block).
Axiom (write : addr -> block -> proc unit).
Axiom (getBadBlock : proc addr).
Axiom (size : proc nat).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr).
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
Axiom
  (write_ok :
     forall a v, proc_spec (write_spec a v) (write a v) recover abstr).
Axiom (getBadBlock_ok : proc_spec getBadBlock_spec getBadBlock recover abstr).
Axiom (size_ok : proc_spec size_spec size recover abstr).
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
Axiom (recover_wipe : rec_wipe recover abstr no_wipe).
Hint Resolve init_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve getBadBlock_ok: core.
Hint Resolve size_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve recover_wipe: core.
End VarsAPI.
Hint Resolve recover_wipe: core.
End BadBlockAPI.
