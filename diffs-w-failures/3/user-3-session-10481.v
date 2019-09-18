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
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr).
Axiom
  (write_ok :
     forall a v, proc_spec (write_spec a v) (write a v) recover abstr).
Axiom (getBadBlock_ok : proc_spec getBadBlock_spec getBadBlock recover abstr).
Axiom (size_ok : proc_spec size_spec size recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_wipe).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited).
Axiom (add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr).
Axiom (mean_ok : proc_spec mean_spec mean recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_crash).
Hint Resolve init_ok: core.
Hint Resolve add_ok: core.
Hint Resolve mean_ok: core.
Hint Resolve recover_wipe: core.
End StatDbAPI.
Hint Resolve init_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve getBadBlock_ok: core.
Hint Resolve size_ok: core.
Hint Resolve recover_wipe: core.
End BadBlockAPI.
