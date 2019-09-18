Require Import POCS.
Require Import POCS.
Definition State : Type := block * block.
Definition get_spec : Specification unit (block * block) unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = state;
  recovered := fun _ state' => state' = state |}.
Definition put_spec v : Specification unit unit unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = tt /\ state' = v;
  recovered := fun _ state' => state' = state \/ state' = v |}.
Module Type AtomicPairAPI.
Axiom (init : proc InitResult).
Axiom (get : proc (block * block)).
Axiom (put : block * block -> proc unit).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (get_ok : proc_spec get_spec get recover abstr).
Axiom (put_ok : forall v, proc_spec (put_spec v) (put v) recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_wipe).
Hint Resolve init_ok: core.
Hint Resolve get_ok: core.
Definition State := disk.
Definition read_spec (a : addr) : Specification _ block unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ diskGet state a =?= r;
  recovered := fun _ state' => state' = state |}.
Definition write_spec (a : addr) (v : block) :
  Specification _ _ unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = tt /\ state' = diskUpd state a v;
  recovered := fun _ state' => state' = state \/ state' = diskUpd state a v |}.
Definition size_spec : Specification _ nat unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ r = diskSize state;
  recovered := fun _ state' => state' = state |}.
Module Type OneDiskAPI.
Axiom (init : proc InitResult).
Axiom (read : addr -> proc block).
Axiom (write : addr -> block -> proc unit).
Axiom (size : proc nat).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr).
Hint Resolve put_ok: core.
Hint Resolve recover_wipe: core.
End AtomicPairAPI.
Axiom
  (write_ok :
     forall a v, proc_spec (write_spec a v) (write a v) recover abstr).
Axiom (size_ok : proc_spec size_spec size recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_wipe).
Hint Resolve init_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve size_ok: core.
Hint Resolve recover_wipe: core.
End OneDiskAPI.
