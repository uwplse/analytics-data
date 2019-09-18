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
Hint Resolve put_ok: core.
Definition State : Type := list block.
Definition get_spec : Specification unit (list block) unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = state;
  recovered := fun _ state' => state' = state |}.
Definition append_spec v : Specification unit bool unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' =>
          r = true /\ state' = state ++ v \/ r = false /\ state' = state;
  recovered := fun _ state' => state' = state \/ state' = state ++ v |}.
Hint Resolve recover_wipe: core.
End AtomicPairAPI.
Definition reset_spec : Specification unit unit unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => r = tt /\ state' = nil;
  recovered := fun _ state' => state' = state \/ state' = nil |}.
Module Type LogAPI.
Axiom (init : proc InitResult).
Axiom (get : proc (list block)).
Axiom (append : list block -> proc bool).
Axiom (reset : proc unit).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom (get_ok : proc_spec get_spec get recover abstr).
Axiom
  (append_ok : forall v, proc_spec (append_spec v) (append v) recover abstr).
Axiom (reset_ok : proc_spec reset_spec reset recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_wipe).
Hint Resolve init_ok: core.
Hint Resolve get_ok: core.
Hint Resolve append_ok: core.
Hint Resolve reset_ok: core.
Hint Resolve recover_wipe: core.
End LogAPI.
