#[global]Set Implicit Arguments.
#[global]Generalizable Variables all.
Axiom (baseOpT : Type -> Type).
CoInductive proc (T : Type) : Type :=
  | BaseOp : forall op : baseOpT T, _
  | Ret : forall v : T, _
  | Bind : forall (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), _.
Require Extraction.
Extraction Language Haskell.
Extract Inductive proc =>  "Proc" [
  "error 'accessing BaseOp'"  "return"  "(>>=)" ]
 "(\fprim fret fbind -> error 'pattern match on proc')".
Axiom (world : Type).
Inductive Result T :=
  | Finished : forall (v : T) (w : world), _
  | Crashed : forall w : world, _.
Arguments Crashed {T} w.
Axiom (base_step : forall T, baseOpT T -> world -> T -> world -> Prop).
Inductive exec : forall T, proc T -> world -> Result T -> Prop :=
  | ExecRet : forall T (v : T) w, exec (Ret v) w (Finished v w)
  | ExecBindFinished :
      forall T T' (p : proc T) (p' : T -> proc T') w v w' r,
      exec p w (Finished v w') -> exec (p' v) w' r -> exec (Bind p p') w r
  | ExecOp :
      forall T (op : baseOpT T) w v w',
      base_step op w v w' -> exec (BaseOp op) w (Finished v w')
  | ExecCrashBegin : forall T (p : proc T) w, exec p w (Crashed w)
  | ExecCrashEnd :
      forall T (p : proc T) w v w',
      exec p w (Finished v w') -> exec p w (Crashed w')
  | ExecBindCrashed :
      forall T T' (p : proc T) (p' : T -> proc T') w w',
      exec p w (Crashed w') -> exec (Bind p p') w (Crashed w').
Axiom (world_crash : world -> world).
Inductive exec_recover R (rec : proc R) (w : world) : R -> world -> Prop :=
  | ExecRecoverExec :
      forall v w', exec rec w (Finished v w') -> exec_recover rec w v w'
  | ExecRecoverCrashDuringRecovery :
      forall w' v w'',
      exec rec w (Crashed w') ->
      exec_recover rec (world_crash w') v w'' -> exec_recover rec w v w''.
Inductive RResult T R :=
  | RFinished : forall (v : T) (w : world), _
  | Recovered : forall (v : R) (w : world), _.
Arguments RFinished {T} {R} v w.
Arguments Recovered {T} {R} v w.
Inductive rexec T R : proc T -> proc R -> world -> RResult T R -> Prop :=
  | RExec :
      forall (p : proc T) (rec : proc R) w v w',
      exec p w (Finished v w') -> rexec p rec w (RFinished v w')
  | RExecCrash :
      forall (p : proc T) (rec : proc R) w w' rv w'',
      exec p w (Crashed w') ->
      exec_recover rec (world_crash w') rv w'' ->
      rexec p rec w (Recovered rv w'').
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 60, right associativity).
Arguments Ret {T} v.
