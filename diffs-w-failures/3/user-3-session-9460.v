Require Import POCS.
Require Import POCS.
Inductive diskId :=
  | d0 : _
  | d1 : _.
Inductive DiskResult T :=
  | Working : forall v : T, _
  | Failed : _.
Require Import Lab0.HeapVariablesAPI.
Module HeapExamples (vars: VarsAPI).
Definition swapXY : proc unit :=
  x <- vars.read VarX;
  y <- vars.read VarY; _ <- vars.write VarX y; _ <- vars.write VarY x; Ret tt.
Arguments Failed {T}.
Inductive State :=
  | BothDisks : forall (d_0 : disk) (d_1 : disk), _
  | OnlyDisk0 : forall d_0 : disk, _
  | OnlyDisk1 : forall d_1 : disk, _.
Definition disk0 (state : State) : option disk :=
  match state with
  | BothDisks d_0 _ => Some d_0
  | OnlyDisk0 d => Some d
  | OnlyDisk1 _ => None
  end.
Definition disk1 (state : State) : option disk :=
  match state with
  | BothDisks _ d_1 => Some d_1
  | OnlyDisk0 _ => None
  | OnlyDisk1 d => Some d
  end.
Definition get_disk (i : diskId) (state : State) : 
  option disk := match i with
                 | d0 => disk0 state
                 | d1 => disk1 state
                 end.
Definition set_disk (i : diskId) (state : State) (d : disk) : State :=
  match i with
  | d0 =>
      match state with
      | BothDisks _ d_1 => BothDisks d d_1
      | OnlyDisk0 _ => OnlyDisk0 d
      | OnlyDisk1 d_1 => BothDisks d d_1
      end
  | d1 =>
      match state with
      | BothDisks d_0 _ => BothDisks d_0 d
      | OnlyDisk0 d_0 => BothDisks d_0 d
      | OnlyDisk1 _ => OnlyDisk1 d
      end
  end.
Inductive Op : Type -> Type :=
  | op_read : forall (i : diskId) (a : addr), Op (DiskResult block)
  | op_write :
      forall (i : diskId) (a : addr) (b : block), Op (DiskResult unit)
  | op_size : forall i : diskId, Op (DiskResult nat).
Theorem swapXY_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' = mkState (StateY state) (StateX state) (StateZ state);
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(unfold swapXY).
step_proc.
step_proc.
Inductive op_step : forall `(op : Op T), Semantics State T :=
  | step_read :
      forall a i r state,
      match get_disk i state with
      | Some d =>
          match diskGet d a with
          | Some b0 => r = Working b0
          | None => exists b, r = Working b
          end
      | None => r = Failed
      end -> op_step (op_read i a) state r state
  | step_write :
      forall a i b state r state',
      match get_disk i state with
      | Some d => state' = set_disk i state (diskUpd d a b) /\ r = Working tt
      | None => r = Failed /\ state' = state
      end -> op_step (op_write i a b) state r state'
  | step_size :
      forall i state r,
      match get_disk i state with
      | Some d => r = Working (diskSize d)
      | None => r = Failed
      end -> op_step (op_size i) state r state.
step_proc.
step_proc.
Inductive bg_failure : State -> State -> Prop :=
  | step_id : forall state : State, bg_failure state state
  | step_fail0 :
      forall d_0 d_1, bg_failure (BothDisks d_0 d_1) (OnlyDisk1 d_1)
  | step_fail1 :
      forall d_0 d_1, bg_failure (BothDisks d_0 d_1) (OnlyDisk0 d_0).
step_proc.
Qed.
Definition combined_step := pre_step bg_failure (@op_step).
Module Type TwoDiskBaseAPI.
Axiom (init : proc InitResult).
Axiom (read : diskId -> addr -> proc (DiskResult block)).
Axiom (write : diskId -> addr -> block -> proc (DiskResult unit)).
Axiom (size : diskId -> proc (DiskResult nat)).
Axiom (recover : proc unit).
Axiom (abstr : Abstraction State).
Axiom (init_ok : init_abstraction init recover abstr inited_any).
Axiom
  (read_ok :
     forall i a,
     proc_spec (op_spec (combined_step (op_read i a))) 
       (read i a) recover abstr).
Axiom
  (write_ok :
     forall i a b,
     proc_spec (op_spec (combined_step (op_write i a b))) 
       (write i a b) recover abstr).
Axiom
  (size_ok :
     forall i,
     proc_spec (op_spec (combined_step (op_size i))) (size i) recover abstr).
Axiom (recover_wipe : rec_wipe recover abstr no_wipe).
Hint Resolve init_ok: core.
Hint Resolve read_ok: core.
Hint Resolve write_ok: core.
Hint Resolve size_ok: core.
Hint Resolve recover_wipe: core.
End TwoDiskBaseAPI.
Theorem swapXY_ok2 :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState y x z;
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(unfold swapXY).
step_proc.
(destruct a' as ((x, y), z); simplify).
step_proc.
step_proc.
step_proc.
step_proc.
Qed.
Definition swapYZ : proc unit :=
  y <- vars.read VarY;
  z <- vars.read VarZ; _ <- vars.write VarY z; _ <- vars.write VarZ y; Ret tt.
Theorem swapYZ_ok :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState x z y;
     recovered := fun _ state' => True |}) swapYZ vars.recover vars.abstr.
Proof.
(unfold swapYZ).
step_proc.
(destruct a' as ((x, y), z); simplify).
step_proc.
step_proc.
step_proc.
step_proc.
Qed.
Definition swapXZ : proc unit :=
  _ <- swapXY; _ <- swapYZ; _ <- swapXY; Ret tt.
Hint Resolve swapXY_ok2 swapYZ_ok: core.
Theorem swapXZ_ok :
  proc_spec
    (fun '(x, y, z) state =>
     {|
     pre := StateX state = x /\ StateY state = y /\ StateZ state = z;
     post := fun r state' => state' = mkState z y x;
     recovered := fun _ state' => True |}) swapXZ vars.recover vars.abstr.
Proof.
(unfold swapXZ).
(spec_intros; simplify).
(destruct a as ((x, y), z); simplify).
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
step_proc.
(eexists (_, _, _); simplify; intuition eauto).
step_proc.
Qed.
Definition swapVars (v1 v2 : var) : proc unit :=
  v1_val <- vars.read v1;
  v2_val <- vars.read v2;
  _ <- vars.write v1 v2_val; _ <- vars.write v2 v1_val; Ret tt.
Theorem swapVars_ok v1 v2 :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             forall v,
             StateVar v state' =
             (if v == v1
              then StateVar v2 state
              else if v == v2 then StateVar v1 state else StateVar v state);
     recovered := fun _ state' => True |}) (swapVars v1 v2) vars.recover
    vars.abstr.
Proof.
(unfold swapVars).
step_proc.
step_proc.
step_proc.
step_proc.
step_proc.
(destruct v, v1, v2; intuition).
Qed.
Definition inc1 (v1 : var) : proc unit :=
  v <- vars.read v1; _ <- vars.write v1 (1 + v); Ret tt.
Definition inc1X_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (1 + StateX state) (StateY state) (StateZ state);
     recovered := fun _ state' => True |}) (inc1 VarX) vars.recover
    vars.abstr.
Proof.
(unfold inc1).
step_proc.
step_proc.
step_proc.
Qed.
Hint Resolve inc1X_ok: core.
Fixpoint increment (v1 : var) (n : nat) : proc unit :=
  match n with
  | 0 => Ret tt
  | S n' => _ <- inc1 v1; increment v1 n'
  end.
Theorem incrementX_ok n :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (n + StateX state) (StateY state) (StateZ state);
     recovered := fun _ state' => True |}) (increment VarX n) vars.recover
    vars.abstr.
Proof.
(induction n; simpl).
-
step_proc.
(destruct state; auto).
-
step_proc.
step_proc.
(simpl).
f_equal.
lia.
Qed.
End HeapExamples.
