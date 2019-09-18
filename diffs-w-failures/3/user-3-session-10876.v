From Coq Require Import List.
From RecoveryRefinement Require Import Lib.
From RecoveryRefinement Require Export Lib.
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
Definition set (i : id) (v : nat) : State -> State :=
  match i with
  | Sum => fun '(_, y) => (v, y)
  | Count => fun '(x, _) => (x, v)
  end.
Require Export Maybe.
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Read i => reads (get i)
          | Write i v => puts (set i v)
          end;
  crash_step := puts (fun _ => (0, 0)) |}.
Definition l : Layer Op :=
  {| Layer.State := State; sem := dynamics; initP := fun s => s = (0, 0) |}.
End Var.
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
          | Avg => reads (fun l => fold_right plus 0 l / length l)
          end;
  crash_step := puts (fun _ => nil) |}.
Definition l : Layer Op :=
  {| Layer.State := State; sem := dynamics; initP := fun s => s = nil |}.
End DB.
Definition read i := Call (Var.Read i).
Definition write i v := Call (Var.Write i v).
Definition impl : LayerImpl Var.Op DB.Op :=
  {|
  compile_op := fun T (op : DB.Op T) =>
                match op with
                | DB.Add n =>
                    (sum <- read Var.Sum;
                     _ <- write Var.Sum (n + sum)%nat;
                     count <- read Var.Count;
                     _ <- write Var.Count (1 + count)%nat; Ret tt)%proc
                | DB.Avg =>
                    (sum <- read Var.Sum;
                     count <- read Var.Count; Ret (sum / count)%nat)%proc
                end;
  recover := Ret tt;
  init := Ret Initialized |}.
Require Export Disk.
Import RelationNotations.
Module TwoDisk.
Inductive diskId :=
  | d0 : _
  | d1 : _.
Inductive DiskResult T :=
  | Working : forall v : T, _
  | Failed : _.
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
Inductive op_step : OpSemantics Op State :=
  | step_read :
      forall a i r state,
      match get_disk i state with
      | Some d =>
          match index d a with
          | Some b0 => r = Working b0
          | None => exists b, r = Working b
          end
      | None => r = Failed
      end -> op_step (op_read i a) state state r
  | step_write :
      forall a i b state r state',
      match get_disk i state with
      | Some d => state' = set_disk i state (assign d a b) /\ r = Working tt
      | None => r = Failed /\ state' = state
      end -> op_step (op_write i a b) state state' r
  | step_size :
      forall i state r,
      match get_disk i state with
      | Some d => r = Working (length d)
      | None => r = Failed
      end -> op_step (op_size i) state state r.
Inductive bg_failure : State -> State -> unit -> Prop :=
  | step_id : forall state : State, bg_failure state state tt
  | step_fail0 :
      forall d_0 d_1, bg_failure (BothDisks d_0 d_1) (OnlyDisk1 d_1) tt
  | step_fail1 :
      forall d_0 d_1, bg_failure (BothDisks d_0 d_1) (OnlyDisk0 d_0) tt.
Definition pre_step {opT} {State} (bg_step : State -> State -> unit -> Prop)
  (step : OpSemantics opT State) : OpSemantics opT State :=
  fun T (op : opT T) state state'' v =>
  exists state', bg_step state state' tt /\ step _ op state' state'' v.
Definition combined_step := pre_step bg_failure (@op_step).
Definition TDBaseDynamics : Dynamics Op State :=
  {| step := op_step; crash_step := RelationAlgebra.identity |}.
Definition td_init (s : State) :=
  exists d_0' d_1', disk0 s ?|= eq d_0' /\ disk1 s ?|= eq d_1'.
Lemma td_init_alt s : td_init s <-> True.
Proof.
(split; auto; intros).
(destruct s as [d0 d1| d| d]).
-
(repeat eexists; try congruence).
-
exists d,d.
firstorder.
-
exists d,d.
firstorder.
Qed.
Definition TDLayer : Layer Op :=
  {| Layer.State := State; sem := TDBaseDynamics; initP := td_init |}.
End TwoDisk.
Module td.
Import TwoDisk.
Definition read i a : proc Op (DiskResult block) := Call (op_read i a).
Definition write i a b : proc Op (DiskResult unit) := Call (op_write i a b).
Definition size i : proc Op (DiskResult nat) := Call (op_size i).
End td.
