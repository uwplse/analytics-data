Time From RecordUpdate Require Import RecordSet.
Time From stdpp Require gmap.
Time From stdpp Require Import fin_maps.
Time From Perennial Require Export Lib.
Time From Perennial Require Import Spec.SemanticsHelpers Spec.LockDefs.
Time From Perennial.Goose Require Import Machine Heap Examples.MailServer.
Time From Perennial.Helpers Require Import RecordZoom.
Time From Transitions Require Import Relations.
Time Module Mail.
Time Section GoModel.
Time Context `{model_wf : GoModelWf}.
Time Implicit Type uid : uint64.
Time
Inductive Op : Type -> Type :=
  | Open : Op unit
  | Pickup_Start : forall uid, Op (list (string * list byte))
  | Pickup_End :
      forall uid (msgs : list (string * list byte)), Op (slice.t Message.t)
  | Deliver_Start : forall uid (msg : slice.t byte), Op unit
  | Deliver_End : forall uid (msg : slice.t byte), Op unit
  | Delete : forall uid (msgID : string), Op unit
  | Lock : forall uid, Op unit
  | Unlock : forall uid, Op unit
  | DataOp : forall T (op : Data.Op T), Op T.
Time
Inductive MailboxStatus :=
  | MPickingUp : _
  | MLocked : _
  | MUnlocked : _.
Time
Definition mailbox_lock_acquire (s : MailboxStatus) : 
  option MailboxStatus :=
  match s with
  | MPickingUp => None
  | MLocked => None
  | MUnlocked => Some MPickingUp
  end.
Time
Definition mailbox_lock_acquire_full (s : MailboxStatus) :
  option MailboxStatus :=
  match s with
  | MPickingUp => None
  | MLocked => None
  | MUnlocked => Some MLocked
  end.
Time
Definition mailbox_finish_pickup (s : MailboxStatus) :
  option MailboxStatus :=
  match s with
  | MPickingUp => Some MLocked
  | MLocked => None
  | MUnlocked => None
  end.
Time
Definition mailbox_lock_release (s : MailboxStatus) : 
  option MailboxStatus :=
  match s with
  | MPickingUp => None
  | MLocked => Some MUnlocked
  | MUnlocked => None
  end.
Time
Record State : Type :={heap : Data.State;
                       messages :
                        gmap.gmap uint64
                          (MailboxStatus * gmap.gmap string (list byte));
                       open : bool}.
Time #[global]
Instance etaState : (Settable _) :=
 settable! Build_State < heap; messages; open >.
Time Import RelationNotations.
Time
Definition lookup K `{countable.Countable K} V
  (proj : State -> gmap.gmap K V) (k : K) : relation State State V :=
  readSome (fun s => s.(proj) !! k).
Time
Definition createSlice V (data : List.list V) :
  relation State State (slice.t V) :=
  r <-
  such_that
    (fun s (r : ptr _) => Data.getAlloc r s.(heap) = None /\ r <> nullptr _);
  salloc <-
  such_that
    (fun _ (salloc : slice.t _ * List.list V) =>
     let (sli, alloc) := salloc in
     sli.(slice.ptr) = r \226\136\167 Data.getSliceModel sli alloc = Some data);
  _ <-
  puts
    (set heap
       (set Data.allocs (updDyn (a:=Ptr.Heap V) r (Unlocked, snd salloc))));
  pure (fst salloc).
Time
Definition createMessages (msgs : list (string * list byte)) :
  list Message.t :=
  map (\206\187 '(name, contents), Message.mk name (bytes_to_string contents)) msgs.
Time Section OpWrappers.
Time
Definition pickup uid : proc Op (slice.t Message.t) :=
  (msgs <- Call (Pickup_Start uid); Call (Pickup_End uid msgs))%proc.
Time
Definition deliver uid msg : proc Op unit :=
  (_ <- Call (Deliver_Start uid msg); Call (Deliver_End uid msg))%proc.
Time End OpWrappers.
Time
Definition readSlice T (p : slice.t T) : relation State State (list T) :=
  let! (s, alloc) <-
  readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
  _ <- readSome (fun _ => lock_available Reader s);
  pure (list.take p.(slice.length) (list.drop p.(slice.offset) alloc)).
Time
Definition readLockSlice T (p : slice.t T) : relation State State unit :=
  let! (s, alloc) <-
  readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
  s' <- readSome (fun _ => lock_acquire Reader s);
  _ <- readSome (fun _ => Data.getSliceModel p alloc);
  puts
    (set heap
       (set Data.allocs (updDyn (a:=Ptr.Heap T) p.(slice.ptr) (s', alloc)))).
Time
Definition readUnlockSlice T (p : slice.t T) :
  relation State State (list T) :=
  let! (s, alloc) <-
  readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
  s' <- readSome (fun _ => lock_release Reader s);
  _ <-
  puts
    (set heap
       (set Data.allocs (updDyn (a:=Ptr.Heap T) p.(slice.ptr) (s', alloc))));
  readSome (fun _ => Data.getSliceModel p alloc).
Time
Definition step_closed T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | Open =>
      _ <- puts (set open (\206\187 _, true));
      puts (set messages (\206\187 m, (\206\187 inbox, (MUnlocked, snd inbox)) <$> m))
  | _ => error
  end.
Time
Definition step_open T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | Pickup_Start uid =>
      let! (s, msgs) <- lookup messages uid;
      match mailbox_lock_acquire s with
      | Some s =>
          _ <- puts (set messages <[uid:=(s, msgs)]>);
          such_that
            (\206\187 _ msgs', Permutation.Permutation msgs' (map_to_list msgs))
      | None => none
      end
  | Pickup_End uid msgs =>
      let! (s, msgs') <- lookup messages uid;
      s <- Filesys.FS.unwrap (mailbox_finish_pickup s);
      _ <- puts (set messages <[uid:=(s, msgs')]>);
      createSlice (createMessages msgs)
  | Deliver_Start uid msg => readLockSlice msg
  | Deliver_End uid msg =>
      let! (s, msgs) <- lookup messages uid;
      n <- such_that (fun _ (n : string) => msgs !! n = None);
      msg <- readUnlockSlice msg;
      puts (set messages <[uid:=(s, <[n:=msg]> msgs)]>)
  | Delete uid msg =>
      let! (s, msgs) <- lookup messages uid;
      match s with
      | MLocked =>
          _ <- Filesys.FS.unwrap (msgs !! msg);
          puts (set messages <[uid:=(s, delete msg msgs)]>)
      | _ => error
      end
  | Lock uid =>
      let! (s, msgs) <- lookup messages uid;
      s <- Filesys.FS.unwrap (mailbox_lock_acquire_full s);
      puts (set messages <[uid:=(s, msgs)]>)
  | Unlock uid =>
      let! (s, msgs) <- lookup messages uid;
      s <- Filesys.FS.unwrap (mailbox_lock_release s);
      puts (set messages <[uid:=(s, msgs)]>)
  | DataOp op =>
      match op with
      | Data.NewMap _ => error
      | Data.MapLookup _ _ => error
      | Data.MapAlter _ _ _ _ => error
      | Data.MapStartIter _ => error
      | Data.MapEndIter _ => error
      | Data.Uint64Get _ _ => error
      | Data.Uint64Put _ _ _ => error
      | _ => _zoom heap (Data.step op)
      end
  | Open => error
  end.
Time
Definition step T (op : Op T) : relation State State T :=
  i <- reads open;
  match i with
  | true => step_open op
  | false => step_closed op
  end.
Time
Definition crash_step : relation State State unit :=
  _ <- puts (set open (\206\187 _, false)); puts (set heap (\206\187 _, \226\136\133)).
Time
Definition finish_step : relation State State unit :=
  _ <- puts (set open (\206\187 _, false)); puts (set heap (\206\187 _, \226\136\133)).
Time
Definition sem : Dynamics Op State :=
  {|
  Proc.step := step;
  Proc.crash_step := crash_step;
  Proc.finish_step := finish_step |}.
Time
Definition initP (s : State) :=
  s.(heap) = \226\136\133 /\
  s.(open) = false /\
  (forall uid : uint64,
   (uid < 100 -> s.(messages) !! uid = Some (MUnlocked, \226\136\133)) /\
   (uid >= 100 -> s.(messages) !! uid = None)).
Time
Lemma crash_step_val :
  \226\136\128 s1 : State, \226\136\131 s2 : State, sem.(Proc.crash_step) s1 (Val s2 ()).
Time Proof.
Time (intros s1).
Time (do 3 eexists; split; econstructor).
Time Qed.
Time
Lemma finish_step_val :
  \226\136\128 s1 : State, \226\136\131 s2 : State, sem.(Proc.finish_step) s1 (Val s2 ()).
Time Proof.
Time (intros s1).
Time (do 3 eexists; split; econstructor).
Time Qed.
Time
Lemma crash_step_non_err :
  \226\136\128 (s1 : State) (ret : Return State ()),
    sem.(Proc.crash_step) s1 ret \226\134\146 ret \226\137\160 Err.
Time Proof.
Time (intros s1 ret H).
Time (destruct ret; inversion H; eauto).
Time (repeat deex).
Time (inversion H1).
Time Qed.
Time
Lemma finish_step_non_err :
  \226\136\128 (s1 : State) (ret : Return State ()),
    sem.(Proc.finish_step) s1 ret \226\134\146 ret \226\137\160 Err.
Time Proof.
Time (intros s1 ret H).
Time (destruct ret; inversion H; eauto).
Time (repeat deex).
Time (inversion H1).
Time Qed.
Time Definition l : Layer Op.
Time
(refine
  {| Layer.sem := sem; trace_proj := fun _ => nil; Layer.initP := initP |};
  intros; try reflexivity; eauto
  using crash_step_val, finish_step_val, crash_step_non_err,
    finish_step_non_err).
Time Defined.
Time End GoModel.
Time End Mail.
