Time From Coq Require Import List.
Time From RecordUpdate Require Import RecordSet.
Time From stdpp Require gmap.
Time From Coq Require Import List.
Time From Coq Require Import List.
Time From Armada Require Export Lib.
Time From stdpp Require Import gmap.
Time From stdpp Require Import gmap.
Time From stdpp Require Import fin_maps.
Time From Armada Require Export Lib.
Time From Armada Require Export Lib.
Time From Armada Require Export Lib.
Time Module AtomicPair.
Time
Inductive Op : Type -> Type :=
  | Write : forall p : nat * nat, Op unit
  | Read : Op (nat * nat).
Time Definition State : Set := nat * nat.
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Write p => puts (fun _ => p)
          | Read => reads (fun l => l)
          end;
  crash_step := pure tt;
  finish_step := pure tt |}.
Time
Lemma crash_total_ok (s : State) :
  exists s', dynamics.(crash_step) s (Val s' tt).
Time Proof.
Time (eexists; econstructor).
Time Qed.
Time
Lemma crash_non_err_ok (s : State) ret :
  dynamics.(crash_step) s ret -> ret \226\137\160 Err.
Time Proof.
Time (inversion 1; congruence).
Time Qed.
Time
Definition l : Layer Op :=
  {|
  Layer.OpState := State;
  sem := dynamics;
  trace_proj := fun _ => nil;
  crash_preserves_trace := fun _ _ _ => eq_refl;
  crash_total := crash_total_ok;
  finish_total := crash_total_ok;
  crash_non_err := crash_non_err_ok;
  finish_non_err := crash_non_err_ok;
  initP := fun s => s = (0, 0) |}.
Time End AtomicPair.
Time From Armada Require Import Spec.SemanticsHelpers Spec.LockDefs.
Time Module ExMach.
Time Definition size := 1000.
Time Definition addr := nat.
Time
Inductive Op : Type -> Type :=
  | Read_Mem : forall i : addr, Op nat
  | Write_Mem : forall (i : addr) (v : nat), Op unit
  | CAS : forall (i : addr) (vold : nat) (vnew : nat), Op nat
  | Read_Disk : forall i : addr, Op nat
  | Write_Disk : forall (i : addr) (v : nat), Op unit
  | Fail : Op unit.
Time Definition size := 1000.
Time
Record State :=
 mkState {mem_state : gmap addr nat; disk_state : gmap addr nat}.
Time
Definition state_wf s :=
  (\226\136\128 i, is_Some (mem_state s !! i) \226\134\148 i < size)
  \226\136\167 (\226\136\128 i, is_Some (disk_state s !! i) \226\134\148 i < size).
Time Definition addr := nat.
Time
Definition wf_range (d : gmap addr nat) := \226\136\128 i, is_Some (d !! i) \226\134\148 i < size.
Time
Definition get_default (i : addr) (s : gmap addr nat) : nat :=
  match s !! i with
  | Some n => n
  | None => 0
  end.
Time
Definition set_default (i : addr) (v : nat) (s : gmap addr nat) :
  gmap addr nat := match s !! i with
                   | Some _ => <[i:=v]> s
                   | None => s
                   end.
Time
Definition get_mem (i : addr) : State -> nat :=
  fun s => get_default i (mem_state s).
Time
Definition get_disk (i : addr) : State -> nat :=
  fun s => get_default i (disk_state s).
Time
Fixpoint init_zero_aux (n : nat) (s : gmap addr nat) :=
  match n with
  | O => s
  | S n' => <[n':=O]> (init_zero_aux n' s)
  end.
Time Definition init_zero := init_zero_aux size gmap_empty.
Time
Lemma init_zero_insert_zero i : i < size \226\134\146 <[i:=0]> init_zero = init_zero.
Time Proof.
Time rewrite /init_zero.
Time (induction 1).
Time
Definition set_mem (i : addr) (v : nat) : State -> State :=
  fun s =>
  {|
  mem_state := set_default i v (mem_state s);
  disk_state := disk_state s |}.
Time
Definition set_disk (i : addr) (v : nat) : State -> State :=
  fun s =>
  {|
  mem_state := mem_state s;
  disk_state := set_default i v (disk_state s) |}.
Time Import RelationNotations.
Time
Definition cas_rel (i : addr) (vold : nat) (vnew : nat) :
  relation State State nat :=
  v <- reads (get_mem i);
  if nat_eq_dec v vold then puts (set_mem i vnew);; pure v else pure v.
Time
Fixpoint init_zero_aux (n : nat) (s : gmap addr nat) :=
  match n with
  | O => s
  | S n' => <[n':=O]> (init_zero_aux n' s)
  end.
Time Definition init_zero := init_zero_aux size gmap_empty.
Time
Lemma init_zero_insert_zero i : i < size \226\134\146 <[i:=0]> init_zero = init_zero.
Time Proof.
Time rewrite /init_zero.
Time -
Time rewrite //=.
Time rewrite insert_insert //.
Time -
Time rewrite //=.
Time (induction 1).
Time -
Time rewrite //=.
Time rewrite insert_insert //.
Time -
Time rewrite //=.
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_commute ; last  by lia).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_commute ; last  by lia).
Time From Armada.Goose Require Import Machine Heap Examples.MailServer.
Time rewrite IHle //=.
Time rewrite IHle //=.
Time Qed.
Time Qed.
Time Lemma init_zero_lookup_lt_zero i : i < size \226\134\146 init_zero !! i = Some 0.
Time From Armada.Helpers Require Import RecordZoom.
Time From Transitions Require Import Relations.
Time Module Mail.
Time Section GoModel.
Time Context `{model_wf : GoModelWf}.
Time Implicit Type uid : uint64.
Time Lemma init_zero_lookup_lt_zero i : i < size \226\134\146 init_zero !! i = Some 0.
Time Proof.
Time rewrite /init_zero.
Time (induction 1).
Time -
Time rewrite lookup_insert //=.
Time Proof.
Time rewrite /init_zero.
Time (induction 1).
Time -
Time rewrite lookup_insert //=.
Time -
Time rewrite //=.
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
Time -
Time rewrite //=.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by lia).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by lia).
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
Time eauto.
Time Qed.
Time eauto.
Time Qed.
Time Lemma init_zero_lookup_ge_None i : \194\172 i < size \226\134\146 init_zero !! i = None.
Time Proof.
Time revert i.
Time rewrite /init_zero.
Time (<ssreflect_plugin::ssrtclintros@0> induction size =>i ?).
Time Lemma init_zero_lookup_ge_None i : \194\172 i < size \226\134\146 init_zero !! i = None.
Time Proof.
Time revert i.
Time rewrite /init_zero.
Time (<ssreflect_plugin::ssrtclintros@0> induction size =>i ?).
Time -
Time rewrite //=.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by lia).
Time -
Time rewrite //=.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by lia).
Time (rewrite IHn; auto).
Time Qed.
Time #[global]
Instance etaState : (Settable _) :=
 settable! Build_State < heap; messages; open >.
Time (rewrite IHn; auto).
Time Qed.
Time Lemma wf_init_zero : wf_range init_zero.
Time Proof.
Time (intros i).
Time split.
Time -
Time (intros Hsome).
Time (apply not_ge).
Time (intros ?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite init_zero_lookup_ge_None // in 
 {} Hsome ; last  lia).
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
Definition init_state :=
  {| mem_state := init_zero; disk_state := init_zero |}.
Time Lemma init_state_wf : state_wf init_state.
Time Proof.
Time (cut (\226\136\128 i : nat, is_Some (init_state.(mem_state) !! i) \226\134\148 i < size)).
Time
Definition createMessages (msgs : list (string * list byte)) :
  list Message.t :=
  map (\206\187 '(name, contents), Message.mk name (bytes_to_string contents)) msgs.
Time Section OpWrappers.
Time
Definition pickup uid : proc Op (slice.t Message.t) :=
  (msgs <- Call (Pickup_Start uid); Call (Pickup_End uid msgs))%proc.
Time {
Time (intros; split; trivial).
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
Time (eapply is_Some_None; eauto).
Time -
Time (intros ?).
Time rewrite init_zero_lookup_lt_zero //.
Time eauto.
Time Qed.
Time
Lemma well_sized_mem_0_init (mem : gmap addr nat) :
  (\226\136\128 i, is_Some (mem !! i) \226\134\148 i < size) \226\134\146 (\206\187 _, 0) <$> mem = init_zero.
Time Proof.
Time (intros).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>i).
Time
Definition step_closed T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | Open =>
      _ <- puts (set open (\206\187 _, true));
      puts (set messages (\206\187 m, (\206\187 inbox, (MUnlocked, snd inbox)) <$> m))
  | _ => error
  end.
Time (destruct (nat_lt_dec i size)).
Time *
Time rewrite init_zero_lookup_lt_zero //.
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
Time rewrite lookup_fmap.
Time (edestruct (H i)).
Time (destruct H1; eauto).
Time rewrite H1 //=.
Time End Mail.
Time *
Time rewrite lookup_fmap.
Time (edestruct (H i)).
Time (destruct (mem !! i) as [| ] eqn:Heq).
Time **
Time rewrite Heq in  {} H0.
Time exfalso.
Time intuition eauto.
Time **
Time rewrite init_zero_lookup_ge_None //=.
Time Qed.
Time Module TwoDisk.
Time Inductive diskId :=
       | d0 : _
       | d1 : _.
Time Definition disk := gmap addr nat.
Time
Inductive DisksState :=
  | BothDisks : forall (d_0 : disk) (d_1 : disk), _
  | OnlyDisk : forall (id : diskId) (d : disk), _.
Time
Inductive Op : Type -> Type :=
  | Read_Mem : forall i : addr, Op nat
  | Write_Mem : forall (i : addr) (v : nat), Op unit
  | CAS : forall (i : addr) (vold : nat) (vnew : nat), Op nat
  | Read_Disk : forall (id : diskId) (i : addr), Op (option nat)
  | Write_Disk : forall (id : diskId) (i : addr) (v : nat), Op unit.
Time
Record State := mkState {mem_state : gmap addr nat; disks_state : DisksState}.
Time
Definition disk0 ds : option disk :=
  match disks_state ds with
  | BothDisks d_0 _ => Some d_0
  | OnlyDisk d0 d => Some d
  | OnlyDisk d1 _ => None
  end.
Time
Definition disk1 ds : option disk :=
  match disks_state ds with
  | BothDisks _ d_1 => Some d_1
  | OnlyDisk d0 _ => None
  | OnlyDisk d1 d => Some d
  end.
Time
Definition get_disk (i : diskId) (state : State) : 
  option disk := match i with
                 | d0 => disk0 state
                 | d1 => disk1 state
                 end.
Time
Definition wf_disk (md : option disk) :=
  match md with
  | Some d => wf_range d
  | None => True
  end.
Time
Definition state_wf s :=
  wf_range (mem_state s) \226\136\167 wf_disk (disk0 s) \226\136\167 wf_disk (disk1 s).
Time
Definition lookup_default (i : addr) (s : gmap addr nat) : nat :=
  match s !! i with
  | Some n => n
  | None => 0
  end.
Time
Definition upd_default (i : addr) (v : nat) (s : gmap addr nat) :
  gmap addr nat := match s !! i with
                   | Some _ => <[i:=v]> s
                   | None => s
                   end.
Time
Definition lookup_mem (i : addr) : State -> nat :=
  fun s => lookup_default i (mem_state s).
Time
Definition lookup_disk id (i : addr) : State -> option nat :=
  fun s =>
  match get_disk id s with
  | None => None
  | Some d => Some (lookup_default i d)
  end.
Time
Definition set_disk' (i : diskId) (state : DisksState) 
  (d : disk) : DisksState :=
  match i with
  | d0 =>
      match state with
      | BothDisks _ d_1 => BothDisks d d_1
      | OnlyDisk d0 _ => OnlyDisk d0 d
      | OnlyDisk d1 d_1 => BothDisks d d_1
      end
  | d1 =>
      match state with
      | BothDisks d_0 _ => BothDisks d_0 d
      | OnlyDisk d0 d_0 => BothDisks d_0 d
      | OnlyDisk d1 _ => OnlyDisk d1 d
      end
  end.
Time
Definition maybe_fail_disk' (i : diskId) (state : DisksState) : DisksState :=
  match i with
  | d0 =>
      match state with
      | BothDisks _ d_1 => OnlyDisk d1 d_1
      | _ => state
      end
  | d1 =>
      match state with
      | BothDisks d_0 _ => OnlyDisk d0 d_0
      | _ => state
      end
  end.
Time
Definition upd_mem (i : addr) (v : nat) :=
  fun s =>
  {|
  mem_state := upd_default i v (mem_state s);
  disks_state := disks_state s |}.
Time
Definition upd_disk (id : diskId) (i : addr) (v : nat) : 
  State -> State :=
  fun s =>
  {|
  mem_state := mem_state s;
  disks_state := match get_disk id s with
                 | Some d => set_disk' id (disks_state s) (upd_default i v d)
                 | None => disks_state s
                 end |}.
Time
Definition maybe_fail_disk (id : diskId) : State -> State :=
  fun s =>
  {|
  mem_state := mem_state s;
  disks_state := maybe_fail_disk' id (disks_state s) |}.
Time Import RelationNotations.
Time
Definition cas_rel (i : addr) (vold : nat) (vnew : nat) :
  relation State State nat :=
  v <- reads (lookup_mem i);
  if nat_eq_dec v vold then puts (upd_mem i vnew);; pure v else pure v.
Time
Definition init_state :=
  {| mem_state := init_zero; disks_state := BothDisks init_zero init_zero |}.
Time Lemma init_state_wf : state_wf init_state.
Time Proof.
Time (split_and !; apply wf_init_zero).
Time Qed.
Time
Definition crash_fun :=
  fun s => {| mem_state := init_zero; disks_state := disks_state s |}.
Time
Definition disk_fail :=
  rel_or (pure tt)
    (rel_or (puts (maybe_fail_disk d0)) (puts (maybe_fail_disk d1))).
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Read_Mem i => reads (lookup_mem i)
          | Write_Mem i v => puts (upd_mem i v)
          | Read_Disk id i => disk_fail;; reads (lookup_disk id i)
          | Write_Disk id i v => disk_fail;; puts (upd_disk id i v)
          | CAS i vold vnew => cas_rel i vold vnew
          end;
  crash_step := puts crash_fun;
  finish_step := puts crash_fun |}.
Time
Lemma crash_total_ok (s : State) :
  exists s', dynamics.(crash_step) s (Val s' tt).
Time Proof.
Time (eexists; econstructor).
Time Qed.
Time
Lemma crash_non_err_ok (s : State) ret :
  dynamics.(crash_step) s ret -> ret \226\137\160 Err.
Time Proof.
Time (inversion 1; congruence).
Time Qed.
Time
Definition l : Layer Op :=
  {|
  Layer.OpState := State;
  sem := dynamics;
  trace_proj := fun _ => nil;
  crash_preserves_trace := fun _ _ _ => eq_refl;
  crash_total := crash_total_ok;
  finish_total := crash_total_ok;
  crash_non_err := crash_non_err_ok;
  finish_non_err := crash_non_err_ok;
  initP := fun s => s = init_state |}.
Time End TwoDisk.
Time Definition read_mem i := Call (TwoDisk.Read_Mem i).
Time Definition write_mem i v := Call (TwoDisk.Write_Mem i v).
Time Definition read_disk id i := Call (TwoDisk.Read_Disk id i).
Time Definition write_disk id i v := Call (TwoDisk.Write_Disk id i v).
Time Definition cas i vold vnew := Call (TwoDisk.CAS i vold vnew).
Time
Definition lock i : proc TwoDisk.Op unit :=
  Loop
    (fun _ : unit =>
     x <- cas i 0 1;
     Ret (if nat_eq_dec x 0 then DoneWithOutcome tt else ContinueOutcome tt))%proc
    tt.
Time Definition unlock i : proc TwoDisk.Op unit := write_mem i 0.
Time }
Time (intros i).
Time split.
Time -
Time (intros Hsome).
Time (apply not_ge).
Time (intros ?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite init_zero_lookup_ge_None // in 
 {} Hsome ; last  lia).
Time (eapply is_Some_None; eauto).
Time -
Time (intros ?).
Time rewrite init_zero_lookup_lt_zero //.
Time eauto.
Time Qed.
Time
Lemma well_sized_mem_0_init (mem : gmap addr nat) :
  (\226\136\128 i, is_Some (mem !! i) \226\134\148 i < size) \226\134\146 (\206\187 _, 0) <$> mem = init_zero.
Time Proof.
Time (intros).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>i).
Time (destruct (nat_lt_dec i size)).
Time *
Time rewrite init_zero_lookup_lt_zero //.
Time rewrite lookup_fmap.
Time (edestruct (H i)).
Time (destruct H1; eauto).
Time rewrite H1 //=.
Time *
Time rewrite lookup_fmap.
Time (edestruct (H i)).
Time (destruct (mem !! i) as [| ] eqn:Heq).
Time **
Time rewrite Heq in  {} H0.
Time exfalso.
Time intuition eauto.
Time **
Time rewrite init_zero_lookup_ge_None //=.
Time Qed.
Time
Definition crash_fun :=
  fun s => {| mem_state := init_zero; disk_state := disk_state s |}.
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Read_Mem i => reads (get_mem i)
          | Write_Mem i v => puts (set_mem i v)
          | Read_Disk i => reads (get_disk i)
          | Write_Disk i v => puts (set_disk i v)
          | CAS i vold vnew => cas_rel i vold vnew
          | Fail => error
          end;
  crash_step := puts crash_fun;
  finish_step := puts crash_fun |}.
Time
Lemma crash_total_ok (s : State) :
  exists s', dynamics.(crash_step) s (Val s' tt).
Time Proof.
Time (eexists; econstructor).
Time Qed.
Time
Lemma crash_non_err_ok (s : State) ret :
  dynamics.(crash_step) s ret -> ret \226\137\160 Err.
Time Proof.
Time (inversion 1; congruence).
Time Qed.
Time
Definition l : Layer Op :=
  {|
  Layer.OpState := State;
  sem := dynamics;
  trace_proj := fun _ => nil;
  crash_preserves_trace := fun _ _ _ => eq_refl;
  crash_total := crash_total_ok;
  finish_total := crash_total_ok;
  crash_non_err := crash_non_err_ok;
  finish_non_err := crash_non_err_ok;
  initP := fun s => s = init_state |}.
Time End ExMach.
Time Definition read_mem i := Call (ExMach.Read_Mem i).
Time Definition write_mem i v := Call (ExMach.Write_Mem i v).
Time Definition read_disk i := Call (ExMach.Read_Disk i).
Time Definition write_disk i v := Call (ExMach.Write_Disk i v).
Time Definition cas i vold vnew := Call (ExMach.CAS i vold vnew).
Time
Definition assert (b : bool) :=
  if b then (_ <- Ret (); Ret ())%proc else Call ExMach.Fail.
Time
Definition lock i : proc ExMach.Op unit :=
  Loop
    (fun _ : unit =>
     x <- cas i 0 1;
     Ret (if nat_eq_dec x 0 then DoneWithOutcome tt else ContinueOutcome tt))%proc
    tt.
Time Definition unlock i : proc ExMach.Op unit := write_mem i 0.
