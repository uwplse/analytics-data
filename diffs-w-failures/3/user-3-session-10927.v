Time From RecordUpdate Require Import RecordSet.
Time From Tactical Require Import ProofAutomation.
Time From Perennial Require Import Spec.Proc.
Time From Perennial Require Import Spec.InjectOp.
Time From Perennial Require Import Spec.SemanticsHelpers.
Time From Perennial Require Import Spec.LockDefs.
Time From Perennial.Goose Require Import Machine.
Time From Perennial.Goose Require Import GoZeroValues.
Time From Perennial.Goose Require Import Heap.
Time From Classes Require Import EqualDec.
Time From stdpp Require gmap.
Time From stdpp Require Import fin_maps.
Time From Transitions Require Import Relations.
Time Import EqualDecNotation.
Time Module FS.
Time Module path.
Time Record t := mk {dir : string; fname : string}.
Time End path.
Time Section GoModel.
Time Context `{model_wf : GoModelWf}.
Time Implicit Types (dir p : string) (fh : File) (bs : slice.t byte).
Time
Inductive Op : Type -> Type :=
  | Open : forall dir p, Op File
  | Close : forall fh, Op unit
  | List :
      forall dir (na : NonAtomicArgs unit), Op (retT na (slice.t string))
  | Size : forall fh, Op uint64
  | ReadAt : forall fh (off : uint64) (len : uint64), Op (slice.t byte)
  | Create : forall dir p, Op (File * bool)
  | Append : forall fh bs', Op unit
  | Delete : forall dir p, Op unit
  | Rename : forall dir1 p1 dir2 p2, Op unit
  | Truncate : forall dir p, Op unit
  | AtomicCreate : forall dir p bs, Op unit
  | Link : forall dir1 p1 dir2 p2, Op bool.
Time Section OpWrappers.
Time Context {Op'} {i : Injectable Op Op'}.
Time Notation proc := (proc Op').
Time
Notation "'Call!' op" := (Call (inject op) : proc _)
  (at level 0, op  at level 200).
Time Definition open dir p : proc _ := Call! Open dir p.
Time Definition close fh : proc _ := Call! Close fh.
Time
Definition list dir : proc (slice.t string) :=
  Bind (Call (inject (List dir Begin)))
    (fun _ => Call (inject (List dir (FinishArgs tt)))).
Time Definition list_start dir : proc unit := Call! List dir Begin.
Time Definition list_finish dir : proc _ := Call! List dir (FinishArgs tt).
Time Definition size fh : proc _ := Call! Size fh.
Time Definition readAt fh off len : proc _ := Call! ReadAt fh off len.
Time Definition create dir p : proc _ := Call! Create dir p.
Time Definition append fh bs : proc _ := Call! Append fh bs.
Time Definition delete dir p : proc _ := Call! Delete dir p.
Time
Definition rename dir1 p1 dir2 p2 : proc _ := Call! Rename dir1 p1 dir2 p2.
Time Definition truncate dir p : proc _ := Call! Truncate dir p.
Time
Definition atomicCreate dir p bs : proc _ := Call! AtomicCreate dir p bs.
Time Definition link dir1 p1 dir2 p2 := Call! Link dir1 p1 dir2 p2.
Time End OpWrappers.
Time Inductive OpenMode :=
       | Read : _
       | Write : _.
Time #[global]Instance path_eqdec : (EqDecision path.t).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance path_countable : (countable.Countable path.t).
Time Proof.
Time
(apply
  (countable.inj_countable' (fun '(path.mk dir fname) => (dir, fname))
     (fun '(dir, fname) => path.mk dir fname))).
Time (destruct x; simpl; auto).
Time Qed.
Time Definition Inode := nat.
Time
Record State :=
 mkState {heap : Data.State;
          dirlocks : gmap.gmap string (LockStatus * unit);
          dirents : gmap.gmap string (gmap.gmap string Inode);
          inodes : gmap.gmap Inode (List.list byte);
          fds : gmap.gmap File (Inode * OpenMode)}.
Time #[global]
Instance _eta : (Settable State) :=
 settable! mkState < heap; dirlocks; dirents; inodes; fds >.
Time Import RelationNotations.
Time
Definition lookup K `{countable.Countable K} V
  (proj : State -> gmap.gmap K V) (k : K) : relation State State V :=
  readSome (fun s => s.(proj) !! k).
Time
Definition resolvePath dir name : relation State State Inode :=
  let! ents <- lookup dirents dir; readSome (fun _ => ents !! name).
Time
Definition fresh_key K `{countable.Countable K} V
  (proj : State -> gmap.gmap K V) : relation State State K :=
  such_that (fun s v => s.(proj) !! v = None).
Time
Definition createSlice V (data : List.list V) :
  relation State State (slice.t V) :=
  r <- such_that
         (fun s (r : ptr _) =>
          Data.getAlloc r s.(heap) = None /\ r <> nullptr _);
  _ <- puts
         (set heap
            (set Data.allocs (updDyn (a:=Ptr.Heap V) r (Unlocked, data))));
  pure {| slice.ptr := r; slice.offset := 0; slice.length := length data |}.
Time
Definition readFd (fh : File) m : relation State State (List.list byte) :=
  let! (inode, m') <- lookup fds fh;
  if m == m' then lookup inodes inode else error.
Time
Definition assert S P (pf : {P} + {\194\172 P}) : relation S S unit :=
  if pf then pure tt else error.
Time
Definition unwrap S A (e : option A) : relation S S A :=
  match e with
  | Some v => pure v
  | None => error
  end.
Time
Definition is_none S A (e : option A) : relation S S unit :=
  match e with
  | Some _ => error
  | None => pure tt
  end.
Time Definition MAX_WRITE_LEN := 4096.
Time Definition MAX_WRITE_LEN_unfold : MAX_WRITE_LEN = 4096 := eq_refl.
Time Opaque MAX_WRITE_LEN.
Time
Definition step T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | Open dir name => inode <- resolvePath dir name; 
      fh <- fresh_key fds; _ <- puts (set fds <[fh:=(inode, Read)]>); 
      pure fh
  | Close fh => _ <- lookup fds fh; puts (set fds (map_delete fh))
  | List dir na => let! (s, _) <- lookup dirlocks dir;
      match na return (relation _ _ (retT na (slice.t string))) with
      | Begin => s' <- unwrap (lock_acquire Reader s);
          puts (set dirlocks <[dir:=(s', tt)]>)
      | FinishArgs _ => let! ents <- lookup dirents dir;
          s' <- unwrap (lock_release Reader s);
          _ <- puts (set dirlocks <[dir:=(s', tt)]>);
          l <- such_that
                 (\206\187 _ l,
                    Permutation.Permutation l (map fst (map_to_list ents)));
          createSlice l
      end
  | Size fh => bs <- readFd fh Read; pure (length bs)
  | ReadAt fh off len => bs <- readFd fh Read;
      let read_bs := list.take len (list.drop off bs) in createSlice read_bs
  | Create dir name => ents <- lookup dirents dir;
      match ents !! name with
      | Some _ => fh <- identity; pure (fh, false)
      | None => inode <- fresh_key inodes; fh <- fresh_key fds;
          _ <- puts (set dirents <[dir:=<[name:=inode]> ents]>);
          _ <- puts (set inodes <[inode:=nil]>);
          _ <- puts (set fds <[fh:=(inode, Write)]>); 
          pure (fh, true)
      end
  | Append fh p' => let! (inode, _) <- lookup fds fh; 
      bs <- readFd fh Write;
      let! (s, alloc) <- readSome
                           (fun st => Data.getAlloc p'.(slice.ptr) st.(heap));
      bs' <- unwrap (Data.getSliceModel p' alloc);
      _ <- assert (le_dec (length bs') MAX_WRITE_LEN);
      _ <- unwrap (lock_available Reader s);
      puts (set inodes <[inode:=bs ++ bs']>)
  | Delete dir name => let! (s, _) <- lookup dirlocks dir;
      _ <- unwrap (lock_available Writer s); ents <- lookup dirents dir;
      _ <- unwrap (ents !! name);
      puts (set dirents <[dir:=map_delete name ents]>)
  | Truncate dir name => error
  | AtomicCreate dir name p => error
  | Rename dir1 name1 dir2 name2 => ents1 <- lookup dirents dir1;
      inode1 <- unwrap (ents1 !! name1); ents2 <- lookup dirents dir2;
      _ <- is_none (ents2 !! name2);
      _ <- puts (set dirents <[dir1:=map_delete name1 ents1]>);
      _ <- puts (set dirents <[dir2:=<[name2:=inode1]> ents2]>); 
      pure tt
  | Link dir1 name1 dir2 name2 => ents1 <- lookup dirents dir1;
      inode1 <- unwrap (ents1 !! name1); ents2 <- lookup dirents dir2;
      match ents2 !! name2 with
      | Some _ => pure false
      | None => _ <- puts (set dirents <[dir2:=<[name2:=inode1]> ents2]>);
          pure true
      end
  end.
Time
Definition crash_step : relation State State unit :=
  _ <- puts (set fds (fun _ => \226\136\133)); _ <- puts (set heap (fun _ => \226\136\133));
  _ <- puts (set dirlocks (fmap (fun _ => (Unlocked, tt)))); 
  pure tt.
Time Theorem crash_step_non_err s res : crash_step s res -> res <> Err.
Time Proof.
Time (destruct res; eauto).
Time (unfold crash_step, puts, pure; simpl; intros).
Time
(repeat
  match goal with
  | H:_ \/ _ |- _ => destruct H
  | _ => progress propositional
  | _ => discriminate
  end).
Time Qed.
Time #[global]
Instance empty_fs : (Empty State) :=
 {| heap := \226\136\133; dirlocks := \226\136\133; dirents := \226\136\133; fds := \226\136\133; inodes := \226\136\133 |}.
Time End GoModel.
Time End FS.
