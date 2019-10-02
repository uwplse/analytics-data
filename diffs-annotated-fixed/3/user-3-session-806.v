Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlfHBdH"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqUyatWL"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqz7j1v9"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From RecordUpdate Require Import RecordSet.
From stdpp Require gmap.
From stdpp Require Import fin_maps.
From Armada Require Export Lib.
From Armada Require Import Spec.SemanticsHelpers
  Spec.LockDefs.
From Armada.Goose Require Import Machine Heap
  Examples.MailServer.
From Armada.Helpers Require Import RecordZoom.
From Transitions Require Import Relations.
Module Mail.
Section GoModel.
Context `{model_wf : GoModelWf}.
Implicit Type uid : uint64.
Inductive Op : Type -> Type :=
  | Open : Op unit
  | Pickup_Start :
      forall uid, Op (list (string * list byte))
  | Pickup_End :
      forall uid
        (msgs : list (string * list byte)),
      Op (slice.t Message.t)
  | Deliver_Start :
      forall uid (msg : slice.t byte), Op unit
  | Deliver_End :
      forall uid (msg : slice.t byte), Op unit
  | Delete : forall uid (msgID : string), Op unit
  | Lock : forall uid, Op unit
  | Unlock : forall uid, Op unit
  | DataOp : forall T (op : Data.Op T), Op T.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCuiSVZ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqqC8oI6"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Inductive MailboxStatus :=
  | MPickingUp : _
  | MLocked : _
  | MUnlocked : _.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqRB7qA0"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqO417MM"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition mailbox_lock_acquire (s : MailboxStatus) : 
  option MailboxStatus :=
  match s with
  | MPickingUp => None
  | MLocked => None
  | MUnlocked => Some MPickingUp
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqyp43Fd"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqkFDg69"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition mailbox_finish_pickup (s : MailboxStatus) :
  option MailboxStatus :=
  match s with
  | MPickingUp => Some MLocked
  | MLocked => None
  | MUnlocked => None
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTW9nvE"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq47Soeq"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition mailbox_lock_release (s : MailboxStatus) : 
  option MailboxStatus :=
  match s with
  | MPickingUp => None
  | MLocked => Some MUnlocked
  | MUnlocked => None
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqqPTVAg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBRYbLj"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Record State : Type :={heap : Data.State;
                       messages :
                        gmap.gmap uint64
                          (MailboxStatus * gmap.gmap string (list byte));
                       open : bool}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqUrB3T4"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqMGTYkg"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
#[global]
Instance etaState : (Settable _) :=
 settable! Build_State < heap; messages; open >.
Import RelationNotations.
Definition lookup K `{countable.Countable K} V
  (proj : State -> gmap.gmap K V) (k : K) : relation State State V :=
  readSome (fun s => s.(proj) !! k).
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
Definition createMessages (msgs : list (string * list byte)) :
  list Message.t :=
  map (\206\187 '(name, contents), Message.mk name (bytes_to_string contents)) msgs.
Section OpWrappers.
Definition pickup uid : proc Op (slice.t Message.t) :=
  (msgs <- Call (Pickup_Start uid); Call (Pickup_End uid msgs))%proc.
Definition deliver uid msg : proc Op unit :=
  (_ <- Call (Deliver_Start uid msg); Call (Deliver_End uid msg))%proc.
End OpWrappers.
Definition readSlice T (p : slice.t T) : relation State State (list T) :=
  let! (s, alloc) <-
  readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
  _ <- readSome (fun _ => lock_available Reader s);
  pure (list.take p.(slice.length) (list.drop p.(slice.offset) alloc)).
Definition readLockSlice T (p : slice.t T) : relation State State unit :=
  let! (s, alloc) <-
  readSome (fun s => Data.getAlloc p.(slice.ptr) s.(heap));
  s' <- readSome (fun _ => lock_acquire Reader s);
  _ <- readSome (fun _ => Data.getSliceModel p alloc);
  puts
    (set heap
       (set Data.allocs (updDyn (a:=Ptr.Heap T) p.(slice.ptr) (s', alloc)))).
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
Definition step_closed T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | Open =>
      _ <- puts (set open (\206\187 _, true));
      puts (set messages (\206\187 m, (\206\187 inbox, (MUnlocked, snd inbox)) <$> m))
  | _ => error
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqE2Av0W"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqLcjvOX"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
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
(* Auto-generated comment: Succeeded. *)

