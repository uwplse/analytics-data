Time From Armada.Goose Require Import base.
Time From Armada.Goose Require Import base.
Time Module partialFile.
Time Record t {model : GoModel} := mk {off : uint64; data : slice.t byte}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _)).
Time End partialFile.
Time
Definition GetUserDir {model : GoModel} (user : uint64) : 
  proc string := Ret ("user" ++ uint64_to_string user).
Time Definition SpoolDir : string := "spool".
Time Definition NumUsers : uint64 := 100.
Time
Definition readMessage {model : GoModel} (userDir : string) 
  (name : string) : proc string :=
  f <- FS.open userDir name;
  fileContents <- Data.newPtr (slice.t byte);
  initData <- Data.newSlice byte 0;
  _ <-
  Loop
    (fun pf =>
     buf <- FS.readAt f pf.(partialFile.off) 512;
     newData <- Data.sliceAppendSlice pf.(partialFile.data) buf;
     if compare_to (slice.length buf) 512 Lt
     then _ <- Data.writePtr fileContents newData; LoopRet tt
     else
      Continue
        {|
        partialFile.off := pf.(partialFile.off) + slice.length buf;
        partialFile.data := newData |})
    {| partialFile.off := 0; partialFile.data := initData |};
  fileData <- Data.readPtr fileContents;
  fileStr <- Data.bytesToString fileData; _ <- FS.close f; Ret fileStr.
Time Module importantStruct.
Time Record t {model : GoModel} := mk {}.
Time Arguments mk {model}.
Time #[global]Instance t_zero  {model : GoModel}: (HasGoZero t) := mk.
Time End importantStruct.
Time Definition doSubtleThings {model : GoModel} : proc unit := Ret tt.
Time Definition GlobalConstant : string := "foo".
Time Definition UntypedStringConstant : string := "bar".
Time Definition TypedInt : uint64 := 32.
Time Definition typedLiteral {model : GoModel} : proc uint64 := Ret 3.
Time
Definition literalCast {model : GoModel} : proc uint64 :=
  let x := 2 in Ret (x + 2).
Time
Definition castInt {model : GoModel} (p : slice.t byte) : 
  proc uint64 := Ret (slice.length p).
Time
Definition stringToByteSlice {model : GoModel} (s : string) :
  proc (slice.t byte) := p <- Data.stringToBytes s; Ret p.
Time
Definition byteSliceToString {model : GoModel} (p : slice.t byte) :
  proc string := s <- Data.bytesToString p; Ret s.
Time
Definition useSlice {model : GoModel} : proc unit :=
  s <- Data.newSlice byte 1;
  s1 <- Data.sliceAppendSlice s s; FS.atomicCreate "dir" "file" s1.
Time
Definition useSliceIndexing {model : GoModel} : proc uint64 :=
  s <- Data.newSlice uint64 2;
  _ <- Data.sliceWrite s 1 2; x <- Data.sliceRead s 0; Ret x.
Time
Definition useMap {model : GoModel} : proc unit :=
  m <- Data.newMap (slice.t byte);
  _ <- Data.mapAlter m 1 (fun _ => Some (slice.nil _));
  let! (x, ok) <- Data.mapGet m 2;
  if ok then Ret tt else Data.mapAlter m 3 (fun _ => Some x).
Time
Definition usePtr {model : GoModel} : proc unit :=
  p <- Data.newPtr uint64;
  _ <- Data.writePtr p 1; x <- Data.readPtr p; Data.writePtr p x.
Time
Definition iterMapKeysAndValues {model : GoModel} 
  (m : Map uint64) : proc uint64 :=
  sumPtr <- Data.newPtr uint64;
  _ <-
  Data.mapIter m
    (fun k v =>
     sum <- Data.readPtr sumPtr; Data.writePtr sumPtr (sum + k + v));
  sum <- Data.readPtr sumPtr; Ret sum.
Time
Definition iterMapKeys {model : GoModel} (m : Map uint64) :
  proc (slice.t uint64) :=
  keysSlice <- Data.newSlice uint64 0;
  keysRef <- Data.newPtr (slice.t uint64);
  _ <- Data.writePtr keysRef keysSlice;
  _ <-
  Data.mapIter m
    (fun k _ =>
     keys <- Data.readPtr keysRef;
     newKeys <- Data.sliceAppend keys k; Data.writePtr keysRef newKeys);
  keys <- Data.readPtr keysRef; Ret keys.
Time
Definition getRandom {model : GoModel} : proc uint64 :=
  r <- Data.randomUint64; Ret r.
Time Definition empty {model : GoModel} : proc unit := Ret tt.
Time Definition emptyReturn {model : GoModel} : proc unit := Ret tt.
Time Module allTheLiterals.
Time Record t {model : GoModel} := mk {int : uint64; s : string; b : bool}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _) (zeroValue _)).
Time End allTheLiterals.
Time
Definition normalLiterals {model : GoModel} : proc allTheLiterals.t :=
  Ret
    {|
    allTheLiterals.int := 0;
    allTheLiterals.s := "foo";
    allTheLiterals.b := true |}.
Time
Definition specialLiterals {model : GoModel} : proc allTheLiterals.t :=
  Ret
    {|
    allTheLiterals.int := 4096;
    allTheLiterals.s := "";
    allTheLiterals.b := false |}.
Time Module Message.
Time Record t {model : GoModel} := mk {Id : string; Contents : string}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _)).
Time End Message.
Time
Definition Pickup {model : GoModel} (user : uint64) :
  proc (slice.t Message.t) :=
  ls <- Globals.getX;
  l <- Data.sliceRead ls user;
  _ <- Data.lockAcquire l Writer;
  userDir <- GetUserDir user;
  names <- FS.list userDir;
  messages <- Data.newPtr (slice.t Message.t);
  initMessages <- Data.newSlice Message.t 0;
  _ <- Data.writePtr messages initMessages;
  _ <-
  Loop
    (fun i =>
     if i == slice.length names
     then LoopRet tt
     else
      name <- Data.sliceRead names i;
      msg <- readMessage userDir name;
      oldMessages <- Data.readPtr messages;
      newMessages <-
      Data.sliceAppend oldMessages
        {| Message.Id := name; Message.Contents := msg |};
      _ <- Data.writePtr messages newMessages; Continue (i + 1)) 0;
  msgs <- Data.readPtr messages; Ret msgs.
Time
Definition createTmp {model : GoModel} : proc (File * string) :=
  initID <- Data.randomUint64;
  finalFile <- Data.newPtr File;
  finalName <- Data.newPtr string;
  _ <-
  Loop
    (fun id =>
     let fname := uint64_to_string id in
     let! (f, ok) <- FS.create SpoolDir fname;
     if ok
     then
      _ <- Data.writePtr finalFile f;
      _ <- Data.writePtr finalName fname; LoopRet tt
     else newID <- Data.randomUint64; Continue newID) initID;
  f <- Data.readPtr finalFile; name <- Data.readPtr finalName; Ret (f, name).
Time
Definition writeTmp {model : GoModel} (data : slice.t byte) : 
  proc string :=
  let! (f, name) <- createTmp;
  _ <-
  Loop
    (fun buf =>
     if compare_to (slice.length buf) 4096 Lt
     then _ <- FS.append f buf; LoopRet tt
     else
      _ <- FS.append f (slice.take 4096 buf); Continue (slice.skip 4096 buf))
    data; _ <- FS.close f; Ret name.
Time
Definition oddLiterals {model : GoModel} : proc allTheLiterals.t :=
  Ret
    {|
    allTheLiterals.int := 5;
    allTheLiterals.s := "backquote string";
    allTheLiterals.b := false |}.
Time
Definition DoSomething {model : GoModel} (s : string) : proc unit := Ret tt.
Time
Definition conditionalInLoop {model : GoModel} : proc unit :=
  Loop
    (fun i =>
     _ <-
     (if compare_to i 3 Lt
      then _ <- DoSomething "i is small"; Ret tt
      else Ret tt);
     if compare_to i 5 Gt then LoopRet tt else Continue (i + 1)) 0.
Time
Definition returnTwo {model : GoModel} (p : slice.t byte) :
  proc (uint64 * uint64) := Ret (0, 0).
Time
Definition returnTwoWrapper {model : GoModel} (data : slice.t byte) :
  proc (uint64 * uint64) := let! (a, b) <- returnTwo data; Ret (a, b).
Time Module Block.
Time Record t {model : GoModel} := mk {Value : uint64}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) := (mk (zeroValue _)).
Time End Block.
Time Definition Disk1 : uint64 := 0.
Time Definition Disk2 : uint64 := 0.
Time Definition DiskSize : uint64 := 1000.
Time
Definition TwoDiskWrite {model : GoModel} (diskId : uint64) 
  (a : uint64) (v : Block.t) : proc bool := Ret true.
Time
Definition TwoDiskRead {model : GoModel} (diskId : uint64) 
  (a : uint64) : proc (Block.t * bool) := Ret ({| Block.Value := 0 |}, true).
Time
Definition TwoDiskLock {model : GoModel} (a : uint64) : proc unit := Ret tt.
Time
Definition TwoDiskUnlock {model : GoModel} (a : uint64) : proc unit := Ret tt.
Time
Definition ReplicatedDiskRead {model : GoModel} (a : uint64) :
  proc Block.t :=
  _ <- TwoDiskLock a;
  let! (v, ok) <- TwoDiskRead Disk1 a;
  if ok
  then _ <- TwoDiskUnlock a; Ret v
  else let! (v2, _) <- TwoDiskRead Disk2 a; _ <- TwoDiskUnlock a; Ret v2.
Time
Definition ReplicatedDiskWrite {model : GoModel} (a : uint64) 
  (v : Block.t) : proc unit :=
  _ <- TwoDiskLock a;
  _ <- TwoDiskWrite Disk1 a v; _ <- TwoDiskWrite Disk2 a v; TwoDiskUnlock a.
Time
Definition ReplicatedDiskRecover {model : GoModel} : 
  proc unit :=
  Loop
    (fun a =>
     if compare_to a DiskSize Gt
     then LoopRet tt
     else
      let! (v, ok) <- TwoDiskRead Disk1 a;
      _ <- (if ok then _ <- TwoDiskWrite Disk2 a v; Ret tt else Ret tt);
      Continue (a + 1)) 0.
Time Definition Skip {model : GoModel} : proc unit := Ret tt.
Time
Definition simpleSpawn {model : GoModel} : proc unit :=
  l <- Data.newLock;
  v <- Data.newPtr uint64;
  _ <-
  Spawn
    (_ <- Data.lockAcquire l Reader;
     x <- Data.readPtr v;
     _ <- (if compare_to x 0 Gt then _ <- Skip; Ret tt else Ret tt);
     Data.lockRelease l Reader);
  _ <- Data.lockAcquire l Writer;
  _ <- Data.writePtr v 1; Data.lockRelease l Writer.
Time
Definition threadCode {model : GoModel} (tid : uint64) : proc unit := Ret tt.
Time
Definition loopSpawn {model : GoModel} : proc unit :=
  _ <-
  Loop
    (fun i =>
     if compare_to i 10 Gt
     then LoopRet tt
     else _ <- Spawn (threadCode i); Continue (i + 1)) 0;
  Loop (fun dummy => Continue (negb dummy)) true.
Time
Definition stringAppend {model : GoModel} (s : string) 
  (x : uint64) : proc string :=
  Ret ("prefix " ++ s ++ " " ++ uint64_to_string x).
Time
Definition DoSomeLocking {model : GoModel} (l : LockRef) : 
  proc unit :=
  _ <- Data.lockAcquire l Writer;
  _ <- Data.lockRelease l Writer;
  _ <- Data.lockAcquire l Reader;
  _ <- Data.lockAcquire l Reader;
  _ <- Data.lockRelease l Reader; Data.lockRelease l Reader.
Time
Definition makeLock {model : GoModel} : proc unit :=
  l <- Data.newLock; DoSomeLocking l.
Time
Definition Deliver {model : GoModel} (user : uint64) 
  (msg : slice.t byte) : proc unit :=
  userDir <- GetUserDir user;
  tmpName <- writeTmp msg;
  initID <- Data.randomUint64;
  _ <-
  Loop
    (fun id =>
     ok <- FS.link SpoolDir tmpName userDir ("msg" ++ uint64_to_string id);
     if ok then LoopRet tt else newID <- Data.randomUint64; Continue newID)
    initID; FS.delete SpoolDir tmpName.
Time
Definition Delete {model : GoModel} (user : uint64) 
  (msgID : string) : proc unit :=
  userDir <- GetUserDir user; FS.delete userDir msgID.
Time
Definition Lock {model : GoModel} (user : uint64) : 
  proc unit :=
  locks <- Globals.getX;
  l <- Data.sliceRead locks user; Data.lockAcquire l Writer.
Time
Definition Unlock {model : GoModel} (user : uint64) : 
  proc unit :=
  locks <- Globals.getX;
  l <- Data.sliceRead locks user; Data.lockRelease l Writer.
Time
Definition Open {model : GoModel} : proc unit :=
  locks <- Data.newPtr (slice.t LockRef);
  initLocks <- Data.newSlice LockRef 0;
  _ <- Data.writePtr locks initLocks;
  _ <-
  Loop
    (fun i =>
     if i == NumUsers
     then LoopRet tt
     else
      oldLocks <- Data.readPtr locks;
      l <- Data.newLock;
      newLocks <- Data.sliceAppend oldLocks l;
      _ <- Data.writePtr locks newLocks; Continue (i + 1)) 0;
  finalLocks <- Data.readPtr locks; Globals.setX finalLocks.
Time
Definition Recover {model : GoModel} : proc unit :=
  spooled <- FS.list SpoolDir;
  Loop
    (fun i =>
     if i == slice.length spooled
     then LoopRet tt
     else
      name <- Data.sliceRead spooled i;
      _ <- FS.delete SpoolDir name; Continue (i + 1)) 0.
