Time From Perennial.Goose Require Import base.
Time Module Table.
Time Record t {model : GoModel} := mk {Index : Map uint64; File : File}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _)).
Time End Table.
Time
Definition CreateTable {model : GoModel} (p : string) : 
  proc Table.t :=
  index <- Data.newMap uint64;
  let! (f, _) <- FS.create "db" p;
  _ <- FS.close f;
  f2 <- FS.open "db" p; Ret {| Table.Index := index; Table.File := f2 |}.
Time Module Entry.
Time Record t {model : GoModel} := mk {Key : uint64; Value : slice.t byte}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _)).
Time End Entry.
Time
Definition DecodeUInt64 {model : GoModel} (p : slice.t byte) :
  proc (uint64 * uint64) :=
  if compare_to (slice.length p) 8 Lt
  then Ret (0, 0)
  else n <- Data.uint64Get p; Ret (n, 8).
Time
Definition DecodeEntry {model : GoModel} (data : slice.t byte) :
  proc (Entry.t * uint64) :=
  let! (key, l1) <- DecodeUInt64 data;
  if l1 == 0
  then Ret ({| Entry.Key := 0; Entry.Value := slice.nil _ |}, 0)
  else
   let! (valueLen, l2) <- DecodeUInt64 (slice.skip l1 data);
   if l2 == 0
   then Ret ({| Entry.Key := 0; Entry.Value := slice.nil _ |}, 0)
   else
    if compare_to (slice.length data) (l1 + l2 + valueLen) Lt
    then Ret ({| Entry.Key := 0; Entry.Value := slice.nil _ |}, 0)
    else
     let value := slice.subslice (l1 + l2) (l1 + l2 + valueLen) data in
     Ret ({| Entry.Key := key; Entry.Value := value |}, l1 + l2 + valueLen).
Time Module lazyFileBuf.
Time Record t {model : GoModel} := mk {offset : uint64; next : slice.t byte}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _)).
Time End lazyFileBuf.
Time
Definition readTableIndex {model : GoModel} (f : File) 
  (index : Map uint64) : proc unit :=
  Loop
    (fun buf =>
     let! (e, l) <- DecodeEntry buf.(lazyFileBuf.next);
     if compare_to l 0 Gt
     then
      _ <-
      Data.mapAlter index e.(Entry.Key)
        (fun _ => Some (8 + buf.(lazyFileBuf.offset)));
      Continue
        {|
        lazyFileBuf.offset := buf.(lazyFileBuf.offset) + l;
        lazyFileBuf.next := slice.skip l buf.(lazyFileBuf.next) |}
     else
      p <-
      FS.readAt f
        (buf.(lazyFileBuf.offset) + slice.length buf.(lazyFileBuf.next)) 4096;
      if slice.length p == 0
      then LoopRet tt
      else
       newBuf <- Data.sliceAppendSlice buf.(lazyFileBuf.next) p;
       Continue
         {|
         lazyFileBuf.offset := buf.(lazyFileBuf.offset);
         lazyFileBuf.next := newBuf |})
    {| lazyFileBuf.offset := 0; lazyFileBuf.next := slice.nil _ |}.
Time
Definition RecoverTable {model : GoModel} (p : string) : 
  proc Table.t :=
  index <- Data.newMap uint64;
  f <- FS.open "db" p;
  _ <- readTableIndex f index;
  Ret {| Table.Index := index; Table.File := f |}.
Time
Definition CloseTable {model : GoModel} (t : Table.t) : 
  proc unit := FS.close t.(Table.File).
Time
Definition readValue {model : GoModel} (f : File) 
  (off : uint64) : proc (slice.t byte) :=
  startBuf <- FS.readAt f off 512;
  totalBytes <- Data.uint64Get startBuf;
  let buf := slice.skip 8 startBuf in
  let haveBytes := slice.length buf in
  if compare_to haveBytes totalBytes Lt
  then
   buf2 <- FS.readAt f (off + 512) (totalBytes - haveBytes);
   newBuf <- Data.sliceAppendSlice buf buf2; Ret newBuf
  else Ret (slice.take totalBytes buf).
Time
Definition tableRead {model : GoModel} (t : Table.t) 
  (k : uint64) : proc (slice.t byte * bool) :=
  let! (off, ok) <- Data.mapGet t.(Table.Index) k;
  if negb ok
  then Ret (slice.nil _, false)
  else p <- readValue t.(Table.File) off; Ret (p, true).
Time Module bufFile.
Time
Record t {model : GoModel} := mk {file : File; buf : ptr (slice.t byte)}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _)).
Time End bufFile.
Time
Definition newBuf {model : GoModel} (f : File) : proc bufFile.t :=
  buf <- Data.newPtr (slice.t byte);
  Ret {| bufFile.file := f; bufFile.buf := buf |}.
Time
Definition bufFlush {model : GoModel} (f : bufFile.t) : 
  proc unit :=
  buf <- Data.readPtr f.(bufFile.buf);
  if slice.length buf == 0
  then Ret tt
  else
   _ <- FS.append f.(bufFile.file) buf;
   Data.writePtr f.(bufFile.buf) (slice.nil _).
Time
Definition bufAppend {model : GoModel} (f : bufFile.t) 
  (p : slice.t byte) : proc unit :=
  buf <- Data.readPtr f.(bufFile.buf);
  buf2 <- Data.sliceAppendSlice buf p; Data.writePtr f.(bufFile.buf) buf2.
Time
Definition bufClose {model : GoModel} (f : bufFile.t) : 
  proc unit := _ <- bufFlush f; FS.close f.(bufFile.file).
Time Module tableWriter.
Time
Record t {model : GoModel} :=
 mk {index : Map uint64;
     name : string;
     file : bufFile.t;
     offset : ptr uint64}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _) (zeroValue _) (zeroValue _)).
Time End tableWriter.
Time
Definition newTableWriter {model : GoModel} (p : string) :
  proc tableWriter.t :=
  index <- Data.newMap uint64;
  let! (f, _) <- FS.create "db" p;
  buf <- newBuf f;
  off <- Data.newPtr uint64;
  Ret
    {|
    tableWriter.index := index;
    tableWriter.name := p;
    tableWriter.file := buf;
    tableWriter.offset := off |}.
Time
Definition tableWriterAppend {model : GoModel} (w : tableWriter.t)
  (p : slice.t byte) : proc unit :=
  _ <- bufAppend w.(tableWriter.file) p;
  off <- Data.readPtr w.(tableWriter.offset);
  Data.writePtr w.(tableWriter.offset) (off + slice.length p).
Time
Definition tableWriterClose {model : GoModel} (w : tableWriter.t) :
  proc Table.t :=
  _ <- bufClose w.(tableWriter.file);
  f <- FS.open "db" w.(tableWriter.name);
  Ret {| Table.Index := w.(tableWriter.index); Table.File := f |}.
Time
Definition EncodeUInt64 {model : GoModel} (x : uint64) 
  (p : slice.t byte) : proc (slice.t byte) :=
  tmp <- Data.newSlice byte 8;
  _ <- Data.uint64Put tmp x; p2 <- Data.sliceAppendSlice p tmp; Ret p2.
Time
Definition EncodeSlice {model : GoModel} (data : slice.t byte)
  (p : slice.t byte) : proc (slice.t byte) :=
  p2 <- EncodeUInt64 (slice.length data) p;
  p3 <- Data.sliceAppendSlice p2 data; Ret p3.
Time
Definition tablePut {model : GoModel} (w : tableWriter.t) 
  (k : uint64) (v : slice.t byte) : proc unit :=
  tmp <- Data.newSlice byte 0;
  tmp2 <- EncodeUInt64 k tmp;
  tmp3 <- EncodeSlice v tmp2;
  off <- Data.readPtr w.(tableWriter.offset);
  _ <-
  Data.mapAlter w.(tableWriter.index) k
    (fun _ => Some (off + slice.length tmp2)); tableWriterAppend w tmp3.
Time Module Database.
Time
Record t {model : GoModel} :=
 mk {wbuffer : ptr (Map (slice.t byte));
     rbuffer : ptr (Map (slice.t byte));
     bufferL : LockRef;
     table : ptr Table.t;
     tableName : ptr string;
     tableL : LockRef;
     compactionL : LockRef}.
Time Arguments mk {model}.
Time #[global]
Instance t_zero  {model : GoModel}: (HasGoZero t) :=
 (mk (zeroValue _) (zeroValue _) (zeroValue _) (zeroValue _) 
    (zeroValue _) (zeroValue _) (zeroValue _)).
Time End Database.
Time
Definition makeValueBuffer {model : GoModel} :
  proc (ptr (Map (slice.t byte))) :=
  buf <- Data.newMap (slice.t byte);
  bufPtr <- Data.newPtr (Map (slice.t byte));
  _ <- Data.writePtr bufPtr buf; Ret bufPtr.
Time
Definition NewDb {model : GoModel} : proc Database.t :=
  wbuf <- makeValueBuffer;
  rbuf <- makeValueBuffer;
  bufferL <- Data.newLock;
  let tableName := "table.0" in
  tableNameRef <- Data.newPtr string;
  _ <- Data.writePtr tableNameRef tableName;
  table <- CreateTable tableName;
  tableRef <- Data.newPtr Table.t;
  _ <- Data.writePtr tableRef table;
  tableL <- Data.newLock;
  compactionL <- Data.newLock;
  Ret
    {|
    Database.wbuffer := wbuf;
    Database.rbuffer := rbuf;
    Database.bufferL := bufferL;
    Database.table := tableRef;
    Database.tableName := tableNameRef;
    Database.tableL := tableL;
    Database.compactionL := compactionL |}.
Time
Definition Read {model : GoModel} (db : Database.t) 
  (k : uint64) : proc (slice.t byte * bool) :=
  _ <- Data.lockAcquire db.(Database.bufferL) Reader;
  buf <- Data.readPtr db.(Database.wbuffer);
  let! (v, ok) <- Data.mapGet buf k;
  if ok
  then _ <- Data.lockRelease db.(Database.bufferL) Reader; Ret (v, true)
  else
   rbuf <- Data.readPtr db.(Database.rbuffer);
   let! (v2, ok) <- Data.mapGet rbuf k;
   if ok
   then _ <- Data.lockRelease db.(Database.bufferL) Reader; Ret (v2, true)
   else
    _ <- Data.lockAcquire db.(Database.tableL) Reader;
    tbl <- Data.readPtr db.(Database.table);
    let! (v3, ok) <- tableRead tbl k;
    _ <- Data.lockRelease db.(Database.tableL) Reader;
    _ <- Data.lockRelease db.(Database.bufferL) Reader; Ret (v3, ok).
Time
Definition Write {model : GoModel} (db : Database.t) 
  (k : uint64) (v : slice.t byte) : proc unit :=
  _ <- Data.lockAcquire db.(Database.bufferL) Writer;
  buf <- Data.readPtr db.(Database.wbuffer);
  _ <- Data.mapAlter buf k (fun _ => Some v);
  Data.lockRelease db.(Database.bufferL) Writer.
Time
Definition freshTable {model : GoModel} (p : string) : 
  proc string :=
  if p == "table.0"
  then Ret "table.1"
  else if p == "table.1" then Ret "table.0" else Ret p.
Time
Definition tablePutBuffer {model : GoModel} (w : tableWriter.t)
  (buf : Map (slice.t byte)) : proc unit :=
  Data.mapIter buf (fun k v => tablePut w k v).
Time
Definition tablePutOldTable {model : GoModel} (w : tableWriter.t)
  (t : Table.t) (b : Map (slice.t byte)) : proc unit :=
  Loop
    (fun buf =>
     let! (e, l) <- DecodeEntry buf.(lazyFileBuf.next);
     if compare_to l 0 Gt
     then
      let! (_, ok) <- Data.mapGet b e.(Entry.Key);
      _ <-
      (if negb ok
       then _ <- tablePut w e.(Entry.Key) e.(Entry.Value); Ret tt
       else Ret tt);
      Continue
        {|
        lazyFileBuf.offset := buf.(lazyFileBuf.offset) + l;
        lazyFileBuf.next := slice.skip l buf.(lazyFileBuf.next) |}
     else
      p <-
      FS.readAt t.(Table.File)
        (buf.(lazyFileBuf.offset) + slice.length buf.(lazyFileBuf.next)) 4096;
      if slice.length p == 0
      then LoopRet tt
      else
       newBuf <- Data.sliceAppendSlice buf.(lazyFileBuf.next) p;
       Continue
         {|
         lazyFileBuf.offset := buf.(lazyFileBuf.offset);
         lazyFileBuf.next := newBuf |})
    {| lazyFileBuf.offset := 0; lazyFileBuf.next := slice.nil _ |}.
Time
Definition constructNewTable {model : GoModel} (db : Database.t)
  (wbuf : Map (slice.t byte)) : proc (Table.t * Table.t) :=
  oldName <- Data.readPtr db.(Database.tableName);
  name <- freshTable oldName;
  w <- newTableWriter name;
  oldTable <- Data.readPtr db.(Database.table);
  _ <- tablePutOldTable w oldTable wbuf;
  _ <- tablePutBuffer w wbuf;
  newTable <- tableWriterClose w; Ret (oldTable, newTable).
Time
Definition Compact {model : GoModel} (db : Database.t) : 
  proc unit :=
  _ <- Data.lockAcquire db.(Database.compactionL) Writer;
  _ <- Data.lockAcquire db.(Database.bufferL) Writer;
  buf <- Data.readPtr db.(Database.wbuffer);
  emptyWbuffer <- Data.newMap (slice.t byte);
  _ <- Data.writePtr db.(Database.wbuffer) emptyWbuffer;
  _ <- Data.writePtr db.(Database.rbuffer) buf;
  _ <- Data.lockRelease db.(Database.bufferL) Writer;
  _ <- Data.lockAcquire db.(Database.tableL) Reader;
  oldTableName <- Data.readPtr db.(Database.tableName);
  let! (oldTable, t) <- constructNewTable db buf;
  newTable <- freshTable oldTableName;
  _ <- Data.lockRelease db.(Database.tableL) Reader;
  _ <- Data.lockAcquire db.(Database.tableL) Writer;
  _ <- Data.writePtr db.(Database.table) t;
  _ <- Data.writePtr db.(Database.tableName) newTable;
  manifestData <- Data.stringToBytes newTable;
  _ <- FS.atomicCreate "db" "manifest" manifestData;
  _ <- CloseTable oldTable;
  _ <- FS.delete "db" oldTableName;
  _ <- Data.lockRelease db.(Database.tableL) Writer;
  Data.lockRelease db.(Database.compactionL) Writer.
Time
Definition recoverManifest {model : GoModel} : proc string :=
  f <- FS.open "db" "manifest";
  manifestData <- FS.readAt f 0 4096;
  tableName <- Data.bytesToString manifestData;
  _ <- FS.close f; Ret tableName.
Time
Definition deleteOtherFile {model : GoModel} (name : string)
  (tableName : string) : proc unit :=
  if name == tableName
  then Ret tt
  else if name == "manifest" then Ret tt else FS.delete "db" name.
Time
Definition deleteOtherFiles {model : GoModel} (tableName : string) :
  proc unit :=
  files <- FS.list "db";
  let nfiles := slice.length files in
  Loop
    (fun i =>
     if i == nfiles
     then LoopRet tt
     else
      name <- Data.sliceRead files i;
      _ <- deleteOtherFile name tableName; Continue (i + 1)) 0.
Time
Definition Recover {model : GoModel} : proc Database.t :=
  tableName <- recoverManifest;
  table <- RecoverTable tableName;
  tableRef <- Data.newPtr Table.t;
  _ <- Data.writePtr tableRef table;
  tableNameRef <- Data.newPtr string;
  _ <- Data.writePtr tableNameRef tableName;
  _ <- deleteOtherFiles tableName;
  wbuffer <- makeValueBuffer;
  rbuffer <- makeValueBuffer;
  bufferL <- Data.newLock;
  tableL <- Data.newLock;
  compactionL <- Data.newLock;
  Ret
    {|
    Database.wbuffer := wbuffer;
    Database.rbuffer := rbuffer;
    Database.bufferL := bufferL;
    Database.table := tableRef;
    Database.tableName := tableNameRef;
    Database.tableL := tableL;
    Database.compactionL := compactionL |}.
Time
Definition Shutdown {model : GoModel} (db : Database.t) : 
  proc unit :=
  _ <- Data.lockAcquire db.(Database.bufferL) Writer;
  _ <- Data.lockAcquire db.(Database.compactionL) Writer;
  t <- Data.readPtr db.(Database.table);
  _ <- CloseTable t;
  _ <- Data.lockRelease db.(Database.compactionL) Writer;
  Data.lockRelease db.(Database.bufferL) Writer.
Time
Definition Close {model : GoModel} (db : Database.t) : 
  proc unit := _ <- Compact db; Shutdown db.
