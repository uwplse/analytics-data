From RecoveryRefinement Require Import Lib.
Require Export Examples.Logging.TxnDiskAPI.
Require Export Examples.Logging.LogEncoding.
Require Export Examples.ReplicatedDisk.OneDiskAPI.
From Array Require Import Array.
Import ProcNotations.
#[local]Open Scope proc.
Axiom (LogHdr_fmt : block_encoder LogHdr).
Axiom (Descriptor_fmt : block_encoder Descriptor).
Definition read a := Call (D.op_read a).
Definition write a v := Call (D.op_write a v).
Definition size := Call D.op_size.
Definition gethdr : proc D.Op LogHdr :=
  b <- read 0; Ret (LogHdr_fmt.(decode) b).
Definition writehdr (hdr : LogHdr) := write 0 (LogHdr_fmt.(encode) hdr).
Definition hdr_full (hdr : LogHdr) :
  {hdr.(log_length) = LOG_LENGTH} + {hdr.(log_length) < LOG_LENGTH}.
(destruct (lt_dec hdr.(log_length) LOG_LENGTH)).
(right; auto).
(pose proof hdr.(log_length_ok)).
(left; omega).
Defined.
Definition hdr_inc (hdr : LogHdr) (pf : hdr.(log_length) < LOG_LENGTH) :
  LogHdr.
refine {| committed := hdr.(committed); log_length := hdr.(log_length) + 1 |}.
(abstract omega).
Defined.
Definition empty_hdr : LogHdr.
refine {| committed := false; log_length := 0 |}.
(abstract omega).
Defined.
Definition hdr_setcommit (hdr : LogHdr) : LogHdr :=
  {|
  committed := true;
  log_length := hdr.(log_length);
  log_length_ok := hdr.(log_length_ok) |}.
Definition getdesc : proc D.Op Descriptor :=
  b <- read 1; Ret (Descriptor_fmt.(decode) b).
Definition writedesc (ds : Descriptor) :=
  write 1 (Descriptor_fmt.(encode) ds).
Instance def_desc : (Default Descriptor).
refine {| addresses := List.repeat 0 LOG_LENGTH |}.
(apply repeat_length).
Defined.
Definition add_addr (ds : Descriptor) (idx : nat) (a : addr) : Descriptor.
refine {| addresses := assign ds.(addresses) idx a |}.
(rewrite length_assign).
(apply ds.(addresses_length)).
Defined.
Definition log_init :=
  sz <- size;
  (if lt_dec sz (2 + LOG_LENGTH)
   then Ret InitFailed
   else _ <- writehdr empty_hdr; _ <- writedesc default; Ret Initialized).
Definition log_size := sz <- size; Ret (sz - (2 + LOG_LENGTH)).
Definition set_desc desc (i : nat) a v :=
  _ <- writedesc (add_addr desc i a); write (2 + i) v.
Definition get_logwrite desc (i : nat) :=
  let a := sel desc.(addresses) i in v <- read (2 + i); Ret (a, v).
Definition data_read a := read (2 + LOG_LENGTH + a).
Definition data_write a v := write (2 + LOG_LENGTH + a) v.
Definition log_read a := data_read a.
Definition log_write a v :=
  hdr <- gethdr;
  match hdr_full hdr with
  | left _ => Ret TxnD.WriteErr
  | right pf =>
      desc <- getdesc;
      _ <- writehdr (hdr_inc hdr pf);
      _ <- set_desc desc hdr.(log_length) a v; Ret TxnD.WriteOK
  end.
Definition apply_at desc (i : nat) :=
  a_v <- get_logwrite desc i;
  (let '(a, v) := a_v in _ <- data_write a v; Ret tt).
Fixpoint apply_upto desc i len :=
  match len with
  | 0 => Ret tt
  | S len => _ <- apply_at desc i; apply_upto desc (i + 1) len
  end.
Definition log_apply :=
  hdr <- gethdr;
  _ <-
  if hdr.(committed)
  then desc <- getdesc; apply_upto desc 0 hdr.(log_length)
  else Ret tt; writehdr empty_hdr.
Definition commit :=
  hdr <- gethdr; _ <- writehdr (hdr_setcommit hdr); log_apply.
Definition recovery := log_apply.
