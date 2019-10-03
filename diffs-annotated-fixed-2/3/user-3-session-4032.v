Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqpbWxQl"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Coq.Strings.String.
Require Import Prog ProgMonad.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirCache.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import SyncedMem.
Require Import GroupLog.
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Set Implicit Arguments.
Import DirTree.
Import ListNotations.
Module AFS.
Definition compute_xparams
  (data_bitmaps inode_bitmaps log_descr_blocks : addr) :=
  let data_blocks := data_bitmaps * valulen in
  let inode_blocks := inode_bitmaps * valulen / INODE.IRecSig.items_per_val
    in
  let inode_base := data_blocks in
  let balloc_base1 := inode_base + inode_blocks + inode_bitmaps in
  let balloc_base2 := balloc_base1 + data_bitmaps in
  let log_hdr := 1 + balloc_base2 + data_bitmaps in
  let log_descr := log_hdr + 1 in
  let log_data := log_descr + log_descr_blocks in
  let log_data_size := log_descr_blocks * PaddedLog.DescSig.items_per_val in
  let max_addr := log_data + log_data_size in
  Build_fs_xparams
    (Build_log_xparams 1 log_hdr log_descr log_descr_blocks log_data
       log_data_size) (Build_inode_xparams inode_base inode_blocks)
    (Build_balloc_xparams balloc_base1 data_bitmaps)
    (Build_balloc_xparams balloc_base2 data_bitmaps)
    (Build_balloc_xparams (inode_base + inode_blocks) inode_bitmaps) 1
    max_addr.
Lemma compute_xparams_ok :
  forall data_bitmaps inode_bitmaps log_descr_blocks magic,
  goodSize addrlen magic ->
  goodSize addrlen
    (1 + data_bitmaps * valulen +
     inode_bitmaps * valulen / INODE.IRecSig.items_per_val + inode_bitmaps +
     data_bitmaps + data_bitmaps + 1 + log_descr_blocks +
     log_descr_blocks * PaddedLog.DescSig.items_per_val) ->
  fs_xparams_ok
    (compute_xparams data_bitmaps inode_bitmaps log_descr_blocks magic).
Proof.
(unfold fs_xparams_ok).
(unfold log_xparams_ok, inode_xparams_ok, balloc_xparams_ok).
(unfold compute_xparams; simpl).
intuition.
all: (eapply goodSize_trans; try eassumption).
all: lia.
Qed.
Notation MSLL := BFILE.MSLL.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSICache := BFILE.MSICache.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSDBlocks := BFILE.MSDBlocks.
Import DIRTREE.
Anomaly "No printing rule found for "If _ _ else _"."
Please report at http://coq.inria.fr/bugs/.
Lemma S_minus_1_helper : forall n a b, S (n + 1 + a + b) - 1 - n = S (a + b).
Proof.
(intros; omega).
Qed.
Lemma S_minus_1_helper2 : forall n, S n - 1 = n.
Proof.
(intros; omega).
Qed.
Ltac
 equate_log_rep :=
  match goal with
  | r:BFILE.memstate,
    H:context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ],
    Hi:context [ IAlloc.Alloc.rep _ _ _ _ ?x_ ]
    |- LOG.rep ?xp ?F ?d ?ms _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ * _ =>
        equate d d';
         equate ms'
          (MSLL
             (BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r)
                (IAlloc.MSCache x_) (MSICache r) (MSCache r) 
                (MSDBlocks r)));
         equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
  | r:BFILE.memstate, H:context [ compute_xparams ?a1 ?a2 ?a3 ?a4 ]
    |- LOG.rep ?xp ?F ?d ?ms _ _ =p=> LOG.rep ?xp' ?F' ?d' ?ms' _ _ * _ =>
        equate d d';
         equate ms'
          (MSLL
             (BFILE.mk_memstate (MSAlloc r) ms (MSAllocC r)
                IAlloc.Alloc.freelist0 (MSICache r) 
                (MSCache r) (MSDBlocks r)));
         equate xp' (FSXPLog (compute_xparams a1 a2 a3 a4))
  end.
Theorem mkfs_ok :
  forall cachesize data_bitmaps inode_bitmaps log_descr_blocks,
  {!!<disk, PRE : vm, hm
  arrayS 0 disk *
  [[cachesize <> 0 /\ data_bitmaps <> 0 /\ inode_bitmaps <> 0]] *
  [[data_bitmaps <= valulen * valulen /\ inode_bitmaps <= valulen * valulen]] *
  [[length disk =
    1 + data_bitmaps * valulen +
    inode_bitmaps * valulen / INODE.IRecSig.items_per_val + inode_bitmaps +
    data_bitmaps + data_bitmaps + 1 + log_descr_blocks +
    log_descr_blocks * PaddedLog.DescSig.items_per_val]] *
  [[goodSize addrlen (length disk)]] POST : vm', hm'
  RET : r
  (exists ms fsxp d sm,
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) 
       (MSLL ms) sm hm' * [[vm' = vm]] *
     ([[isError r]] \/
      (exists ilist frees,
         [[r = OK (ms, fsxp)]] *
         [[[d
         ::: rep fsxp emp (TreeDir (FSXPRootInum fsxp) nil) ilist frees ms sm]]])))
  CRASH : hm' any >!!}
  mkfs cachesize data_bitmaps inode_bitmaps log_descr_blocks.
Proof.
(unfold mkfs).
safestep.
prestep.
(norml; unfold stars; simpl).
denote! (arrayS _ _ _) as Hx.
(eapply arrayN_isolate_hd in Hx).
(unfold ptsto_subset in Hx at 1).
safecancel.
(apply compute_xparams_ok).
(apply SB.goodSize_magic_number).
(denote (length disk = _) as Heq; rewrite Heq in *; auto).
auto.
prestep.
norm.
cancel.
intuition simpl.
pred_apply.
(erewrite arrayN_split  at 1).
(simpl).
(rewrite sep_star_comm).
(apply sep_star_assoc).
(rewrite skipn_length).
setoid_rewrite skipn_length.
substl length disk.
(apply S_minus_1_helper).
(rewrite firstn_length).
setoid_rewrite skipn_length.
substl length disk.
(rewrite Nat.min_l).
(rewrite Nat.sub_0_r; auto).
(rewrite S_minus_1_helper2).
(generalize
  (data_bitmaps * valulen +
   inode_bitmaps * valulen / INODE.IRecSig.items_per_val); 
  intros).
(generalize (log_descr_blocks * PaddedLog.DescSig.items_per_val); intros).
omega.
(eapply goodSize_trans; [  | eauto ]).
(rewrite skipn_length).
setoid_rewrite skipn_length.
substl length disk.
(generalize
  (data_bitmaps * valulen +
   inode_bitmaps * valulen / INODE.IRecSig.items_per_val); 
  intros).
(generalize (log_descr_blocks * PaddedLog.DescSig.items_per_val); intros).
omega.
auto.
auto.
step.
(rewrite Nat.sub_0_r in *).
step.
step.
step.
step.
step.
step.
step.
(rewrite latest_pushd).
equate_log_rep.
cancel.
or_r.
(unfold rep).
cancel.
denote (_ =p=> freeinode_pred) as Hy.
denote (freeinode_pred =p=> _) as Hz.
(rewrite <- Hy in Hz).
2: (apply repeat_length with (x := BFILE.bfile0)).
(assert
  (Hlen :
   1 <
   length
     (repeat BFILE.bfile0
        (inode_bitmaps * valulen / INODE.IRecSig.items_per_val *
         INODE.IRecSig.items_per_val)))).
(rewrite repeat_length; omega).
specialize (Hz _ (list2nmem_array _)).
(pred_apply; cancel).
(pose proof (list2nmem_ptsto_cancel BFILE.bfile0 _ Hlen)).
(unfold tree_dir_names_pred).
cancel.
(unfold BFILE.freepred in *).
subst.
(apply DirTreePred.SDIR.bfile0_empty).
(apply emp_empty_mem).
(eapply Forall_repeat).
eauto.
(apply pimpl_any).
step.
step.
step.
equate_log_rep.
cancel.
(or_l; cancel).
(apply pimpl_any).
step.
step.
equate_log_rep.
cancel.
(or_l; cancel).
(apply pimpl_any).
step.
equate_log_rep.
cancel.
(or_l; cancel).
all: (try (solve [ try xcrash; apply pimpl_any ])).
substl length disk.
(apply gt_Sn_O).
Unshelve.
all: (try easy).
(try exact ($ (0), nil)).
Qed.
Anomaly "No printing rule found for "If _ _ else _"."
Please report at http://coq.inria.fr/bugs/.
Definition file_get_attr fsxp inum ams :=
  t1 <- Rdtsc;
  ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
  let^(ams,attr) <- DIRTREE.getattr fsxp inum
                      (BFILE.mk_memstate (MSAlloc ams) ms 
                         (MSAllocC ams) (MSIAllocC ams) 
                         (MSICache ams) (MSCache ams) 
                         (MSDBlocks ams));
  ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
  r <- Ret
         ^( BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) 
              (MSIAllocC ams) (MSICache ams) (MSCache ams) 
              (MSDBlocks ams), attr);
  t2 <- Rdtsc;
  Debug "get_attr" (t2 - t1);; Ret r.
Definition file_get_sz fsxp inum ams :=
  t1 <- Rdtsc;
  let^(ams,attr) <- file_get_attr fsxp inum ams;
  t2 <- Rdtsc;
  Debug "file_get_sz" (t2 - t1);; Ret ^( ams, INODE.ABytes attr).
Anomaly "No printing rule found for "If _ _ else _"."
Please report at http://coq.inria.fr/bugs/.
Anomaly "No printing rule found for "If _ _ else _"."
Please report at http://coq.inria.fr/bugs/.
Definition read_fblock fsxp inum off ams :=
  t1 <- Rdtsc;
  ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
  let^(ams,b) <- DIRTREE.read fsxp inum off
                   (BFILE.mk_memstate (MSAlloc ams) ms 
                      (MSAllocC ams) (MSIAllocC ams) 
                      (MSICache ams) (MSCache ams) 
                      (MSDBlocks ams));
  ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
  r <- Ret
         ^( BFILE.mk_memstate (MSAlloc ams) ms (MSAllocC ams) 
              (MSIAllocC ams) (MSICache ams) (MSCache ams) 
              (MSDBlocks ams), b);
  t2 <- Rdtsc;
  Debug "read_fblock" (t2 - t1);; Ret r.
Anomaly "No printing rule found for "If _ _ else _"."
Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coquCxBy2"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqkkNjS0"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(* Auto-generated comment: Succeeded. *)

