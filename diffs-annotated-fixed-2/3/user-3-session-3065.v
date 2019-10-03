Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqP5KcmG"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Armada.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap
  MailTriples.
From Armada.Goose.Examples Require Import MailServer.
From Armada.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From Armada Require AtomicPair.Helpers.
From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Armada.Goose Require Import ExplicitModel.
From Armada.Goose Require Import GoZeroValues.
Inductive compile_mail_base {gm : GoModel} :
forall {T}, proc Mail.Op T \226\134\146 proc GoLayer.Op T \226\134\146 Prop :=
  | cm_open : compile_mail_base (Call Mail.Open) MailServer.Open
  | cm_pickup :
      forall uid, compile_mail_base (Mail.pickup uid) (MailServer.Pickup uid)
  | cm_deliver :
      forall uid msg,
      compile_mail_base (Mail.deliver uid msg) (MailServer.Deliver uid msg)
  | cm_delete :
      forall uid msg,
      compile_mail_base (Call (Mail.Delete uid msg))
        (MailServer.Delete uid msg)
  | cm_lock :
      forall uid,
      compile_mail_base (Call (Mail.Lock uid)) (MailServer.Lock uid)
  | cm_unlock :
      forall uid,
      compile_mail_base (Call (Mail.Unlock uid)) (MailServer.Unlock uid)
  | cm_dataop :
      forall {T} (op : Data.Op T),
      compile_mail_base (Call (Mail.DataOp op)) (Call (DataOp op)).
Definition mail_impl {gm : GoModel} :=
  {|
  compile_rel_base := @compile_mail_base gm;
  recover_rel := rec_singleton MailServer.Recover |}.
Import Filesys.FS.
Import GoLayer.Go.
Import Mail.
Set Default Proof Using "Type".
Section refinement_recovery_defs.
Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Context {hGcontents : ghost_mapG contentsC \206\163}.
Context {hGinit : ghost_mapG ghost_init_statusC \206\163}.
Context {hGTmp : gen_heapG string Filesys.FS.Inode \206\163}.
Definition HeapInv_crash (\207\131 : Mail.State) : iProp \206\163 := True%I.
Definition InitInv_crash (\206\147 : gmap uint64 gname) \206\179 
  \207\131 :=
  (ghost_mapsto_auth \206\179 Uninit
   \226\136\151 ghost_mapsto \206\179 O Uninit
     \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), \226\136\131 \206\179uid,
                                         \226\140\156\206\147 !! uid = Some \206\179uid\226\140\157
                                         \226\136\151 InboxLockInv \206\179uid O))%I.
Definition MsgsInv_crash (\206\147 : gmap uint64 gname) (\206\179 : gname) 
  (\207\131 : Mail.State) : iProp \206\163 :=
  (\226\136\131 ls,
     GlobalInv ls false
     \226\136\151 RootDirInv \207\131
       \226\136\151 InitInv_crash \206\147 \206\179 \207\131
         \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm false))%I.
Lemma MsgsInv_crash_set_false \206\147 \206\179 \207\131 :
  MsgsInv_crash \206\147 \206\179 \207\131 -\226\136\151 MsgsInv \206\147 \206\179 (RecordSet.set open (\206\187 _, false) \207\131).
Proof.
iIntros "H".
iDestruct "H" as ( ls ) "(Hglobal&Hrootdir&Hinit&Hmsgs)".
iExists ls.
iFrame.
rewrite /InitInv_crash /InitInv.
iExists Uninit.
iDestruct "Hinit" as "($&$&$)".
eauto.
Qed.
#[global]
Instance MsgsInv_crash_timeless  \206\147 \206\179 \207\131: (Timeless (MsgsInv_crash \206\147 \206\179 \207\131)).
Proof.
(apply _).
Qed.
Definition TmpInv_crash \206\179tmp : iProp \206\163 :=
  (\226\136\131 tmps_map,
     SpoolDir \226\134\166 dom (gset string) tmps_map
     \226\136\151 ghost_mapsto_auth (A:=discreteC (gset string)) \206\179tmp
         (dom (gset _) tmps_map)
       \226\136\151 ([\226\136\151 map] name\226\134\166inode \226\136\136 tmps_map, path.mk SpoolDir name \226\134\166 inode))%I.
Definition CrashInv \206\179tmp :=
  (\226\136\131 \206\147 \206\179,
     source_ctx
     \226\136\151 inv execN
         (\226\136\131 \207\131,
            source_state \207\131
            \226\136\151 MsgsInv_crash \206\147 \206\179 \207\131 \226\136\151 HeapInv_crash \207\131 \226\136\151 TmpInv_crash \206\179tmp))%I.
Definition CrashStarter \206\179tmp :=
  (\226\136\131 tmps : gset string,
     ghost_mapsto (A:=discreteC (gset string)) \206\179tmp 0 tmps
     \226\136\151 SpoolDir \226\134\166 Unlocked)%I.
Definition CrashInner : iProp \206\163 :=
  (\226\136\131 \206\179tmp,
     (\226\136\131 \206\147 \206\179 \207\131,
        source_state \207\131
        \226\136\151 MsgsInv_crash \206\147 \206\179 \207\131 \226\136\151 HeapInv_crash \207\131 \226\136\151 TmpInv_crash \206\179tmp)
     \226\136\151 CrashStarter \206\179tmp)%I.
End refinement_recovery_defs.
Module mRT<: goose_refinement_type.
Definition init_base `{@GoModelWf gm} (s : GoLayer.Go.State) :=
  s.(fs).(FS.heap) = \226\136\133
  \226\136\167 (forall uid : uint64,
     (uid < 100 -> s.(fs).(dirents) !! UserDir uid = Some \226\136\133)
     \226\136\167 (uid >= 100 -> s.(fs).(dirents) !! UserDir uid = None))
    \226\136\167 s.(fs).(FS.dirents) !! SpoolDir = Some \226\136\133
      \226\136\167 (\226\136\128 d,
           is_Some (s.(fs).(FS.dirents) !! d)
           \226\134\146 d = SpoolDir \226\136\168 (\226\136\131 uid, d = UserDir uid))
        \226\136\167 dom (gset string) s.(fs).(FS.dirents) =
          dom (gset string) s.(fs).(FS.dirlocks)
          \226\136\167 (\226\136\128 dir l, s.(fs).(FS.dirlocks) !! dir = Some l \226\134\146 fst l = Unlocked)
            \226\136\167 s.(maillocks) = None.
Context {gm} {gmWf : GoModelWf gm}.
(* Auto-generated comment: Failed. *)

