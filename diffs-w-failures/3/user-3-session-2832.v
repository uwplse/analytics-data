Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time
From Armada.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap
  MailTriples.
Time From Armada.Goose.Examples Require Import MailServer.
Time From Armada.Goose.Proof Require Import Interp.
Time Require Import Goose.Proof.RefinementAdequacy.
Time From Armada Require AtomicPair.Helpers.
Time From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Armada.Goose Require Import ExplicitModel.
Time From Armada.Goose Require Import GoZeroValues.
Time
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
Time
Definition mail_impl {gm : GoModel} :=
  {|
  compile_rel_base := @compile_mail_base gm;
  recover_rel := rec_singleton MailServer.Recover |}.
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time Import Mail.
Time Set Default Proof Using "Type".
Time Section refinement_recovery_defs.
Time Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Time Context {hGcontents : ghost_mapG contentsC \206\163}.
Time Context {hGinit : ghost_mapG ghost_init_statusC \206\163}.
Time Context {hGTmp : gen_heapG string Filesys.FS.Inode \206\163}.
Time Definition HeapInv_crash (\207\131 : Mail.State) : iProp \206\163 := True%I.
Time
Definition InitInv_crash (\206\147 : gmap uint64 gname) \206\179 
  \207\131 :=
  (ghost_mapsto_auth \206\179 Uninit
   \226\136\151 ghost_mapsto \206\179 O Uninit
     \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), \226\136\131 \206\179uid,
                                         \226\140\156\206\147 !! uid = Some \206\179uid\226\140\157
                                         \226\136\151 InboxLockInv \206\179uid O))%I.
Time
Definition MsgsInv_crash (\206\147 : gmap uint64 gname) (\206\179 : gname) 
  (\207\131 : Mail.State) : iProp \206\163 :=
  (\226\136\131 ls,
     GlobalInv ls false
     \226\136\151 RootDirInv \207\131
       \226\136\151 InitInv_crash \206\147 \206\179 \207\131
         \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm false))%I.
Time
Lemma MsgsInv_crash_set_false \206\147 \206\179 \207\131 :
  MsgsInv_crash \206\147 \206\179 \207\131 -\226\136\151 MsgsInv \206\147 \206\179 (RecordSet.set open (\206\187 _, false) \207\131).
Time Proof.
Time iIntros "H".
Time iDestruct "H" as ( ls ) "(Hglobal&Hrootdir&Hinit&Hmsgs)".
Time iExists ls.
Time iFrame.
Time rewrite /InitInv_crash /InitInv.
Time iExists Uninit.
Time iDestruct "Hinit" as "($&$&$)".
Time eauto.
Time Qed.
Time #[global]
Instance MsgsInv_crash_timeless  \206\147 \206\179 \207\131: (Timeless (MsgsInv_crash \206\147 \206\179 \207\131)).
Time Proof.
Time (apply _).
Time Qed.
Time
Definition TmpInv_crash \206\179tmp : iProp \206\163 :=
  (\226\136\131 tmps_map,
     SpoolDir \226\134\166 dom (gset string) tmps_map
     \226\136\151 ghost_mapsto_auth (A:=discreteC (gset string)) \206\179tmp
         (dom (gset _) tmps_map)
       \226\136\151 ([\226\136\151 map] name\226\134\166inode \226\136\136 tmps_map, path.mk SpoolDir name \226\134\166 inode))%I.
Time
Definition CrashInv \206\179tmp :=
  (\226\136\131 \206\147 \206\179,
     source_ctx
     \226\136\151 inv execN
         (\226\136\131 \207\131,
            source_state \207\131
            \226\136\151 MsgsInv_crash \206\147 \206\179 \207\131 \226\136\151 HeapInv_crash \207\131 \226\136\151 TmpInv_crash \206\179tmp))%I.
Time
Definition CrashStarter \206\179tmp :=
  (\226\136\131 tmps : gset string,
     ghost_mapsto (A:=discreteC (gset string)) \206\179tmp 0 tmps
     \226\136\151 SpoolDir \226\134\166 Unlocked)%I.
Time
Definition CrashInner : iProp \206\163 :=
  (\226\136\131 \206\179tmp,
     (\226\136\131 \206\147 \206\179 \207\131,
        source_state \207\131
        \226\136\151 MsgsInv_crash \206\147 \206\179 \207\131 \226\136\151 HeapInv_crash \207\131 \226\136\151 TmpInv_crash \206\179tmp)
     \226\136\151 CrashStarter \206\179tmp)%I.
Time End refinement_recovery_defs.
Time Module mRT<: goose_refinement_type.
Time
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
Time Definition init_absr sa sc := Mail.initP sa \226\136\167 init_base sc.
Time
Definition \206\163 : gFunctors :=
  #[ @goose\206\163 gm gmWf; @cfg\206\163 Mail.Op Mail.l; ghost_map\206\163 ghost_init_statusC;
  ghost_map\206\163 contentsC; gen_heap\206\163 string Filesys.FS.Inode].
