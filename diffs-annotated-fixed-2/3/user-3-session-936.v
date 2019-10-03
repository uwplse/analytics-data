Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqfBHD4G"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Armada.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap MailTriples.
From Armada.Goose.Examples Require Import MailServer.
From Armada.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From Armada Require AtomicPair.Helpers.
From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Armada.Goose Require Import Machine.
From Armada.Goose Require Import GoZeroValues.
Inductive compile_mail_base {gm : GoModel} : forall {T}, proc Mail.Op T \226\134\146 proc GoLayer.Op T \226\134\146 Prop :=
  | cm_open : compile_mail_base (Call Mail.Open) MailServer.Open
  | cm_pickup : forall uid, compile_mail_base (Mail.pickup uid) (MailServer.Pickup uid)
  | cm_deliver : forall uid msg, compile_mail_base (Mail.deliver uid msg) (MailServer.Deliver uid msg)
  | cm_delete :
      forall uid msg, compile_mail_base (Call (Mail.Delete uid msg)) (MailServer.Delete uid msg)
  | cm_unlock : forall uid, compile_mail_base (Call (Mail.Unlock uid)) (MailServer.Unlock uid)
  | cm_dataop :
      forall {T} (op : Data.Op T), compile_mail_base (Call (Mail.DataOp op)) (Call (DataOp op)).
Definition mail_impl {gm : GoModel} :=
  {| compile_rel_base := @compile_mail_base gm; recover_rel := rec_singleton MailServer.Recover |}.
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
Definition InitInv_crash (\206\147 : gmap uint64 gname) \206\179 \207\131 :=
  (ghost_mapsto_auth \206\179 Uninit
   \226\136\151 ghost_mapsto \206\179 O Uninit
     \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), \226\136\131 \206\179uid, \226\140\156\206\147 !! uid = Some \206\179uid\226\140\157 \226\136\151 InboxLockInv \206\179uid O))%I.
Definition MsgsInv_crash (\206\147 : gmap uint64 gname) (\206\179 : gname) (\207\131 : Mail.State) : 
  iProp \206\163 :=
  (\226\136\131 ls,
     GlobalInv ls false
     \226\136\151 RootDirInv \207\131 \226\136\151 InitInv_crash \206\147 \206\179 \207\131 \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm false))%I.
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
#[global]Instance MsgsInv_crash_timeless  \206\147 \206\179 \207\131: (Timeless (MsgsInv_crash \206\147 \206\179 \207\131)).
Proof.
(apply _).
Qed.
Definition TmpInv_crash \206\179tmp : iProp \206\163 :=
  (\226\136\131 tmps_map,
     SpoolDir \226\134\166 dom (gset string) tmps_map
     \226\136\151 ghost_mapsto_auth (A:=discreteC (gset string)) \206\179tmp (dom (gset _) tmps_map)
       \226\136\151 ([\226\136\151 map] name\226\134\166inode \226\136\136 tmps_map, path.mk SpoolDir name \226\134\166 inode))%I.
Definition CrashInv \206\179tmp :=
  (\226\136\131 \206\147 \206\179,
     source_ctx
     \226\136\151 inv execN (\226\136\131 \207\131, source_state \207\131 \226\136\151 MsgsInv_crash \206\147 \206\179 \207\131 \226\136\151 HeapInv_crash \207\131 \226\136\151 TmpInv_crash \206\179tmp))%I.
Definition CrashStarter \206\179tmp :=
  (\226\136\131 tmps : gset string, ghost_mapsto (A:=discreteC (gset string)) \206\179tmp 0 tmps \226\136\151 SpoolDir \226\134\166 Unlocked)%I.
Definition CrashInner : iProp \206\163 :=
  (\226\136\131 \206\179tmp,
     (\226\136\131 \206\147 \206\179 \207\131, source_state \207\131 \226\136\151 MsgsInv_crash \206\147 \206\179 \207\131 \226\136\151 HeapInv_crash \207\131 \226\136\151 TmpInv_crash \206\179tmp)
     \226\136\151 CrashStarter \206\179tmp)%I.
End refinement_recovery_defs.
Module mRT<: goose_refinement_type.
Definition init_base `{@GoModelWf gm} (s : GoLayer.Go.State) :=
  s.(fs).(FS.heap) = \226\136\133
  \226\136\167 (forall uid : uint64,
     (uid < 100 -> s.(fs).(dirents) !! UserDir uid = Some \226\136\133)
     \226\136\167 (uid >= 100 -> s.(fs).(dirents) !! UserDir uid = None))
    \226\136\167 s.(fs).(FS.dirents) !! SpoolDir = Some \226\136\133
      \226\136\167 (\226\136\128 d, is_Some (s.(fs).(FS.dirents) !! d) \226\134\146 d = SpoolDir \226\136\168 (\226\136\131 uid, d = UserDir uid))
        \226\136\167 dom (gset string) s.(fs).(FS.dirents) = dom (gset string) s.(fs).(FS.dirlocks)
          \226\136\167 (\226\136\128 dir l, s.(fs).(FS.dirlocks) !! dir = Some l \226\134\146 fst l = Unlocked) \226\136\167 s.(maillocks) = None.
Context {gm : GoModel}.
Context {gmWf : GoModelWf gm}.
Definition init_absr sa sc := Mail.initP sa \226\136\167 init_base sc.
Definition \206\163 : gFunctors :=
  #[ @goose\206\163 gm gmWf; @cfg\206\163 Mail.Op Mail.l; ghost_map\206\163 ghost_init_statusC; 
  ghost_map\206\163 contentsC; gen_heap\206\163 string Filesys.FS.Inode].
Existing Instance subG_goosePreG.
Existing Instance subG_cfgPreG.
Definition OpT := Mail.Op.
Definition \206\155a := Mail.l.
Definition impl := mail_impl.
Instance from_exist_left_sep'  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) Q:
 (FromExist ((\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \206\166 a \226\136\151 Q)%I).
Proof.
rewrite /FromExist.
iIntros "H".
iDestruct "H" as ( ? ) "(?&$)".
(iExists _; eauto).
Qed.
Instance CFG : (@cfgPreG Mail.Op Mail.l \206\163).
(apply _).
Qed.
Instance HEX : (RefinementAdequacy.goosePreG gm \206\163).
(apply _).
Defined.
Instance INV : (Adequacy.invPreG \206\163).
(apply _).
Qed.
Instance REG : (inG \206\163 (csumR countingR (authR (optionUR (exclR unitC))))).
(apply _).
Qed.
#[global]Instance inG_inst1 : (ghost_mapG contentsC \206\163).
Proof.
(apply _).
Qed.
#[global]Instance inG_inst2 : (ghost_mapG ghost_init_statusC \206\163).
Proof.
(apply _).
Qed.
Definition exec_inv := fun H1 H2 => (\226\136\131 hGTmp, @ExecInv gm _ \206\163 H2 H1 _ _ hGTmp)%I.
Definition exec_inner := fun H1 H2 => (\226\136\131 hGTmp, @ExecInner gm _ \206\163 H2 H1 _ _ hGTmp)%I.
Definition crash_inner := fun H1 H2 => @CrashInner gm _ \206\163 H2 H1 _ _.
Definition crash_param := fun (_ : @cfgG OpT \206\155a \206\163) (_ : gooseG gm \206\163) => gname.
Definition crash_inv := fun H1 H2 \206\179 => @CrashInv _ _ \206\163 H2 H1 _ _ \206\179.
Definition crash_starter := fun (H1 : @cfgG OpT \206\155a \206\163) H2 \206\179 => @CrashStarter _ _ \206\163 H2 \206\179.
Definition E := nclose sourceN.
Definition recv := MailServer.Recover.
End mRT.
Module mRD:=  goose_refinement_definitions mRT.
Module mRO: goose_refinement_obligations mRT.
Module eRD:=  mRD.
Import mRT mRD.
Lemma init_dirs \207\1311a \207\1311c :
  init_absr \207\1311a \207\1311c
  \226\134\146 dom (gset string) \207\1311c.(fs).(dirents) =
    set_map UserDir (dom (gset uint64) \207\1311a.(messages)) \226\136\170 {[SpoolDir]}.
Proof.
(intros (Hinita, Hinitc)).
(destruct Hinita as (Hheap, (?, Hrange))).
(destruct Hinitc as (Hheap', (Hrange', (Hspool, (Hdirs, (Hlocks1, Hlocks2)))))).
(assert
  (dom (gset string) \207\1311c.(fs).(dirents) =
   set_map UserDir (dom (gset uint64) \207\1311a.(messages)) \226\136\170 {[SpoolDir]}) as ->; auto).
(<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>d).
split.
*
(intros Hin).
(apply elem_of_dom in Hin).
(edestruct (Hdirs d) as [| (uid, Heq)]; eauto).
**
subst.
set_solver +.
**
rewrite Heq.
(<ssreflect_plugin::ssrtclseq@0> destruct (lt_dec uid 100) ; last  first).
{
exfalso.
(destruct (Hrange' uid) as (?, Hnone)).
subst.
(rewrite Hnone in  {} Hin; try lia).
(eapply is_Some_None; eauto).
}
(apply elem_of_union_l).
(apply elem_of_map).
(exists uid; split; eauto).
(apply elem_of_dom).
(destruct (Hrange uid) as (Hsome, ?)).
(rewrite Hsome; auto).
eauto.
*
(intros [Huser| Hisspool]%elem_of_union).
**
(apply elem_of_dom).
(apply elem_of_map in Huser as (uid, (Heq, Hin))).
(apply elem_of_dom in Hin).
subst.
(<ssreflect_plugin::ssrtclseq@0> destruct (lt_dec uid 100) ; last  first).
{
exfalso.
(destruct (Hrange uid) as (?, Hnone)).
(rewrite Hnone in  {} Hin; try lia).
(eapply is_Some_None; eauto).
}
(destruct (Hrange' uid) as (Hsome, ?)).
(rewrite Hsome; eauto).
**
(apply elem_of_singleton in Hisspool).
subst.
(eapply elem_of_dom; eauto).
Qed.
Lemma init_base_dirs_empty \207\131 dir x : init_base \207\131 \226\134\146 \207\131.(fs).(dirents) !! dir = Some x \226\134\146 x = \226\136\133.
Proof.
(intros (_, (Hrange, (Hspool, (Hdom, _))))).
(intros Hsome).
(destruct (Hdom dir) as [| (uid, ?)]; eauto).
*
subst.
congruence.
*
(<ssreflect_plugin::ssrtclseq@0> destruct (lt_dec uid 100) ; last  first).
{
exfalso.
(destruct (Hrange uid) as (?, Hnone)).
subst.
(rewrite Hnone in  {} Hsome; try lia).
congruence.
}
(destruct (Hrange uid) as (Hsome', ?)).
subst.
(rewrite Hsome' in  {} Hsome; try lia).
congruence.
Qed.
Lemma einv_persist : forall {H1 : @cfgG OpT \206\155a \206\163} {H2}, Persistent (exec_inv H1 H2).
Proof.
(apply _).
Qed.
Lemma cinv_persist : forall {H1 : @cfgG OpT \206\155a \206\163} {H2} P, Persistent (crash_inv H1 H2 P).
Proof.
(apply _).
Qed.
Lemma nameIncl : nclose sourceN \226\138\134 E.
Proof.
solve_ndisj.
Qed.
Lemma recsingle : recover_rel impl = rec_singleton recv.
Proof.
trivial.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgjrAUS" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqLU7EyD" SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(* Auto-generated comment: Succeeded. *)

