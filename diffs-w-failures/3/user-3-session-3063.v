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
Time Definition gm : GoModel := _.
Time Definition gmWf : GoModelWf gm := _.
Time Definition init_absr sa sc := Mail.initP sa \226\136\167 init_base sc.
Time
Definition \206\163 : gFunctors :=
  #[ @goose\206\163 gm gmWf; @cfg\206\163 Mail.Op Mail.l; ghost_map\206\163 ghost_init_statusC;
  ghost_map\206\163 contentsC; gen_heap\206\163 string Filesys.FS.Inode].
Time Existing Instance subG_goosePreG.
Time Existing Instance subG_cfgPreG.
Time Definition OpT := Mail.Op.
Time Definition \206\155a := Mail.l.
Time Definition impl := mail_impl.
Time
Instance from_exist_left_sep'  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist ((\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \206\166 a \226\136\151 Q)%I).
Time Proof.
Time rewrite /FromExist.
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&$)".
Time (iExists _; eauto).
Time Qed.
Time Instance CFG : (@cfgPreG Mail.Op Mail.l \206\163).
Time (apply _).
Time Qed.
Time Instance HEX : (RefinementAdequacy.goosePreG gm \206\163).
Time (apply _).
Time Defined.
Time Instance INV : (Adequacy.invPreG \206\163).
Time (apply _).
Time Qed.
Time
Instance REG : (inG \206\163 (csumR countingR (authR (optionUR (exclR unitC))))).
Time (apply _).
Time Qed.
Time #[global]Instance inG_inst1 : (ghost_mapG contentsC \206\163).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance inG_inst2 : (ghost_mapG ghost_init_statusC \206\163).
Time Proof.
Time (apply _).
Time Qed.
Time
Definition exec_inv :=
  fun H1 H2 => (\226\136\131 hGTmp, @ExecInv gm _ \206\163 H2 H1 _ _ hGTmp)%I.
Time
Definition exec_inner :=
  fun H1 H2 => (\226\136\131 hGTmp, @ExecInner gm _ \206\163 H2 H1 _ _ hGTmp)%I.
Time Definition crash_inner := fun H1 H2 => @CrashInner gm _ \206\163 H2 H1 _ _.
Time
Definition crash_param := fun (_ : @cfgG OpT \206\155a \206\163) (_ : gooseG gm \206\163) => gname.
Time Definition crash_inv := fun H1 H2 \206\179 => @CrashInv _ _ \206\163 H2 H1 _ _ \206\179.
Time
Definition crash_starter :=
  fun (H1 : @cfgG OpT \206\155a \206\163) H2 \206\179 => @CrashStarter _ _ \206\163 H2 \206\179.
Time Definition E := nclose sourceN.
Time Definition recv := MailServer.Recover.
Time End mRT.
Time Module mRD:=  goose_refinement_definitions mRT.
Time Module mRO: goose_refinement_obligations mRT.
Time Module eRD:=  mRD.
Time Import mRT mRD.
Time
Lemma init_dirs \207\1311a \207\1311c :
  init_absr \207\1311a \207\1311c
  \226\134\146 dom (gset string) \207\1311c.(fs).(dirents) =
    set_map UserDir (dom (gset uint64) \207\1311a.(messages)) \226\136\170 {[SpoolDir]}.
Time Proof.
Time (intros (Hinita, Hinitc)).
Time (destruct Hinita as (Hheap, (?, Hrange))).
Time
(destruct Hinitc
  as (Hheap', (Hrange', (Hspool, (Hdirs, (Hlocks1, Hlocks2)))))).
Time
(assert
  (dom (gset string) \207\1311c.(fs).(dirents) =
   set_map UserDir (dom (gset uint64) \207\1311a.(messages)) \226\136\170 {[SpoolDir]}) 
  as ->; auto).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>d).
Time split.
Time *
Time (intros Hin).
Time (apply elem_of_dom in Hin).
Time (edestruct (Hdirs d) as [| (uid, Heq)]; eauto).
Time **
Time subst.
Time set_solver +.
Time **
Time rewrite Heq.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (lt_dec uid 100) ; last  first).
Time {
Time exfalso.
Time (destruct (Hrange' uid) as (?, Hnone)).
Time subst.
Time (rewrite Hnone in  {} Hin; try lia).
Time (eapply is_Some_None; eauto).
Time }
Time (apply elem_of_union_l).
Time (apply elem_of_map).
Time (exists uid; split; eauto).
Time (apply elem_of_dom).
Time (destruct (Hrange uid) as (Hsome, ?)).
Time (rewrite Hsome; auto).
Time eauto.
Time *
Time (intros [Huser| Hisspool]%elem_of_union).
Time **
Time (apply elem_of_dom).
Time (apply elem_of_map in Huser as (uid, (Heq, Hin))).
Time (apply elem_of_dom in Hin).
Time subst.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (lt_dec uid 100) ; last  first).
Time {
Time exfalso.
Time (destruct (Hrange uid) as (?, Hnone)).
Time (rewrite Hnone in  {} Hin; try lia).
Time (eapply is_Some_None; eauto).
Time }
Time (destruct (Hrange' uid) as (Hsome, ?)).
Time (rewrite Hsome; eauto).
Time **
Time (apply elem_of_singleton in Hisspool).
Time subst.
Time (eapply elem_of_dom; eauto).
Time Qed.
Time
Lemma init_base_dirs_empty \207\131 dir x :
  init_base \207\131 \226\134\146 \207\131.(fs).(dirents) !! dir = Some x \226\134\146 x = \226\136\133.
Time Proof.
Time (intros (_, (Hrange, (Hspool, (Hdom, _))))).
Time (intros Hsome).
Time (destruct (Hdom dir) as [| (uid, ?)]; eauto).
Time *
Time subst.
Time congruence.
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (lt_dec uid 100) ; last  first).
Time {
Time exfalso.
Time (destruct (Hrange uid) as (?, Hnone)).
Time subst.
Time (rewrite Hnone in  {} Hsome; try lia).
Time congruence.
Time }
Time (destruct (Hrange uid) as (Hsome', ?)).
Time subst.
Time (rewrite Hsome' in  {} Hsome; try lia).
Time congruence.
Time Qed.
Time
Lemma einv_persist :
  forall {H1 : @cfgG OpT \206\155a \206\163} {H2}, Persistent (exec_inv H1 H2).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma cinv_persist :
  forall {H1 : @cfgG OpT \206\155a \206\163} {H2} P, Persistent (crash_inv H1 H2 P).
Time Proof.
Time (apply _).
Time Qed.
Time Lemma nameIncl : nclose sourceN \226\138\134 E.
Time Proof.
Time solve_ndisj.
Time Qed.
Time Lemma recsingle : recover_rel impl = rec_singleton recv.
Time Proof.
Time trivial.
Time Qed.
Time Lemma refinement_base_triples : refinement_base_triples_type.
Time Proof.
Time (intros ? ? ? ? j K Hctx p p' Hcompile).
Time iIntros "(Hj&Hreg&Hexec)".
Time iDestruct "Hexec" as ( hGTmp ) "Hexec".
Time (inversion Hcompile; inj_pair2).
Time -
Time iApply (open_refinement with "[$]").
Time iIntros "!>".
Time (iIntros ( ? ) "(?&?)"; iFrame).
Time -
Time iApply (pickup_refinement with "[$]").
Time iIntros "!>".
Time (iIntros ( ? ) "(?&?)"; iFrame).
Time -
Time iApply (deliver_refinement with "[$]").
Time iIntros "!>".
Time (iIntros ( ? ) "(?&?)"; iFrame).
Time -
Time iApply (delete_refinement with "[$]").
Time iIntros "!>".
Time (iIntros ( ? ) "(?&?)"; iFrame).
Time -
Time iApply (lock_refinement with "[$]").
Time iIntros "!>".
Time (iIntros ( ? ) "(?&?)"; iFrame).
Time -
Time iApply (unlock_refinement with "[$]").
Time iIntros "!>".
Time (iIntros ( ? ) "(?&?)"; iFrame).
Time -
Time iDestruct "Hexec" as ( \206\147 \206\179 ) "(#Hsource&#Hinv)".
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iApply (data_op_refinement j K with "[$]").
Time {
Time solve_ndisj.
Time }
Time iIntros ( v ) "!> H".
Time iDestruct "H" as ( h' ) "(Hj&Hreg&Hstate&Hheap)".
Time iModIntro.
Time iFrame.
Time iNext.
Time iExists _.
Time iFrame.
Time Qed.
Time Lemma exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx.
Time Proof.
Time (intros).
Time iIntros "H".
Time iDestruct "H" as ( hGTmp ? ? ) "($&?)".
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time (red).
Time (intros H1 H2 param).
Time iIntros "(Hrest&Hreg&Hstarter)".
Time iDestruct "Hrest" as ( \206\147 \206\179 ) "(#Hsource&#Hinv)".
Time iDestruct "Hstarter" as ( tmps ) "(Htmps_frag&Hlock)".
Time wp_bind.
Time wp_bind.
Time iApply (wp_list_start with "[$]").
Time iIntros "!> Hlock".
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
Time iDestruct "Htmp" as ( tmps_map ) "(Hdir&Hauth&Hpaths)".
Time
iDestruct (@ghost_var_agree (discreteC (gset string)) \206\163 with "Hauth [$]") as
 % Heq_dom.
Time iApply (wp_list_finish with "[$]").
Time iIntros ( s ltmps ) "!> (Hltmps&Hs&Htmps&Hlock)".
Time iExists _.
Time iSplitL "Hstate Hmsgs Hheap Hauth Htmps Hpaths".
Time {
Time iFrame.
Time iExists _.
Time by iFrame.
Time }
Time iModIntro.
Time iDestruct "Hltmps" as % Hltmps.
Time (assert (tmps = tmps \226\136\150 list_to_set (take 0 ltmps)) as ->).
Time {
Time by rewrite difference_empty_L.
Time }
Time iDestruct (slice_mapsto_len with "Hs") as % ->.
