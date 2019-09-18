Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time
From Perennial.Examples.MailServer Require Import MailAPI MailAPILemmas
  MailHeap MailTriples.
Time From Perennial.Goose.Examples Require Import MailServer.
Time From Perennial.Goose.Proof Require Import Interp.
Time Require Import Goose.Proof.RefinementAdequacy.
Time From Perennial Require AtomicPair.Helpers.
Time From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Perennial.Goose Require Import Machine.
Time From Perennial.Goose Require Import GoZeroValues.
Time From Perennial.Goose Require Import ExplicitModel.
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
     \226\136\151 ghost_mapsto_auth (A:=discreteO (gset string)) \206\179tmp
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
     ghost_mapsto (A:=discreteO (gset string)) \206\179tmp 0 tmps
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
Time Instance gm : GoModel := aModel.
Time Instance gmWf : (GoModelWf gm) := aModel_wf.
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
Instance REG : (inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))).
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
iDestruct (@ghost_var_agree (discreteO (gset string)) \206\163 with "Hauth [$]") as
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
Time (assert (Hlen : 0 <= length ltmps) by lia).
Time revert Hlen.
Time (remember 0 as i eqn:Heq_i ).
Time (intros Hlen).
Time rewrite [a in S a]Heq_i.
Time clear Heq_i.
Time iL\195\182b as "IH" forall ( i Hlen ).
Time wp_loop.
Time (destruct equal as [Heqlen| Hneq]).
Time -
Time iClear "IH".
Time subst.
Time rewrite firstn_all.
Time wp_ret.
Time wp_ret.
Time iNext.
Time iInv "Hinv" as "H" "_".
Time clear \207\131.
Time iDestruct "H" as ( \207\131 ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
Time iApply (fupd_mask_weaken _ _).
Time {
Time solve_ndisj.
Time }
Time iExists _ , _.
Time iFrame.
Time iSplitL "".
Time {
Time iPureIntro.
Time (do 2 eexists; split; econstructor).
Time }
Time iClear "Hsource".
Time iIntros ( ? ? ? ) "(#Hsource&Hstate)".
Time iDestruct "Htmp" as ( tmps_map' ) "(Hdir&Hauth&Hpaths)".
Time
iDestruct (@ghost_var_agree (discreteO (gset string)) \206\163 with "[$] [$]") as %
 Heq_dom.
Time (rewrite <- Heq_dom).
Time iMod (gen_heap_init tmps_map') as ( hGTmp ) "Htmp".
Time iExists hGTmp , \206\147 , \206\179 , _.
Time iFrame.
Time iSplitL "".
Time {
Time eauto.
Time }
Time iSplitL "Hmsgs".
Time {
Time by iApply MsgsInv_crash_set_false.
Time }
Time iSplitL "".
Time {
Time iModIntro.
Time by iApply big_sepDM_empty.
Time }
Time iExists _.
Time by iFrame.
Time -
Time wp_bind.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (nth_error ltmps i) as [curr_name| ] eqn:Heq_curr_name ; last 
 first).
Time {
Time exfalso.
Time (eapply nth_error_Some; eauto).
Time (inversion Hlen; try congruence; try lia).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_sliceRead with "[$]") ; first 
 eauto).
Time iIntros "!> Hs".
Time wp_bind.
Time iInv "Hinv" as "H".
Time clear \207\131.
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iDestruct "Htmp" as ( tmps_map' ) "(Hdir&Hauth&Hpaths)".
Time
iDestruct (@ghost_var_agree (discreteO (gset string)) \206\163 with "[$] [$]") as %
 Heq_dom'.
Time rewrite Heq_dom'.
Time (assert (Hcurr_in : curr_name \226\136\136 tmps \226\136\150 list_to_set (take i ltmps))).
Time {
Time (apply elem_of_difference; split).
Time -
Time rewrite -Heq_dom.
Time (apply elem_of_elements).
Time rewrite -Hltmps.
Time (apply elem_of_list_In).
Time (eapply nth_error_In; eauto).
Time -
Time rewrite elem_of_list_to_set.
Time rewrite elem_of_list_In.
Time (assert (HNoDup : NoDup ltmps)).
Time {
Time rewrite Hltmps.
Time (apply NoDup_elements).
Time }
Time
(eapply nth_error_split in Heq_curr_name as (l1, (l2, (Hsplit, Hlen')))).
Time rewrite Hsplit.
Time rewrite -Hlen' take_app.
Time rewrite Hsplit in  {} HNoDup.
Time (apply NoDup_app in HNoDup as (?, (Hnotin, ?))).
Time (intros Hin).
Time (eapply Hnotin).
Time {
Time (apply elem_of_list_In).
Time eauto.
Time }
Time by left.
Time }
Time (assert (\226\136\131 v, tmps_map' !! curr_name = Some v) as (inode, Hcurr_inode)).
Time {
Time rewrite -Heq_dom' in  {} Hcurr_in.
Time (apply elem_of_dom in Hcurr_in as (v, ?)).
Time eauto.
Time }
Time (iDestruct (big_sepM_delete with "Hpaths") as "(Hcurr&Hpaths)"; eauto).
Time iApply (wp_delete with "[$]").
Time iIntros "!> (Hdir&Hdirlock)".
Time
iMod (@ghost_var_update (discreteO (gset string)) with "Hauth [$]") as
 "(Hauth&Hfrag)".
Time iSplitL "Hstate Hmsgs Hheap Hpaths Hdir Hauth".
Time {
Time iExists _.
Time iFrame.
Time iModIntro.
Time iNext.
Time iExists _.
Time iFrame.
Time rewrite dom_delete_L.
Time rewrite Heq_dom'.
Time iFrame.
Time }
Time wp_ret.
Time iModIntro.
Time iNext.
Time iApply ("IH" with "[] [$] [Hfrag] [$] [$]").
Time {
Time iPureIntro.
Time (inversion Hlen; try congruence; try lia).
Time }
Time rewrite dom_delete_L Heq_dom'.
Time rewrite difference_difference_L.
Time
(<ssreflect_plugin::ssrtclseq@0>
 assert
  (tmps \226\136\150 list_to_set (take (i + 1) ltmps) =
   tmps \226\136\150 (list_to_set (take i ltmps) \226\136\170 {[curr_name]})) 
  as -> ; last  by auto).
Time f_equal.
Time
(eapply nth_error_split in Heq_curr_name as (l1, (l2, (Hsplit, Hlen')))).
Time rewrite Hsplit -Hlen' take_app.
Time rewrite firstn_app_2 //= firstn_O.
Time rewrite list_to_set_app_L //= right_id_L //.
Time Unshelve.
Time (eapply sigPtr_eq_dec).
Time Qed.
Time Lemma init_wf : init_wf_type.
Time Proof.
Time (red).
Time rewrite /init_absr /initP /init_base.
Time intuition.
Time Qed.
Time Lemma init_exec_inner : init_exec_inner_type.
Time Proof.
Time clear.
Time iIntros ( \207\1311a \207\1311c Hinit ).
Time iIntros ( ? ? ) "(Hdirs&Hroot&Hdirlocks&Hsrc&Hstate&Hglobal)".
Time (pose proof (init_dirs _ _ Hinit) as Hdirs).
Time (destruct Hinit as (Hinita, Hinitc)).
Time iMod (gen_heap_init (\226\136\133 : gmap string Inode)) as ( hGTmp ) "Htmp".
Time iExists hGTmp.
Time
iMod (ghost_var_alloc (A:=@ghost_init_statusC mRT.gm mRT.gmWf) Uninit) as "H".
Time iDestruct "H" as ( \206\179 ) "(Hauth&Hfrag)".
Time
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\1311a.(messages) (\206\187 _ _, \226\136\133)) as "H".
Time iDestruct "H" as ( \206\147 H\206\147dom ) "H\206\147".
Time
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\1311a.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147 !! k = Some \206\1790\226\140\157)%I
 with "[H\206\147]" as "#H\206\147'".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
Time iIntros ( ? ? ? ) "H".
Time (iDestruct "H" as ( ? ) "(?&?)"; eauto).
Time }
Time iExists \206\147 , \206\179 , \207\1311a.
Time iFrame.
Time (assert (SpoolDir \226\136\136 dom (gset string) \207\1311c.(fs).(dirents))).
Time {
Time rewrite /init_base in  {} Hinitc.
Time intuition.
Time (apply elem_of_dom).
Time (eexists; eauto).
Time }
Time iSplitL "".
Time {
Time iPureIntro.
Time (destruct Hinita as (?, (->, ?)); auto).
Time }
Time
(iDestruct (big_opS_delete with "Hdirlocks") as "(Hlock&Hdirlocks)"; eauto).
Time iDestruct (big_opM_delete with "Hdirs") as "(Hspool&Hdirs)".
Time {
Time rewrite /init_base in  {} Hinitc.
Time intuition.
Time eauto.
Time }
Time iSplitR "Htmp Hlock Hspool".
Time {
Time rewrite /MsgsInv.
Time iExists [].
Time rewrite /initP in  {} Hinita.
Time (destruct Hinita as (Hheap, (Hopen, Hrange))).
Time rewrite Hopen.
Time iFrame.
Time iSplitL "Hroot".
Time {
Time iModIntro.
Time rewrite /RootDirInv.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  first).
Time -
Time iPureIntro.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>uid).
Time (destruct (Hrange uid)).
Time (split; intros).
Time *
Time (apply elem_of_dom; eexists; eauto).
Time *
Time (apply not_elem_of_dom; eauto).
Time -
Time rewrite /init_base in  {} Hinitc.
Time rewrite Hdirs.
Time eauto.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Hdirs Hdirlocks" ; last  first).
Time {
Time rewrite -dom_delete_L.
Time iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
Time
(<ssreflect_plugin::ssrtclseq@0> iAssert
 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\1311a.(messages), MsgInv \206\147 [] uid (MUnlocked, \226\136\133) false)%I
 with "[Hdirs Hdirlocks]" as "H" ; last  first).
Time {
Time iModIntro.
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hin ) "H".
Time iDestruct "H" as ( ? \206\179uid ) "(H1&H2&H3)".
Time iExists _ , _.
Time iFrame.
Time
(<ssreflect_plugin::ssrtclseq@0> assert (x = (MUnlocked, \226\136\133)) as -> ; last  by
 auto).
Time (destruct (lt_dec k 100) as [Hlt| Hnlt]).
Time *
Time (destruct (Hrange k) as (Hrange1, ?)).
Time
(<ssreflect_plugin::ssrtclseq@0> feed pose proof Hrange1 ; first  by lia).
Time congruence.
Time *
Time (destruct (Hrange k) as (?, Hgt)).
Time (<ssreflect_plugin::ssrtclseq@0> feed pose proof Hgt ; first  by lia).
Time congruence.
Time }
Time
iAssert ([\226\136\151 map] k\226\134\166y \226\136\136 base.delete SpoolDir \207\1311c.(fs).(dirents), k \226\134\166 \226\136\133)%I with
 "[Hdirs]" as "Hdirs".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
Time iIntros ( dir x Hin ) "Hk".
Time (cut (x = \226\136\133)).
Time {
Time (intros ->).
Time by rewrite dom_empty_L.
Time }
Time (apply lookup_delete_Some in Hin as (Hneq, Hlookup)).
Time (destruct (Hinitc) as (?, (Hrange', _))).
Time (eapply init_base_dirs_empty; eauto).
Time }
Time
(assert
  (Hdirs_delete :
   dom (gset string) (map_delete SpoolDir \207\1311c.(fs).(dirents)) =
   set_map UserDir (dom (gset uint64) \207\1311a.(messages)))).
Time {
Time rewrite dom_delete_L Hdirs.
Time set_solver +.
Time }
Time move : {}Hdirs_delete {}.
Time rewrite /base.delete.
Time
(<ssreflect_plugin::ssrtclintros@0>
 generalize (map_delete SpoolDir \207\1311c.(fs).(dirents)) =>dirs).
Time (<ssreflect_plugin::ssrtclintros@0> generalize \207\1311a.(messages) =>msgs).
Time (<ssreflect_plugin::ssrtclintros@0> clear Hrange Hdirs Hheap H =>Hdom).
Time iInduction msgs as [| k i m] "IH" using map_ind forall ( dirs Hdom ).
Time {
Time by iApply big_sepM_empty.
Time }
Time rewrite big_sepM_insert //.
Time rewrite big_sepM_insert //.
Time (assert (\226\136\131 v, dirs !! UserDir k = Some v) as (v, Hin)).
Time {
Time rewrite dom_insert_L in  {} Hdom.
Time (assert (Hin : UserDir k \226\136\136 dom (gset string) dirs)).
Time {
Time set_solver.
Time }
Time (apply elem_of_dom in Hin).
Time eauto.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_delete with "Hdirlocks")
 as "(Hlock&Hdirlocks)" ; first  eauto).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_delete with "Hdirs") as
 "(Hdir&Hdirs)" ; first  eauto).
Time iDestruct "H\206\147'" as "(Hghost&H\206\147')".
Time iSplitL "Hlock Hdir Hghost".
Time {
Time iDestruct "Hghost" as ( \206\179uid ) "H".
Time iExists (zeroValue _) , \206\179uid.
Time iFrame.
Time (simpl).
Time rewrite dom_empty_L.
Time iFrame.
Time (iSplitL ""; auto).
Time }
Time iApply ("IH" with "[] [$] [$] [$]").
Time iPureIntro.
Time rewrite dom_insert_L in  {} Hdom.
Time rewrite dom_delete_L.
Time rewrite Hdom.
Time
(assert
  (Hnin : UserDir k \226\136\137 (set_map UserDir (dom (gset uint64) m) : gset string))).
Time {
Time rewrite elem_of_map.
Time (intros (k0, (Heq, Hin'))).
Time (apply string_app_inj, uint64_to_string_inj in Heq).
Time subst.
Time (apply elem_of_dom in Hin' as (?, ?); congruence).
Time }
Time clear - Hnin.
Time rewrite set_map_union_singleton.
Time rewrite -leibniz_equiv_iff.
Time rewrite difference_union_distr_l.
Time rewrite difference_diag_L left_id.
Time rewrite difference_disjoint //.
Time rewrite disjoint_singleton_r.
Time auto.
Time }
Time iExists _.
Time iFrame.
Time iFrame.
Time (iSplitL ""; auto).
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
Time iIntros ( ? ? ? ) "H".
Time iDestruct "H" as ( \206\179uid ) "(?&?&?)".
Time iExists _.
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time }
Time {
Time iSplitL "".
Time -
Time rewrite /HeapInv.
Time rewrite /initP in  {} Hinita.
Time (destruct Hinita as (->, ?)).
Time (simpl).
Time iModIntro.
Time by iApply big_sepDM_empty.
Time -
Time iExists \226\136\133.
Time iFrame.
Time by iApply big_sepM_empty.
Time }
Time Unshelve.
Time apply : {}sigPtr_eq_dec {}.
Time Qed.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time iIntros ( ? ? ) "H".
Time iDestruct "H" as ( hGtmp_old ) "Hrest".
Time iDestruct "Hrest" as ( \206\147old \206\179old ) "(#Hsource&#Hinv)".
Time iInv "Hinv" as "H" "_".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iApply (fupd_mask_weaken _ _).
Time {
Time solve_ndisj.
Time }
Time iDestruct "Hmsgs" as ( ? ) "(_&>Hroot&Hinit&Hmsgs)".
Time iDestruct (big_sepM_mono with "Hmsgs") as "Hmsgs".
Time {
Time iIntros ( ? ? ? ).
Time iApply MsgInv_weaken.
Time }
Time iDestruct "Hmsgs" as ">Hmsgs".
Time iIntros ( ? ? ? ? ? ) "(Hroot'&Hglobal)".
Time iDestruct "Hroot'" as ( S ) "(Hroot'&Hdirlocks)".
Time iDestruct "Hroot" as "(Hroot&%)".
Time
iDestruct (@ghost_var_agree2 (discreteO (gset string)) _ with "Hroot Hroot'")
 as % Heq_dom.
Time iDestruct "Htmp" as ( tmp_map ) "(Hdir&_&_&Hpaths)".
Time iMod (gen_heap_init (tmp_map : gmap string Inode)) as ( hGTmp ) "Htmp".
Time
iMod (@ghost_var_alloc (@ghost_init_statusC _ mRT.gmWf) _ _ _ _ Uninit) as
 "H".
Time iDestruct "H" as ( \206\179 ) "(Hauth&Hfrag)".
Time
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\131.(messages) (\206\187 _ _, \226\136\133)) as "H".
Time iDestruct "H" as ( \206\147 H\206\147dom ) "H\206\147".
Time
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\131.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147 !! k = Some \206\1790\226\140\157)%I with
 "[H\206\147]" as "#H\206\147'".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
Time iIntros ( ? ? ? ) "H".
Time (iDestruct "H" as ( ? ) "(?&?)"; eauto).
Time }
Time
iMod
 (@ghost_var_alloc (@discreteO (gset string)) _ _ _
    Hex.(@go_fs_inG mRT.gm mRT.gmWf \206\163).(@go_fs_domalg_inG mRT.gm mRT.gmWf \206\163)
    (dom (gset _) tmp_map)) as "H".
Time iDestruct "H" as ( \206\179tmp ) "(Hauth_tmp&Hfrag_tmp)".
Time iModIntro.
Time iExists \206\179tmp , \206\147 , \206\179 , _.
Time iFrame.
Time (rewrite <- Heq_dom).
Time
iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
Time {
Time by apply elem_of_union_r, elem_of_singleton.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Hfrag_tmp Hspoollock" ; last 
 first).
Time {
Time iExists _.
Time (iSplitL "Hfrag_tmp"; auto).
Time }
Time iExists [].
Time rewrite /HeapInv.
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Htmp Hdir Hauth_tmp Hpaths" ; last 
 first).
Time {
Time (iSplitL ""; auto).
Time iExists _.
Time iFrame.
Time }
Time (iSplitL ""; auto).
Time iSplitL "H\206\147".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
Time iIntros ( ? ? ? ) "H".
Time iDestruct "H" as ( \206\179uid ? ) "(?&?)".
Time iExists _.
Time (iSplitL ""; auto).
Time iExists _ , _.
Time iFrame.
Time }
Time iClear "Hheap".
Time
(assert
  (((set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
    \226\136\150 {[SpoolDir]}
      : gset string) = set_map UserDir (dom (gset uint64) \207\131.(messages)))
  as ->).
Time {
Time set_solver.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> rewrite big_opS_fmap ; last  first).
Time {
Time rewrite /UserDir.
Time (intros ? ? Heq).
Time (apply string_app_inj, uint64_to_string_inj in Heq).
Time auto.
Time }
Time iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
Time iDestruct (big_sepM_sep with "[Hdirlocks Hmsgs]") as "Hmsgs".
Time {
Time iFrame.
Time }
Time iDestruct (big_sepM_sep with "[Hmsgs]") as "Hmsgs".
Time {
Time iFrame.
Time iFrame "H\206\147'".
Time }
Time iApply (big_sepM_mono with "Hmsgs").
Time iIntros ( k x Hlookup ) "((H1&H2)&H3)".
Time iDestruct "H3" as % Hlookup'.
Time (destruct Hlookup' as (\206\179', ?)).
Time iDestruct "H1" as ( ? ? ) "(_&(?&?&?))".
Time iExists _ , _.
Time (iSplitL ""; eauto).
Time (iSplitL ""; eauto).
Time iFrame.
Time auto.
Time Unshelve.
Time (apply (zeroValue _)).
Time Qed.
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time Proof.
Time iIntros ( ? ? \206\179tmp ) "Hcrash".
Time iDestruct "Hcrash" as ( ? ? ) "(#Hsrc&#Hinv)".
Time iInv "Hinv" as "H" "_".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
Time iApply (fupd_mask_weaken _ _).
Time {
Time solve_ndisj.
Time }
Time iDestruct "Hmsgs" as ( ? ) "(_&Hroot&Hinit&Hmsgs)".
Time iIntros ( ? ? ? ? ? ) "(Hroot'&Hglobal)".
Time iDestruct "Hroot'" as ( S ) "(Hroot'&Hdirlocks)".
Time iDestruct "Hroot" as "(Hroot&%)".
Time
iDestruct (@ghost_var_agree2 (discreteO (gset string)) _ with "Hroot Hroot'")
 as % Heq_dom.
Time iDestruct "Htmp" as ( tmp_map ) "(Hdir&_&Hpaths)".
Time iMod (gen_heap_init (tmp_map : gmap string Inode)) as ( hGTmp ) "Htmp".
Time
iMod (ghost_var_alloc (A:=@ghost_init_statusC _ mRT.gmWf) Uninit) as "H".
Time iDestruct "H" as ( \206\179 ) "(Hauth&Hfrag)".
Time
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\131.(messages) (\206\187 _ _, \226\136\133)) as "H".
Time iDestruct "H" as ( \206\147 H\206\147dom ) "H\206\147".
Time
iMod
 (@ghost_var_alloc (@discreteO (gset string)) _ _ _
    Hex.(@go_fs_inG mRT.gm mRT.gmWf \206\163).(@go_fs_domalg_inG mRT.gm mRT.gmWf \206\163)
    (dom (gset _) tmp_map)) as "H".
Time iDestruct "H" as ( \206\179tmp' ) "(Hauth_tmp&Hfrag_tmp)".
Time
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\131.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147 !! k = Some \206\1790\226\140\157)%I with
 "[H\206\147]" as "#H\206\147'".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
Time iIntros ( ? ? ? ) "H".
Time (iDestruct "H" as ( ? ) "(?&?)"; eauto).
Time }
Time iModIntro.
Time iExists \206\179tmp' , \206\147 , \206\179 , _.
Time iFrame.
Time (rewrite <- Heq_dom).
Time
iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
Time {
Time by apply elem_of_union_r, elem_of_singleton.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Hfrag_tmp Hspoollock" ; last 
 first).
Time {
Time iExists _.
Time iFrame.
Time }
Time iExists [].
Time rewrite /HeapInv.
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Htmp Hdir Hauth_tmp Hpaths" ; last 
 first).
Time {
Time iExists _.
Time iFrame.
Time }
Time (iSplitL ""; auto).
Time iSplitL "H\206\147".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
Time iIntros ( ? ? ? ) "H".
Time iDestruct "H" as ( \206\179uid ? ) "(?&?)".
Time iExists _.
Time (iSplitL ""; auto).
Time iExists _ , _.
Time iFrame.
Time }
Time
(assert
  (((set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
    \226\136\150 {[SpoolDir]}
      : gset string) = set_map UserDir (dom (gset uint64) \207\131.(messages)))
  as ->).
Time {
Time set_solver.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> rewrite big_opS_fmap ; last  first).
Time {
Time rewrite /UserDir.
Time (intros ? ? Heq).
Time (apply string_app_inj, uint64_to_string_inj in Heq).
Time auto.
Time }
Time iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
Time iDestruct (big_sepM_sep with "[Hdirlocks Hmsgs]") as "Hmsgs".
Time {
Time iFrame.
Time }
Time iDestruct (big_sepM_sep with "[Hmsgs]") as "Hmsgs".
Time {
Time iFrame.
Time iFrame "H\206\147'".
Time }
Time iApply (big_sepM_mono with "Hmsgs").
Time iIntros ( k x Hlookup ) "((H1&H2)&H3)".
Time iDestruct "H3" as % Hlookup'.
Time (destruct Hlookup' as (\206\179', ?)).
Time iDestruct "H1" as ( ? ? ) "(_&(?&?&?&?&?))".
Time iExists _ , _.
Time (iSplitL ""; eauto).
Time (iSplitL ""; eauto).
Time iFrame.
Time auto.
Time Unshelve.
Time (apply (zeroValue _)).
Time Qed.
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time iIntros ( ? ? ) "(H1&H2)".
Time iDestruct "H1" as ( Hinv \206\179tmp ) "(H&Hstarter)".
Time iDestruct "H" as ( ? ? ? ) "(?&?&?)".
Time iExists _.
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod
 (@inv_alloc \206\163 go_invG execN _ _ with "[-]") ; last  eauto).
Time iNext.
Time iExists _.
Time iFrame.
Time Qed.
Time Lemma exec_inner_inv : exec_inner_inv_type.
Time Proof.
Time iIntros ( ? ? ) "(H1&H2)".
Time
iDestruct "H1" as ( Hinv hGTmp ? ? ? Hclosed ) "(Hstate&Hmsgs&Heap&Htmps)".
Time iExists hGTmp.
Time iExists _ , _.
Time iFrame.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod
 (@inv_alloc \206\163 go_invG execN _ _ with "[-]") ; last  eauto).
Time iNext.
Time iExists _.
Time iFrame "Hstate Heap Htmps".
Time rewrite /MsgsInv.
Time iDestruct "Hmsgs" as ( ? ) "(Hglobal&Hroot&Hinit&Hmsgs)".
Time iExists _.
Time iFrame "Hglobal Hroot Hinit".
Time rewrite Hclosed.
Time eauto.
Time Qed.
Time Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Time Proof.
Time iIntros ( ? ? ) "_ H".
Time iDestruct "H" as ( hGTmp \206\147 \206\179 ) "Hrest".
Time iDestruct "Hrest" as "(#Hsource&#Hinv)".
Time iInv "Hinv" as "H" "_".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iDestruct "Hmsgs" as ( ? ) "(_&>Hroot&Hinit&Hmsgs)".
Time iDestruct (big_sepM_mono with "Hmsgs") as "Hmsgs".
Time {
Time iIntros ( ? ? ? ).
Time iApply MsgInv_weaken.
Time }
Time iDestruct "Hmsgs" as ">Hmsgs".
Time iApply (fupd_mask_weaken _ _).
Time {
Time solve_ndisj.
Time }
Time iExists _ , _.
Time iFrame.
Time iSplitL "".
Time {
Time iPureIntro.
Time (do 2 eexists).
Time (split; econstructor).
Time }
Time iDestruct "Hroot" as "(Hroot&%)".
Time iClear "Hsource".
Time iIntros ( ? ? ? ? ? ? ? ) "(#Hsource&Hstate&Hdirlocks&Hglobal)".
Time iDestruct "Htmp" as ( tmps_map' ) "(Hdir&Hdirlock&Hauth'&Hpaths)".
Time iMod (gen_heap_init tmps_map') as ( hGTmp' ) "Htmp".
Time
iMod (@ghost_var_alloc (@ghost_init_statusC _ mRT.gmWf) _ _ _ _ Uninit) as
 "H".
Time iDestruct "H" as ( \206\179' ) "(Hauth&Hfrag)".
Time
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\131.(messages) (\206\187 _ _, \226\136\133)) as "H".
Time iDestruct "H" as ( \206\147' H\206\147dom ) "H\206\147".
Time iDestruct "Hdirlocks" as ( S ) "(Hroot'&Hdirlocks)".
Time
iDestruct (@ghost_var_agree2 (discreteO (gset string)) _ with "Hroot Hroot'")
 as % Heq_dom.
Time
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\131.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147' !! k = Some \206\1790\226\140\157)%I
 with "[H\206\147]" as "#H\206\147'".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
Time iIntros ( ? ? ? ) "H".
Time (iDestruct "H" as ( ? ) "(?&?)"; eauto).
Time }
Time iExists hGTmp' , \206\147' , \206\179' , _.
Time iModIntro.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  eauto).
Time iExists [].
Time iFrame.
Time (rewrite <- Heq_dom).
Time
iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
Time {
Time by apply elem_of_union_r, elem_of_singleton.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Htmp Hdir Hpaths Hspoollock" ;
 last  first).
Time {
Time iSplitL "".
Time {
Time by iApply big_sepDM_empty.
Time }
Time iExists _.
Time iFrame.
Time }
Time (iSplitL ""; auto).
Time iExists _.
Time iFrame.
Time iFrame.
Time iSplitL "H\206\147".
Time {
Time (iSplitL ""; auto).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
Time iIntros ( ? ? ? ) "H".
Time iDestruct "H" as ( \206\179uid ? ) "(?&?)".
Time iExists _.
Time (iSplitL ""; auto).
Time iExists _ , _.
Time iFrame.
Time }
Time
(assert
  (((set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
    \226\136\150 {[SpoolDir]}
      : gset string) = set_map UserDir (dom (gset uint64) \207\131.(messages)))
  as ->).
Time {
Time set_solver.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> rewrite big_opS_fmap ; last  first).
Time {
Time rewrite /UserDir.
Time (intros ? ? Heq).
Time (apply string_app_inj, uint64_to_string_inj in Heq).
Time auto.
Time }
Time iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
Time iDestruct (big_sepM_sep with "[Hdirlocks Hmsgs]") as "Hmsgs".
Time {
Time iFrame.
Time }
Time iDestruct (big_sepM_sep with "[Hmsgs]") as "Hmsgs".
Time {
Time iFrame.
Time iFrame "H\206\147'".
Time }
Time iApply (big_sepM_mono with "Hmsgs").
Time iIntros ( k x Hlookup ) "((H1&H2)&H3)".
Time iDestruct "H3" as % Hlookup'.
Time (destruct Hlookup' as (\206\179'', ?)).
Time iDestruct "H1" as ( ? ? ) "(_&H)".
Time iDestruct "H" as "(?&?&?)".
Time iExists _ , _.
Time (iSplitL ""; eauto).
Time (iSplitL ""; eauto).
Time iFrame.
Time auto.
Time Unshelve.
Time (apply sigPtr_eq_dec).
Time idtac "Beginning final qed soon.".
Time (apply (zeroValue _)).
Time Qed.
Time End mRO.
Time Module mR:=  goose_refinement mRT mRO.
Time Import mR.
Time
Lemma mail_crash_refinement_seq {T} \207\1311c \207\1311a esa esc :
  mRT.init_absr \207\1311a \207\1311c
  \226\134\146 wf_client_seq esa
    \226\134\146 compile_rel_proc_seq mail_impl esa esc
      \226\134\146 \194\172 proc_exec_seq Mail.l esa (rec_singleton (Ret ())) (1, \207\1311a) Err
        \226\134\146 \226\136\128 \207\1312c (res : T),
            proc_exec_seq GoLayer.Go.l esc (rec_singleton MailServer.Recover)
              (1, \207\1311c) (Val \207\1312c res)
            \226\134\146 \226\136\131 \207\1312a,
                proc_exec_seq Mail.l esa (rec_singleton (Ret tt)) 
                  (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (apply mR.R.crash_refinement_seq).
Time Qed.
Time Print Assumptions mail_crash_refinement_seq.
