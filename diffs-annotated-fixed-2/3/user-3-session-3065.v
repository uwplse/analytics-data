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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8RNjmf"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqaIVHDi"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsgunyn"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVuvULk"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Context {gm : GoModel}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq5B1JEB"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrABeE1"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Context {gmWf : GoModelWf gm}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq5Ul19P"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqo5xQ4U"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition init_absr sa sc := Mail.initP sa \226\136\167 init_base sc.
Definition \206\163 : gFunctors :=
  #[ @goose\206\163 gm gmWf; @cfg\206\163 Mail.Op Mail.l; ghost_map\206\163 ghost_init_statusC;
  ghost_map\206\163 contentsC; gen_heap\206\163 string Filesys.FS.Inode].
Existing Instance subG_goosePreG.
Existing Instance subG_cfgPreG.
Definition OpT := Mail.Op.
Definition \206\155a := Mail.l.
Definition impl := mail_impl.
Instance from_exist_left_sep'  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist ((\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \206\166 a \226\136\151 Q)%I).
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
Definition exec_inv :=
  fun H1 H2 => (\226\136\131 hGTmp, @ExecInv gm _ \206\163 H2 H1 _ _ hGTmp)%I.
Definition exec_inner :=
  fun H1 H2 => (\226\136\131 hGTmp, @ExecInner gm _ \206\163 H2 H1 _ _ hGTmp)%I.
Definition crash_inner := fun H1 H2 => @CrashInner gm _ \206\163 H2 H1 _ _.
Definition crash_param := fun (_ : @cfgG OpT \206\155a \206\163) (_ : gooseG gm \206\163) => gname.
Definition crash_inv := fun H1 H2 \206\179 => @CrashInv _ _ \206\163 H2 H1 _ _ \206\179.
Definition crash_starter :=
  fun (H1 : @cfgG OpT \206\155a \206\163) H2 \206\179 => @CrashStarter _ _ \206\163 H2 \206\179.
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
(destruct Hinitc
  as (Hheap', (Hrange', (Hspool, (Hdirs, (Hlocks1, Hlocks2)))))).
(assert
  (dom (gset string) \207\1311c.(fs).(dirents) =
   set_map UserDir (dom (gset uint64) \207\1311a.(messages)) \226\136\170 {[SpoolDir]}) 
  as ->; auto).
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
Lemma init_base_dirs_empty \207\131 dir x :
  init_base \207\131 \226\134\146 \207\131.(fs).(dirents) !! dir = Some x \226\134\146 x = \226\136\133.
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
Lemma einv_persist :
  forall {H1 : @cfgG OpT \206\155a \206\163} {H2}, Persistent (exec_inv H1 H2).
Proof.
(apply _).
Qed.
Lemma cinv_persist :
  forall {H1 : @cfgG OpT \206\155a \206\163} {H2} P, Persistent (crash_inv H1 H2 P).
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
Lemma refinement_base_triples : refinement_base_triples_type.
Proof.
(intros ? ? ? ? j K Hctx p p' Hcompile).
iIntros "(Hj&Hreg&Hexec)".
iDestruct "Hexec" as ( hGTmp ) "Hexec".
(inversion Hcompile; inj_pair2).
-
iApply (open_refinement with "[$]").
iIntros "!>".
(iIntros ( ? ) "(?&?)"; iFrame).
-
iApply (pickup_refinement with "[$]").
iIntros "!>".
(iIntros ( ? ) "(?&?)"; iFrame).
-
iApply (deliver_refinement with "[$]").
iIntros "!>".
(iIntros ( ? ) "(?&?)"; iFrame).
-
iApply (delete_refinement with "[$]").
iIntros "!>".
(iIntros ( ? ) "(?&?)"; iFrame).
-
iApply (lock_refinement with "[$]").
iIntros "!>".
(iIntros ( ? ) "(?&?)"; iFrame).
-
iApply (unlock_refinement with "[$]").
iIntros "!>".
(iIntros ( ? ) "(?&?)"; iFrame).
-
iDestruct "Hexec" as ( \206\147 \206\179 ) "(#Hsource&#Hinv)".
iInv "Hinv" as "H".
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iApply (data_op_refinement j K with "[$]").
{
solve_ndisj.
}
iIntros ( v ) "!> H".
iDestruct "H" as ( h' ) "(Hj&Hreg&Hstate&Hheap)".
iModIntro.
iFrame.
iNext.
iExists _.
iFrame.
Qed.
Lemma exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx.
Proof.
(intros).
iIntros "H".
iDestruct "H" as ( hGTmp ? ? ) "($&?)".
Qed.
Lemma recv_triple : recv_triple_type.
Proof.
(red).
(intros H1 H2 param).
iIntros "(Hrest&Hreg&Hstarter)".
iDestruct "Hrest" as ( \206\147 \206\179 ) "(#Hsource&#Hinv)".
iDestruct "Hstarter" as ( tmps ) "(Htmps_frag&Hlock)".
wp_bind.
wp_bind.
iApply (wp_list_start with "[$]").
iIntros "!> Hlock".
iInv "Hinv" as "H".
iDestruct "H" as ( \207\131 ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
iDestruct "Htmp" as ( tmps_map ) "(Hdir&Hauth&Hpaths)".
iDestruct (@ghost_var_agree (discreteC (gset string)) \206\163 with "Hauth [$]") as
 % Heq_dom.
iApply (wp_list_finish with "[$]").
iIntros ( s ltmps ) "!> (Hltmps&Hs&Htmps&Hlock)".
iExists _.
iSplitL "Hstate Hmsgs Hheap Hauth Htmps Hpaths".
{
iFrame.
iExists _.
by iFrame.
}
iModIntro.
iDestruct "Hltmps" as % Hltmps.
(assert (tmps = tmps \226\136\150 list_to_set (take 0 ltmps)) as ->).
{
by rewrite difference_empty_L.
}
iDestruct (slice_mapsto_len with "Hs") as % ->.
(assert (Hlen : 0 <= length ltmps) by lia).
revert Hlen.
(remember 0 as i eqn:Heq_i ).
(intros Hlen).
rewrite [a in S a]Heq_i.
clear Heq_i.
iL\195\182b as "IH" forall ( i Hlen ).
wp_loop.
(destruct equal as [Heqlen| Hneq]).
-
iClear "IH".
subst.
rewrite firstn_all.
wp_ret.
wp_ret.
iNext.
iInv "Hinv" as "H" "_".
clear \207\131.
iDestruct "H" as ( \207\131 ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
iApply (fupd_mask_weaken _ _).
{
solve_ndisj.
}
iExists _ , _.
iFrame.
iSplitL "".
{
iPureIntro.
(do 2 eexists; split; econstructor).
}
iClear "Hsource".
iIntros ( ? ? ? ) "(#Hsource&Hstate)".
iDestruct "Htmp" as ( tmps_map' ) "(Hdir&Hauth&Hpaths)".
iDestruct (@ghost_var_agree (discreteC (gset string)) \206\163 with "[$] [$]") as %
 Heq_dom.
(rewrite <- Heq_dom).
iMod (gen_heap_init tmps_map') as ( hGTmp ) "Htmp".
iExists hGTmp , \206\147 , \206\179 , _.
iFrame.
iSplitL "".
{
eauto.
}
iSplitL "Hmsgs".
{
by iApply MsgsInv_crash_set_false.
}
iSplitL "".
{
iModIntro.
by iApply big_sepDM_empty.
}
iExists _.
by iFrame.
-
wp_bind.
(<ssreflect_plugin::ssrtclseq@0>
 destruct (nth_error ltmps i) as [curr_name| ] eqn:Heq_curr_name ; last 
 first).
{
exfalso.
(eapply nth_error_Some; eauto).
(inversion Hlen; try congruence; try lia).
}
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_sliceRead with "[$]") ; first 
 eauto).
iIntros "!> Hs".
wp_bind.
iInv "Hinv" as "H".
clear \207\131.
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iDestruct "Htmp" as ( tmps_map' ) "(Hdir&Hauth&Hpaths)".
iDestruct (@ghost_var_agree (discreteC (gset string)) \206\163 with "[$] [$]") as %
 Heq_dom'.
rewrite Heq_dom'.
(assert (Hcurr_in : curr_name \226\136\136 tmps \226\136\150 list_to_set (take i ltmps))).
{
(apply elem_of_difference; split).
-
rewrite -Heq_dom.
(apply elem_of_elements).
rewrite -Hltmps.
(apply elem_of_list_In).
(eapply nth_error_In; eauto).
-
rewrite elem_of_list_to_set.
rewrite elem_of_list_In.
(assert (HNoDup : NoDup ltmps)).
{
rewrite Hltmps.
(apply NoDup_elements).
}
(eapply nth_error_split in Heq_curr_name as (l1, (l2, (Hsplit, Hlen')))).
rewrite Hsplit.
rewrite -Hlen' take_app.
rewrite Hsplit in  {} HNoDup.
(apply NoDup_app in HNoDup as (?, (Hnotin, ?))).
(intros Hin).
(eapply Hnotin).
{
(apply elem_of_list_In).
eauto.
}
by left.
}
(assert (\226\136\131 v, tmps_map' !! curr_name = Some v) as (inode, Hcurr_inode)).
{
rewrite -Heq_dom' in  {} Hcurr_in.
(apply elem_of_dom in Hcurr_in as (v, ?)).
eauto.
}
(iDestruct (big_sepM_delete with "Hpaths") as "(Hcurr&Hpaths)"; eauto).
iApply (wp_delete with "[$]").
iIntros "!> (Hdir&Hdirlock)".
iMod (@ghost_var_update (discreteC (gset string)) with "Hauth [$]") as
 "(Hauth&Hfrag)".
iSplitL "Hstate Hmsgs Hheap Hpaths Hdir Hauth".
{
iExists _.
iFrame.
iModIntro.
iNext.
iExists _.
iFrame.
rewrite dom_delete_L.
rewrite Heq_dom'.
iFrame.
}
wp_ret.
iModIntro.
iNext.
iApply ("IH" with "[] [$] [Hfrag] [$] [$]").
{
iPureIntro.
(inversion Hlen; try congruence; try lia).
}
rewrite dom_delete_L Heq_dom'.
rewrite difference_difference_L.
(<ssreflect_plugin::ssrtclseq@0>
 assert
  (tmps \226\136\150 list_to_set (take (i + 1) ltmps) =
   tmps \226\136\150 (list_to_set (take i ltmps) \226\136\170 {[curr_name]})) 
  as -> ; last  by auto).
f_equal.
(eapply nth_error_split in Heq_curr_name as (l1, (l2, (Hsplit, Hlen')))).
rewrite Hsplit -Hlen' take_app.
rewrite firstn_app_2 //= firstn_O.
rewrite list_to_set_app_L //= right_id_L //.
Unshelve.
(eapply sigPtr_eq_dec).
Qed.
Lemma init_wf : init_wf_type.
Proof.
(red).
rewrite /init_absr /initP /init_base.
intuition.
Qed.
Lemma init_exec_inner : init_exec_inner_type.
Proof.
clear.
iIntros ( \207\1311a \207\1311c Hinit ).
iIntros ( ? ? ) "(Hdirs&Hroot&Hdirlocks&Hsrc&Hstate&Hglobal)".
(pose proof (init_dirs _ _ Hinit) as Hdirs).
(destruct Hinit as (Hinita, Hinitc)).
iMod (gen_heap_init (\226\136\133 : gmap string Inode)) as ( hGTmp ) "Htmp".
iExists hGTmp.
iMod (ghost_var_alloc (A:=@ghost_init_statusC mRT.gm mRT.gmWf) Uninit) as "H".
iDestruct "H" as ( \206\179 ) "(Hauth&Hfrag)".
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\1311a.(messages) (\206\187 _ _, \226\136\133)) as "H".
iDestruct "H" as ( \206\147 H\206\147dom ) "H\206\147".
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\1311a.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147 !! k = Some \206\1790\226\140\157)%I
 with "[H\206\147]" as "#H\206\147'".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
iIntros ( ? ? ? ) "H".
(iDestruct "H" as ( ? ) "(?&?)"; eauto).
}
iExists \206\147 , \206\179 , \207\1311a.
iFrame.
(assert (SpoolDir \226\136\136 dom (gset string) \207\1311c.(fs).(dirents))).
{
rewrite /init_base in  {} Hinitc.
intuition.
(apply elem_of_dom).
(eexists; eauto).
}
iSplitL "".
{
iPureIntro.
(destruct Hinita as (?, (->, ?)); auto).
}
(iDestruct (big_opS_delete with "Hdirlocks") as "(Hlock&Hdirlocks)"; eauto).
iDestruct (big_opM_delete with "Hdirs") as "(Hspool&Hdirs)".
{
rewrite /init_base in  {} Hinitc.
intuition.
eauto.
}
iSplitR "Htmp Hlock Hspool".
{
rewrite /MsgsInv.
iExists [].
rewrite /initP in  {} Hinita.
(destruct Hinita as (Hheap, (Hopen, Hrange))).
rewrite Hopen.
iFrame.
iSplitL "Hroot".
{
iModIntro.
rewrite /RootDirInv.
(<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  first).
-
iPureIntro.
(<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>uid).
(destruct (Hrange uid)).
(split; intros).
*
(apply elem_of_dom; eexists; eauto).
*
(apply not_elem_of_dom; eauto).
-
rewrite /init_base in  {} Hinitc.
rewrite Hdirs.
eauto.
}
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Hdirs Hdirlocks" ; last  first).
{
rewrite -dom_delete_L.
iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
(<ssreflect_plugin::ssrtclseq@0> iAssert
 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\1311a.(messages), MsgInv \206\147 [] uid (MUnlocked, \226\136\133) false)%I
 with "[Hdirs Hdirlocks]" as "H" ; last  first).
{
iModIntro.
iApply (big_sepM_mono with "H").
iIntros ( k x Hin ) "H".
iDestruct "H" as ( ? \206\179uid ) "(H1&H2&H3)".
iExists _ , _.
iFrame.
(<ssreflect_plugin::ssrtclseq@0> assert (x = (MUnlocked, \226\136\133)) as -> ; last  by
 auto).
(destruct (lt_dec k 100) as [Hlt| Hnlt]).
*
(destruct (Hrange k) as (Hrange1, ?)).
(<ssreflect_plugin::ssrtclseq@0> feed pose proof Hrange1 ; first  by lia).
congruence.
*
(destruct (Hrange k) as (?, Hgt)).
(<ssreflect_plugin::ssrtclseq@0> feed pose proof Hgt ; first  by lia).
congruence.
}
iAssert ([\226\136\151 map] k\226\134\166y \226\136\136 base.delete SpoolDir \207\1311c.(fs).(dirents), k \226\134\166 \226\136\133)%I with
 "[Hdirs]" as "Hdirs".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
iIntros ( dir x Hin ) "Hk".
(cut (x = \226\136\133)).
{
(intros ->).
by rewrite dom_empty_L.
}
(apply lookup_delete_Some in Hin as (Hneq, Hlookup)).
(destruct (Hinitc) as (?, (Hrange', _))).
(eapply init_base_dirs_empty; eauto).
}
(assert
  (Hdirs_delete :
   dom (gset string) (map_delete SpoolDir \207\1311c.(fs).(dirents)) =
   set_map UserDir (dom (gset uint64) \207\1311a.(messages)))).
{
rewrite dom_delete_L Hdirs.
set_solver +.
}
move : {}Hdirs_delete {}.
rewrite /base.delete.
(<ssreflect_plugin::ssrtclintros@0>
 generalize (map_delete SpoolDir \207\1311c.(fs).(dirents)) =>dirs).
(<ssreflect_plugin::ssrtclintros@0> generalize \207\1311a.(messages) =>msgs).
(<ssreflect_plugin::ssrtclintros@0> clear Hrange Hdirs Hheap H =>Hdom).
iInduction msgs as [| k i m] "IH" using map_ind forall ( dirs Hdom ).
{
by iApply big_sepM_empty.
}
rewrite big_sepM_insert //.
rewrite big_sepM_insert //.
(assert (\226\136\131 v, dirs !! UserDir k = Some v) as (v, Hin)).
{
rewrite dom_insert_L in  {} Hdom.
(assert (Hin : UserDir k \226\136\136 dom (gset string) dirs)).
{
set_solver.
}
(apply elem_of_dom in Hin).
eauto.
}
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_delete with "Hdirlocks")
 as "(Hlock&Hdirlocks)" ; first  eauto).
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_delete with "Hdirs") as
 "(Hdir&Hdirs)" ; first  eauto).
iDestruct "H\206\147'" as "(Hghost&H\206\147')".
iSplitL "Hlock Hdir Hghost".
{
iDestruct "Hghost" as ( \206\179uid ) "H".
iExists (zeroValue _) , \206\179uid.
iFrame.
(simpl).
rewrite dom_empty_L.
iFrame.
(iSplitL ""; auto).
}
iApply ("IH" with "[] [$] [$] [$]").
iPureIntro.
rewrite dom_insert_L in  {} Hdom.
rewrite dom_delete_L.
rewrite Hdom.
(assert
  (Hnin : UserDir k \226\136\137 (set_map UserDir (dom (gset uint64) m) : gset string))).
{
rewrite elem_of_map.
(intros (k0, (Heq, Hin'))).
(apply string_app_inj, uint64_to_string_inj in Heq).
subst.
(apply elem_of_dom in Hin' as (?, ?); congruence).
}
clear - Hnin.
rewrite set_map_union_singleton.
rewrite -leibniz_equiv_iff.
rewrite difference_union_distr_l.
rewrite difference_diag_L left_id.
rewrite difference_disjoint //.
rewrite disjoint_singleton_r.
auto.
}
iExists _.
iFrame.
iFrame.
(iSplitL ""; auto).
iModIntro.
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
iIntros ( ? ? ? ) "H".
iDestruct "H" as ( \206\179uid ) "(?&?&?)".
iExists _.
iFrame.
iExists _ , _.
iFrame.
}
{
iSplitL "".
-
rewrite /HeapInv.
rewrite /initP in  {} Hinita.
(destruct Hinita as (->, ?)).
(simpl).
iModIntro.
by iApply big_sepDM_empty.
-
iExists \226\136\133.
iFrame.
by iApply big_sepM_empty.
}
Unshelve.
(apply sigPtr_eq_dec).
Qed.
Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Proof.
iIntros ( ? ? ) "H".
iDestruct "H" as ( hGtmp_old ) "Hrest".
iDestruct "Hrest" as ( \206\147old \206\179old ) "(#Hsource&#Hinv)".
iInv "Hinv" as "H" "_".
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iApply (fupd_mask_weaken _ _).
{
solve_ndisj.
}
iDestruct "Hmsgs" as ( ? ) "(_&>Hroot&Hinit&Hmsgs)".
iDestruct (big_sepM_mono with "Hmsgs") as "Hmsgs".
{
iIntros ( ? ? ? ).
iApply MsgInv_weaken.
}
iDestruct "Hmsgs" as ">Hmsgs".
iIntros ( ? ? ? ? ? ) "(Hroot'&Hglobal)".
iDestruct "Hroot'" as ( S ) "(Hroot'&Hdirlocks)".
iDestruct "Hroot" as "(Hroot&%)".
iDestruct (@ghost_var_agree2 (discreteC (gset string)) _ with "Hroot Hroot'")
 as % Heq_dom.
iDestruct "Htmp" as ( tmp_map ) "(Hdir&_&_&Hpaths)".
iMod (gen_heap_init (tmp_map : gmap string Inode)) as ( hGTmp ) "Htmp".
iMod (@ghost_var_alloc (@ghost_init_statusC _ mRT.gmWf) _ _ _ _ Uninit) as
 "H".
iDestruct "H" as ( \206\179 ) "(Hauth&Hfrag)".
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\131.(messages) (\206\187 _ _, \226\136\133)) as "H".
iDestruct "H" as ( \206\147 H\206\147dom ) "H\206\147".
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\131.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147 !! k = Some \206\1790\226\140\157)%I with
 "[H\206\147]" as "#H\206\147'".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
iIntros ( ? ? ? ) "H".
(iDestruct "H" as ( ? ) "(?&?)"; eauto).
}
iMod
 (@ghost_var_alloc (@discreteC (gset string)) _ _ _
    Hex.(@go_fs_inG mRT.gm mRT.gmWf \206\163).(@go_fs_domalg_inG mRT.gm mRT.gmWf \206\163)
    (dom (gset _) tmp_map)) as "H".
iDestruct "H" as ( \206\179tmp ) "(Hauth_tmp&Hfrag_tmp)".
iModIntro.
iExists \206\179tmp , \206\147 , \206\179 , _.
iFrame.
(rewrite <- Heq_dom).
iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
{
by apply elem_of_union_r, elem_of_singleton.
}
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Hfrag_tmp Hspoollock" ; last 
 first).
{
iExists _.
(iSplitL "Hfrag_tmp"; auto).
}
iExists [].
rewrite /HeapInv.
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Htmp Hdir Hauth_tmp Hpaths" ; last 
 first).
{
(iSplitL ""; auto).
iExists _.
iFrame.
}
(iSplitL ""; auto).
iSplitL "H\206\147".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
iIntros ( ? ? ? ) "H".
iDestruct "H" as ( \206\179uid ? ) "(?&?)".
iExists _.
(iSplitL ""; auto).
iExists _ , _.
iFrame.
}
iClear "Hheap".
(assert
  (((set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
    \226\136\150 {[SpoolDir]}
      : gset string) = set_map UserDir (dom (gset uint64) \207\131.(messages)))
  as ->).
{
set_solver.
}
(<ssreflect_plugin::ssrtclseq@0> rewrite big_opS_fmap ; last  first).
{
rewrite /UserDir.
(intros ? ? Heq).
(apply string_app_inj, uint64_to_string_inj in Heq).
auto.
}
iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
iDestruct (big_sepM_sep with "[Hdirlocks Hmsgs]") as "Hmsgs".
{
iFrame.
}
iDestruct (big_sepM_sep with "[Hmsgs]") as "Hmsgs".
{
iFrame.
iFrame "H\206\147'".
}
iApply (big_sepM_mono with "Hmsgs").
iIntros ( k x Hlookup ) "((H1&H2)&H3)".
iDestruct "H3" as % Hlookup'.
(destruct Hlookup' as (\206\179', ?)).
iDestruct "H1" as ( ? ? ) "(_&(?&?&?))".
iExists _ , _.
(iSplitL ""; eauto).
(iSplitL ""; eauto).
iFrame.
auto.
Unshelve.
(apply (zeroValue _)).
Qed.
Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Proof.
iIntros ( ? ? \206\179tmp ) "Hcrash".
iDestruct "Hcrash" as ( ? ? ) "(#Hsrc&#Hinv)".
iInv "Hinv" as "H" "_".
iDestruct "H" as ( \207\131 ) "(>Hstate&>Hmsgs&>Hheap&>Htmp)".
iApply (fupd_mask_weaken _ _).
{
solve_ndisj.
}
iDestruct "Hmsgs" as ( ? ) "(_&Hroot&Hinit&Hmsgs)".
iIntros ( ? ? ? ? ? ) "(Hroot'&Hglobal)".
iDestruct "Hroot'" as ( S ) "(Hroot'&Hdirlocks)".
iDestruct "Hroot" as "(Hroot&%)".
iDestruct (@ghost_var_agree2 (discreteC (gset string)) _ with "Hroot Hroot'")
 as % Heq_dom.
iDestruct "Htmp" as ( tmp_map ) "(Hdir&_&Hpaths)".
iMod (gen_heap_init (tmp_map : gmap string Inode)) as ( hGTmp ) "Htmp".
iMod (ghost_var_alloc (A:=@ghost_init_statusC _ mRT.gmWf) Uninit) as "H".
iDestruct "H" as ( \206\179 ) "(Hauth&Hfrag)".
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\131.(messages) (\206\187 _ _, \226\136\133)) as "H".
iDestruct "H" as ( \206\147 H\206\147dom ) "H\206\147".
iMod
 (@ghost_var_alloc (@discreteC (gset string)) _ _ _
    Hex.(@go_fs_inG mRT.gm mRT.gmWf \206\163).(@go_fs_domalg_inG mRT.gm mRT.gmWf \206\163)
    (dom (gset _) tmp_map)) as "H".
iDestruct "H" as ( \206\179tmp' ) "(Hauth_tmp&Hfrag_tmp)".
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\131.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147 !! k = Some \206\1790\226\140\157)%I with
 "[H\206\147]" as "#H\206\147'".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
iIntros ( ? ? ? ) "H".
(iDestruct "H" as ( ? ) "(?&?)"; eauto).
}
iModIntro.
iExists \206\179tmp' , \206\147 , \206\179 , _.
iFrame.
(rewrite <- Heq_dom).
iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
{
by apply elem_of_union_r, elem_of_singleton.
}
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Hfrag_tmp Hspoollock" ; last 
 first).
{
iExists _.
iFrame.
}
iExists [].
rewrite /HeapInv.
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Htmp Hdir Hauth_tmp Hpaths" ; last 
 first).
{
iExists _.
iFrame.
}
(iSplitL ""; auto).
iSplitL "H\206\147".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
iIntros ( ? ? ? ) "H".
iDestruct "H" as ( \206\179uid ? ) "(?&?)".
iExists _.
(iSplitL ""; auto).
iExists _ , _.
iFrame.
}
(assert
  (((set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
    \226\136\150 {[SpoolDir]}
      : gset string) = set_map UserDir (dom (gset uint64) \207\131.(messages)))
  as ->).
{
set_solver.
}
(<ssreflect_plugin::ssrtclseq@0> rewrite big_opS_fmap ; last  first).
{
rewrite /UserDir.
(intros ? ? Heq).
(apply string_app_inj, uint64_to_string_inj in Heq).
auto.
}
iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
iDestruct (big_sepM_sep with "[Hdirlocks Hmsgs]") as "Hmsgs".
{
iFrame.
}
iDestruct (big_sepM_sep with "[Hmsgs]") as "Hmsgs".
{
iFrame.
iFrame "H\206\147'".
}
iApply (big_sepM_mono with "Hmsgs").
iIntros ( k x Hlookup ) "((H1&H2)&H3)".
iDestruct "H3" as % Hlookup'.
(destruct Hlookup' as (\206\179', ?)).
iDestruct "H1" as ( ? ? ) "(_&(?&?&?&?&?))".
iExists _ , _.
(iSplitL ""; eauto).
(iSplitL ""; eauto).
iFrame.
auto.
Unshelve.
(apply (zeroValue _)).
Qed.
Lemma crash_inner_inv : crash_inner_inv_type.
Proof.
iIntros ( ? ? ) "(H1&H2)".
iDestruct "H1" as ( Hinv \206\179tmp ) "(H&Hstarter)".
iDestruct "H" as ( ? ? ? ) "(?&?&?)".
iExists _.
iFrame.
iExists _ , _.
iFrame.
(<ssreflect_plugin::ssrtclseq@0> iMod
 (@inv_alloc \206\163 go_invG execN _ _ with "[-]") ; last  eauto).
iNext.
iExists _.
iFrame.
Qed.
Lemma exec_inner_inv : exec_inner_inv_type.
Proof.
iIntros ( ? ? ) "(H1&H2)".
iDestruct "H1" as ( Hinv hGTmp ? ? ? Hclosed ) "(Hstate&Hmsgs&Heap&Htmps)".
iExists hGTmp.
iExists _ , _.
iFrame.
(<ssreflect_plugin::ssrtclseq@0> iMod
 (@inv_alloc \206\163 go_invG execN _ _ with "[-]") ; last  eauto).
iNext.
iExists _.
iFrame "Hstate Heap Htmps".
rewrite /MsgsInv.
iDestruct "Hmsgs" as ( ? ) "(Hglobal&Hroot&Hinit&Hmsgs)".
iExists _.
iFrame "Hglobal Hroot Hinit".
rewrite Hclosed.
eauto.
Qed.
Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Proof.
iIntros ( ? ? ) "_ H".
iDestruct "H" as ( hGTmp \206\147 \206\179 ) "Hrest".
iDestruct "Hrest" as "(#Hsource&#Hinv)".
iInv "Hinv" as "H" "_".
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iDestruct "Hmsgs" as ( ? ) "(_&>Hroot&Hinit&Hmsgs)".
iDestruct (big_sepM_mono with "Hmsgs") as "Hmsgs".
{
iIntros ( ? ? ? ).
iApply MsgInv_weaken.
}
iDestruct "Hmsgs" as ">Hmsgs".
iApply (fupd_mask_weaken _ _).
{
solve_ndisj.
}
iExists _ , _.
iFrame.
iSplitL "".
{
iPureIntro.
(do 2 eexists).
(split; econstructor).
}
iDestruct "Hroot" as "(Hroot&%)".
iClear "Hsource".
iIntros ( ? ? ? ? ? ? ? ) "(#Hsource&Hstate&Hdirlocks&Hglobal)".
iDestruct "Htmp" as ( tmps_map' ) "(Hdir&Hdirlock&Hauth'&Hpaths)".
iMod (gen_heap_init tmps_map') as ( hGTmp' ) "Htmp".
iMod (@ghost_var_alloc (@ghost_init_statusC _ mRT.gmWf) _ _ _ _ Uninit) as
 "H".
iDestruct "H" as ( \206\179' ) "(Hauth&Hfrag)".
iMod (ghost_var_bulk_alloc (A:=contentsC) \207\131.(messages) (\206\187 _ _, \226\136\133)) as "H".
iDestruct "H" as ( \206\147' H\206\147dom ) "H\206\147".
iDestruct "Hdirlocks" as ( S ) "(Hroot'&Hdirlocks)".
iDestruct (@ghost_var_agree2 (discreteC (gset string)) _ with "Hroot Hroot'")
 as % Heq_dom.
iAssert ([\226\136\151 map] k\226\134\166_ \226\136\136 \207\131.(messages), \226\136\131 \206\1790 : gname, \226\140\156\206\147' !! k = Some \206\1790\226\140\157)%I
 with "[H\206\147]" as "#H\206\147'".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
iIntros ( ? ? ? ) "H".
(iDestruct "H" as ( ? ) "(?&?)"; eauto).
}
iExists hGTmp' , \206\147' , \206\179' , _.
iModIntro.
iFrame.
(<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  eauto).
iExists [].
iFrame.
(rewrite <- Heq_dom).
iDestruct (big_sepS_delete with "Hdirlocks") as "(Hspoollock&Hdirlocks)".
{
by apply elem_of_union_r, elem_of_singleton.
}
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Htmp Hdir Hpaths Hspoollock" ;
 last  first).
{
iSplitL "".
{
by iApply big_sepDM_empty.
}
iExists _.
iFrame.
}
(iSplitL ""; auto).
iExists _.
iFrame.
iFrame.
iSplitL "H\206\147".
{
(iSplitL ""; auto).
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  iApply "H\206\147").
iIntros ( ? ? ? ) "H".
iDestruct "H" as ( \206\179uid ? ) "(?&?)".
iExists _.
(iSplitL ""; auto).
iExists _ , _.
iFrame.
}
(assert
  (((set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
    \226\136\150 {[SpoolDir]}
      : gset string) = set_map UserDir (dom (gset uint64) \207\131.(messages)))
  as ->).
{
set_solver.
}
(<ssreflect_plugin::ssrtclseq@0> rewrite big_opS_fmap ; last  first).
{
rewrite /UserDir.
(intros ? ? Heq).
(apply string_app_inj, uint64_to_string_inj in Heq).
auto.
}
iDestruct (big_sepM_dom with "Hdirlocks") as "Hdirlocks".
iDestruct (big_sepM_sep with "[Hdirlocks Hmsgs]") as "Hmsgs".
{
iFrame.
}
iDestruct (big_sepM_sep with "[Hmsgs]") as "Hmsgs".
{
iFrame.
iFrame "H\206\147'".
}
iApply (big_sepM_mono with "Hmsgs").
iIntros ( k x Hlookup ) "((H1&H2)&H3)".
iDestruct "H3" as % Hlookup'.
(destruct Hlookup' as (\206\179'', ?)).
iDestruct "H1" as ( ? ? ) "(_&H)".
iDestruct "H" as "(?&?&?)".
iExists _ , _.
(iSplitL ""; eauto).
(iSplitL ""; eauto).
iFrame.
auto.
Unshelve.
(apply sigPtr_eq_dec).
idtac "Beginning final qed soon.".
(apply (zeroValue _)).
Qed.
End mRO.
(* Auto-generated comment: Succeeded. *)

