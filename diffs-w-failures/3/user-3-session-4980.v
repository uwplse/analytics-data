Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time From Perennial.Examples.MailServer Require Import MailAPI MailAPILemmas.
Time From Perennial.Goose.Examples Require Import MailServer.
Time From Perennial.Goose.Proof Require Import Interp.
Time Require Import Goose.Proof.Interp.
Time From Perennial Require AtomicPair.Helpers.
Time From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Perennial.Goose Require Import Machine.
Time From Perennial.Goose Require Import GoZeroValues.
Time Unset Implicit Arguments.
Time Set Default Proof Using "Type".
Time Section refinement_heap_triples.
Time Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time Import Mail.
Time
Definition HeapInv' (\207\131 : DynMap gmodel.(@Ptr) Data.ptrModel) : 
  iProp \206\163 :=
  big_opDM bi_sep
    (\206\187 T p v,
       match fst v, T with
       | ReadLocked n, Ptr.Heap _ =>
           Count_Typed_Heap.mapsto (hG:=go_heap_inG) p (S n) Unlocked (snd v)
       | _, _ =>
           Count_Typed_Heap.mapsto (hG:=go_heap_inG) p O (fst v) (snd v)
       end \226\136\151 \226\140\156p \226\137\160 gmodel.(@nullptr) _\226\140\157)%I \207\131.
Time
Definition HeapInv (\207\131 : Mail.State) : iProp \206\163 :=
  big_opDM bi_sep
    (\206\187 T p v,
       match fst v, T with
       | ReadLocked n, Ptr.Heap _ =>
           Count_Typed_Heap.mapsto (hG:=go_heap_inG) p (S n) Unlocked (snd v)
       | _, _ =>
           Count_Typed_Heap.mapsto (hG:=go_heap_inG) p O (fst v) (snd v)
       end \226\136\151 \226\140\156p \226\137\160 gmodel.(@nullptr) _\226\140\157)%I (Data.allocs \207\131.(heap)).
Time #[global]Instance HeapInv_Timeless  \207\131: (Timeless (HeapInv \207\131)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> apply big_sepDM_timeless ; first  apply _).
Time (intros [] ? ([], ?); apply _).
Time Qed.
Time
Lemma HeapInv_agree_slice {T} \207\131 sli alloc alloc' (vs vs' : List.list T)
  status q :
  Data.getAlloc sli.(slice.ptr) \207\131.(heap) = Some (status, alloc')
  \226\134\146 Data.getSliceModel sli alloc' = Some vs'
    \226\134\146 sli \226\134\166{ q} (alloc, vs) -\226\136\151 HeapInv \207\131 -\226\136\151 \226\140\156alloc = alloc' \226\136\167 vs = vs'\226\140\157.
Time Proof.
Time iIntros ( ? ? ) "Hsli Hheap".
Time rewrite /HeapInv.
Time
iDestruct (big_sepDM_lookup (dec:=sigPtr_eq_dec) with "Hheap") as
 "(Hlookup&%)".
Time {
Time eauto.
Time }
Time
iAssert (\226\136\131 s q, Count_Typed_Heap.mapsto sli.(slice.ptr) s q alloc')%I with
 "[Hlookup]" as ( ? ? ) "Hlookup".
Time {
Time (destruct status; eauto).
Time }
Time iDestruct "Hsli" as ( ? ? ) "Hsli".
Time
iDestruct (Count_Typed_Heap.mapsto_agree_generic with "[Hsli] Hlookup") as %
 Heq.
Time {
Time eauto.
Time }
Time subst.
Time (iPureIntro; split; auto).
Time (simpl in *).
Time congruence.
Time Qed.
Time
Lemma HeapInv_non_alloc_lock_inv' \207\131 lk q mode :
  q >= 0
  \226\134\146 HeapInv' \207\131
    -\226\136\151 lock_mapsto lk q mode -\226\136\151 \226\140\156getDyn \207\131 lk = None /\ lk \226\137\160 nullptr _\226\140\157.
Time Proof.
Time iIntros ( ? ) "Hheap (%&Hp)".
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; last  auto).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (getDyn \207\131 lk) as [v| ] eqn:Heq_get
 ; last  by done).
Time iExFalso.
Time
(iPoseProof
  (big_sepDM_lookup (T:=Ptr.Lock) (dec:=sigPtr_eq_dec) with "Hheap") as
  "(Hheap&%)"; eauto).
Time
(destruct v as ([], ?); iApply
  (Count_Typed_Heap.mapsto_valid_generic with "[Hp] Hheap"); 
  try iFrame; eauto with lia).
Time Qed.
Time
Lemma HeapInv_non_alloc_inv' {A} \207\131 p q (ls : List.list A) :
  q >= 0 \226\134\146 HeapInv' \207\131 -\226\136\151 p \226\134\166{ q} ls -\226\136\151 \226\140\156getDyn \207\131 p = None /\ p \226\137\160 nullptr _\226\140\157.
Time Proof.
Time iIntros ( ? ) "Hheap Hp".
Time iDestruct "Hp" as "(%&Hp)".
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; last  auto).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (getDyn \207\131 p) as [v| ] eqn:Heq_get ;
 last  by done).
Time iExFalso.
Time rewrite /HeapInv.
Time rewrite /Data.getAlloc in  {} Heq_get.
Time
(iPoseProof
  (big_sepDM_lookup (T:=Ptr.Heap A) (dec:=sigPtr_eq_dec) with "Hheap") as
  "(Hheap&%)"; eauto).
Time
(destruct v as ([], ?); iApply
  (Count_Typed_Heap.mapsto_valid_generic with "[Hp] Hheap"); 
  try iFrame; eauto with lia).
Time Qed.
Time
Lemma HeapInv_non_alloc_inv {A} \207\131 p q (ls : List.list A) :
  q >= 0
  \226\134\146 HeapInv \207\131
    -\226\136\151 p \226\134\166{ q} ls -\226\136\151 \226\140\156Data.getAlloc p \207\131.(heap) = None /\ p \226\137\160 nullptr _\226\140\157.
Time Proof.
Time iIntros ( ? ) "Hheap Hp".
Time (iDestruct (HeapInv_non_alloc_inv' with "[$] [$]") as % Heq; eauto).
Time Qed.
Time
Lemma take_drop_sublist_inv {A} (l : List.list A) 
  a n1 n2 : take n2 (drop n1 l) = a :: l \226\134\146 False.
Time Proof.
Time (intros Htake).
Time (apply (f_equal length) in Htake).
Time rewrite take_length drop_length //= in  {} Htake.
Time lia.
Time Qed.
Time
Lemma take_drop_all_inv {A : Type} (l : List.list A) 
  n1 n2 : n1 \226\137\164 length l \226\134\146 take n2 (drop n1 l) = l \226\134\146 n1 = O.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct l, n1 =>//=).
Time -
Time (inversion 1).
Time -
Time (intros; exfalso; by eapply take_drop_sublist_inv).
Time Qed.
Time
Lemma getSliceModel_full_inv {T} (p : slice.t T) l :
  Data.getSliceModel p l = Some l
  \226\134\146 length l = p.(slice.length) \226\136\167 p.(slice.offset) = 0.
Time Proof.
Time (intros Hget).
Time split.
Time -
Time (eapply getSliceModel_len_inv; eauto).
Time -
Time move : {}Hget {}.
Time rewrite /Data.getSliceModel /sublist_lookup /mguard /option_guard.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by congruence).
Time (inversion 1).
Time (eapply take_drop_all_inv; eauto).
Time lia.
Time Qed.
Time
Lemma data_op_refinement {T1} {T2} j K `{LanguageCtx _ _ T2 Mail.l K}
  (op : Data.Op T1) E \207\131 :
  nclose sourceN \226\138\134 E
  \226\134\146 {{{ j \226\164\135 K (Call (DataOp op))
        \226\136\151 Registered \226\136\151 source_ctx \226\136\151 source_state \207\131 \226\136\151 HeapInv \207\131 }}} 
  Call (GoLayer.DataOp op) @ E {{{ v, RET v; \226\136\131 h,
                                               j \226\164\135 K (Ret v)
                                               \226\136\151 Registered
                                                 \226\136\151 
                                                 source_state
                                                 (RecordSet.set heap 
                                                 (\206\187 _, h) \207\131)
                                                 \226\136\151 
                                                 HeapInv
                                                 (RecordSet.set heap 
                                                 (\206\187 _, h) \207\131)}}}.
Time Proof.
Time iIntros ( HE \206\166 ) "(Hj&Hreg&#Hsource&Hstate&Hheap) H\206\166".
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time rewrite -wp_fupd.
Time (destruct op).
Time -
Time iApply (wp_newAlloc with "[//]").
Time iIntros ( p ) "!> Hp".
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (HeapInv_non_alloc_inv _ _ 0 with "[$] Hp") as % ? ; first  auto).
Time
iMod
 (ghost_step_call _ _ _ p (RecordSet.set heap _ \207\131 : l.(OpState))
 with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time (do 2 eexists).
Time split.
Time **
Time (econstructor; eauto).
Time **
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  econstructor).
Time econstructor.
Time *
Time eauto.
Time }
Time {
Time solve_ndisj.
Time }
Time iModIntro.
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time {
Time rewrite /HeapInv //=.
Time (rewrite big_sepDM_updDyn; try intuition).
Time iFrame.
Time (simpl).
Time (iDestruct "Hp" as "(?&$)"; eauto).
Time }
Time -
Time
iMod (deref_step_inv_do with "Hj Hsource Hstate") as ( s alloc v Heq )
 "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time (destruct Heq as (Heq1, (Heq2, Heq3))).
Time
iDestruct (big_sepDM_lookup_acc (dec:=sigPtr_eq_dec) with "Hheap") as
 "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time (destruct s; try (simpl in Heq2; congruence); simpl).
Time *
Time iApply (wp_ptrDeref' with "Hp").
Time {
Time eauto.
Time }
Time {
Time eauto.
Time }
Time iIntros "!> Hp".
Time iApply "H\206\166".
Time iExists \207\131.(heap).
Time iFrame.
Time (simpl).
Time (destruct \207\131).
Time iFrame "Hstate".
Time iApply "Hheap".
Time by iFrame.
Time *
Time iApply (wp_ptrDeref' with "Hp").
Time {
Time eauto.
Time }
Time {
Time eauto.
Time }
Time iIntros "!> Hp".
Time iApply "H\206\166".
Time iExists \207\131.(heap).
Time iFrame.
Time (simpl).
Time (destruct \207\131).
Time iFrame "Hstate".
Time iApply "Hheap".
Time by iFrame.
Time -
Time (<ssreflect_plugin::ssrtclseq@0> destruct na ; last  first).
Time *
Time
iMod (store_start_step_inv_do j K with "Hj Hsource Hstate") as ( s alloc Heq
 ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time (destruct Heq as (Heq1, Heq2)).
Time iDestruct (@big_sepDM_insert_acc with "Hheap") as "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time (destruct s; try (simpl in Heq2; congruence); simpl; [  ]).
Time iApply (wp_ptrStore_start with "Hp").
Time iIntros "!> Hp".
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time iApply "Hheap".
Time by iFrame.
Time *
Time
iMod (store_finish_step_inv_do j K with "Hj Hsource Hstate") as ( s alloc
 alloc' Heq ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time (destruct Heq as (Heq1, (Heq2, Heq3))).
Time iDestruct (@big_sepDM_insert_acc with "Hheap") as "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time (destruct s; try (simpl in Heq3; congruence); simpl; [  ]).
Time (destruct args).
Time iApply (wp_ptrStore_finish with "Hp").
Time {
Time eauto.
Time }
Time iIntros "!> Hp".
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time iApply "Hheap".
Time by iFrame.
Time -
Time
iMod (slice_append_step_inv j K with "Hj Hsource Hstate") as ( s' alloc vs
 Heq ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time (destruct Heq as (He1, (Heq2, Heq3))).
Time iDestruct (@big_sepDM_delete with "Hheap") as "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time (destruct s'; try (simpl in Heq3; congruence); simpl; [  ]).
Time iApply (wp_sliceAppend with "[Hp]").
Time {
Time iNext.
Time iFrame.
Time iPureIntro.
Time (split; eauto).
Time }
Time iIntros ( p' ) "!> Hp".
Time iDestruct "Hp" as ( Heq ) "Hp".
Time (simpl in Heq).
Time (efeed pose proof @getSliceModel_len_inv as Hlen; eauto).
Time iApply "H\206\166".
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (HeapInv_non_alloc_inv' _ _ 0 with "Hheap Hp") as % ? ; first  auto).
Time (edestruct @getSliceModel_full_inv as (Heqp'1, Heqp'2); eauto).
Time (destruct p' as [ptr ? ?]).
Time (simpl in Heqp'1, Heqp'2).
Time rewrite -Heqp'1 Heqp'2.
Time (simpl).
Time subst.
Time
iMod
 (ghost_step_call _ _ _
    {| slice.ptr := ptr; slice.offset := 0; slice.length := _ |}
    (RecordSet.set heap
       (\206\187 heap,
          RecordSet.set Data.allocs (updDyn ptr (Unlocked, vs ++ [x]))
            (RecordSet.set Data.allocs (deleteDyn s.(slice.ptr)) heap)) \207\131
       : l.(OpState)) with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time (do 2 eexists).
Time split.
Time **
Time non_err.
Time **
Time (simpl).
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  by non_err).
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  by non_err).
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  by non_err).
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  by econstructor).
Time (do 2 eexists; split).
Time econstructor.
Time split.
Time ***
Time intuition.
Time (destruct \207\131).
Time rewrite /Data.getAlloc.
Time (simpl).
Time eauto.
Time ***
Time intuition.
Time ***
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  by econstructor).
Time (simpl).
Time econstructor.
Time *
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time (simpl in *).
Time rewrite app_length (getSliceModel_len_inv _ _ _ Heq2).
Time iFrame.
Time iModIntro.
Time rewrite /HeapInv.
Time (simpl).
Time intuition.
Time (rewrite big_sepDM_updDyn; try iFrame; eauto).
Time (iDestruct "Hp" as "(?&?)"; iFrame; eauto).
Time -
Time ghost_err.
Time err_start.
Time econstructor.
Time -
Time ghost_err.
Time err_start.
Time econstructor.
Time -
Time ghost_err.
Time err_start.
Time econstructor.
Time -
Time ghost_err.
Time err_start.
Time econstructor.
Time -
Time ghost_err.
Time err_start.
Time econstructor.
Time -
Time iApply (wp_newLock_raw with "[//]").
Time iIntros ( p ) "!> Hp".
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (HeapInv_non_alloc_lock_inv' _ _ 0 with "[$] Hp") as % ? ; first  auto).
Time
iMod
 (ghost_step_call _ _ _ p (RecordSet.set heap _ \207\131 : l.(OpState))
 with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time (do 2 eexists).
Time split.
Time **
Time (econstructor; eauto).
Time **
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  econstructor).
Time econstructor.
Time *
Time eauto.
Time }
Time {
Time solve_ndisj.
Time }
Time iModIntro.
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time {
Time rewrite /HeapInv //=.
Time (rewrite big_sepDM_updDyn; try intuition).
Time iFrame.
Time (simpl).
Time (iDestruct "Hp" as "(?&$)"; eauto).
Time }
Time -
Time
iMod (lock_acquire_step_inv j K with "Hj Hsource Hstate") as ( s' )
 "(Heq&Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time iDestruct "Heq" as % Hget.
Time
iDestruct (@big_sepDM_insert_acc _ _ _ _ _ Ptr.Lock with "Hheap") as
 "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time (destruct l0).
Time *
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131') ) "(?&H\207\131'&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131' [Hp]") as %
 [s'' [? Hlock]].
Time {
Time (destruct s'; eauto).
Time }
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time (destruct l0; inversion Htl_err).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclseq@0>
 edestruct (lock_acquire_Reader_success_inv) as (?, ?) ; first  by eauto).
Time inv_step.
Time (destruct s').
Time {
Time (apply Count_Heap.Cinr_included_excl' in Hlock; subst).
Time (simpl in *; congruence).
Time }
Time {
Time (apply Count_Heap.Cinl_included_nat' in Hlock as (m, (?, ?))).
Time subst.
Time
iMod (gen_typed_heap_readlock' Ptr.Lock with "H\207\131' Hp") as ( s' Heq )
 "(H\207\131&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time iModIntro.
Time iApply "H\206\166".
Time
iMod
 (ghost_step_call _ _ _ _ (RecordSet.set heap _ \207\131 : l.(OpState))
 with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time (do 2 eexists).
Time split.
Time **
Time non_err.
Time **
Time (do 2 eexists).
Time *
Time eauto.
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time iApply "Hheap".
Time (simpl).
Time iFrame.
Time eauto.
Time }
Time {
Time (apply Count_Heap.Cinl_included_nat' in Hlock as (m, (?, ?))).
Time subst.
Time
iMod (gen_typed_heap_readlock Ptr.Lock with "H\207\131' Hp") as ( s' Heq ) "(H\207\131&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time iModIntro.
Time iApply "H\206\166".
Time
iMod
 (ghost_step_call _ _ _ _ (RecordSet.set heap _ \207\131 : l.(OpState))
 with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time (do 2 eexists).
Time split.
Time **
Time non_err.
Time **
Time (do 2 eexists).
Time *
Time eauto.
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time iApply "Hheap".
Time (simpl).
Time iFrame.
Time eauto.
Time }
Time *
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131') ) "(?&H\207\131'&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131' [Hp]") as %
 [s'' [? Hlock]].
Time {
Time (destruct s'; eauto).
Time }
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time (destruct l0; inversion Htl_err).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclseq@0>
 edestruct (lock_acquire_Writer_success_inv) as (?, (?, ?)) ; first  by
 eauto; subst).
Time subst.
Time inv_step.
Time (destruct s').
Time {
Time (apply Count_Heap.Cinr_included_excl' in Hlock; subst).
Time (simpl in *; congruence).
Time }
Time {
Time subst.
Time (simpl in *).
Time (apply Count_Heap.Cinl_included_nat in Hlock).
Time lia.
Time }
Time iMod (gen_typed_heap_update Ptr.Lock with "H\207\131' Hp") as "($&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time iModIntro.
Time iApply "H\206\166".
Time
iMod
 (ghost_step_call _ _ _ _ (RecordSet.set heap _ \207\131 : l.(OpState))
 with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time (do 2 eexists).
Time split.
Time **
Time non_err.
Time **
Time (do 2 eexists).
Time *
Time eauto.
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time iApply "Hheap".
Time (simpl).
Time iFrame.
Time eauto.
Time -
Time
iMod (lock_release_step_inv_do j K with "Hj Hsource Hstate") as ( s1 s2
 (He1, He2) ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time
iDestruct (@big_sepDM_insert_acc _ _ _ _ _ Ptr.Lock with "Hheap") as
 "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time (destruct l0).
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_lockRelease_read_raw with "[Hp]")
 ; first  by eauto).
Time {
Time (destruct s1; iFrame; eauto).
Time }
Time iIntros "!> (%&?)".
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time iApply "Hheap".
Time (simpl).
Time (destruct s2; by iFrame).
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> iApply
 (wp_lockRelease_writer_raw with "[Hp]") ; first  by eauto).
Time {
Time (destruct s1; iFrame; eauto).
Time }
Time iIntros "!> (%&?)".
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time iApply "Hheap".
Time (simpl).
Time (destruct s2; by iFrame).
Time -
Time ghost_err.
Time err_start.
Time econstructor.
Time -
Time ghost_err.
Time err_start.
Time econstructor.
Time -
Time
iMod (bytes_to_string_step_inv_do j K with "Hj Hsource Hstate") as ( s alloc
 val (He1, (He2, He3)) ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time
iDestruct
 (big_sepDM_lookup_acc (dec:=sigPtr_eq_dec) (T:=Ptr.Heap byte) with "Hheap")
 as "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time (destruct s; try (simpl in He3; congruence); simpl; [  |  ]).
Time *
Time iApply (wp_bytesToString with "[Hp]").
Time {
Time iNext.
Time iFrame.
Time eauto.
Time }
Time iIntros "!> Hp".
Time iApply "H\206\166".
Time iExists \207\131.(heap).
Time iFrame.
Time (simpl).
Time (destruct \207\131).
Time iFrame "Hstate".
Time iApply "Hheap".
Time iDestruct "Hp" as "(?&?&?)".
Time iFrame.
Time eauto.
Time *
Time iApply (wp_bytesToString with "[Hp]").
Time {
Time iNext.
Time iFrame.
Time eauto.
Time }
Time iIntros "!> Hp".
Time iApply "H\206\166".
Time iExists \207\131.(heap).
Time iFrame.
Time (simpl).
Time (destruct \207\131).
Time iFrame "Hstate".
Time iApply "Hheap".
Time iDestruct "Hp" as "(?&?&?)".
Time iFrame.
Time eauto.
Time -
Time iApply (wp_stringToBytes with "[//]").
Time iIntros ( p ) "!> (Hp&%)".
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (HeapInv_non_alloc_inv' _ _ 0 with "[$] Hp") as % ? ; first  auto).
Time
iMod
 (ghost_step_call _ _ _ p
    ((RecordSet.set heap
        (\206\187 h,
           RecordSet.set Data.allocs
             (updDyn p.(slice.ptr) (Unlocked, string_to_bytes s)) h)) \207\131
       : l.(OpState)) with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time (do 2 eexists).
Time split.
Time **
Time (do 2 eexists).
Time split.
Time ***
Time (do 2 eexists; intuition eauto).
Time ***
Time (do 2 eexists; non_err).
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  by econstructor).
Time econstructor.
Time **
Time (simpl).
Time intuition.
Time subst.
Time (destruct p).
Time (simpl in *).
Time subst.
Time econstructor.
Time *
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time iModIntro.
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time {
Time rewrite /HeapInv //=.
Time (rewrite big_sepDM_updDyn; try intuition).
Time iFrame.
Time (simpl).
Time (iDestruct "Hp" as "(?&$)"; eauto).
Time }
Time -
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131') ) "(?&H\207\131'&?)".
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (inv_step; simpl in *; subst; inv_step).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iFrame.
Time (simpl).
Time inv_step.
Time (inversion H2).
Time subst.
Time (simpl in *).
Time iSplitL "H\207\131'".
Time {
Time (unfold RecordSet.set).
Time (destruct \207\131').
Time (simpl).
Time by iFrame.
Time }
Time iModIntro.
Time
iMod (ghost_step_call _ _ _ e2 _ with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time *
Time by econstructor.
Time *
Time (destruct \207\131; eauto).
Time }
Time {
Time solve_ndisj.
Time }
Time iModIntro.
Time iApply "H\206\166".
Time iExists _.
Time iFrame.
Time (destruct \207\131; simpl).
Time iFrame.
Time Time Qed.
Time End refinement_heap_triples.
