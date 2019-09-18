Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time
Require Import OneDiskAPI ReplicatedDiskImpl ReplicatedDisk.WeakestPre
  ReplicatedDisk.RefinementAdequacy.
Time Set Default Proof Using "All".
Time Unset Implicit Arguments.
Time Import agree.
Time From Tactical Require Import UnfoldLemma.
Time Definition addrset := dom (gset nat) init_zero.
Time Opaque init_zero size.
Time Definition addrset_unfold := unfold_lemma addrset.
Time Lemma not_lt_size_not_in_addrset a : \194\172 a < size \226\134\146 a \226\136\137 addrset.
Time Proof.
Time (intros).
Time (apply not_elem_of_dom, init_zero_lookup_ge_None; lia).
Time Qed.
Time Lemma lt_size_in_addrset a : a < size \226\134\146 a \226\136\136 addrset.
Time Proof.
Time (intros).
Time (apply elem_of_dom).
Time eexists.
Time (apply init_zero_lookup_lt_zero; lia).
Time Qed.
Time #[global]Instance odstate_inhaibted : (Inhabited OneDisk.State).
Time Proof.
Time econstructor.
Time exact {| OneDisk.disk_state := init_zero |}.
Time Qed.
Time
Lemma upd_disk_dom a v \207\131 :
  dom (gset nat) (OneDisk.upd_disk a v \207\131).(OneDisk.disk_state) =
  dom (gset nat) \207\131.(OneDisk.disk_state).
Time Proof.
Time rewrite /OneDisk.upd_disk //= /OneDisk.upd_default //=.
Time (destruct (_ !! a) as [?| ] eqn:Hlookup).
Time -
Time rewrite dom_insert_L.
Time (assert (a \226\136\136 dom (gset nat) \207\131.(OneDisk.disk_state))).
Time {
Time (apply elem_of_dom; eauto).
Time }
Time set_solver.
Time -
Time auto.
Time Qed.
Time Section gen_heap.
Time Context `{hG : gen_heapG L V \206\163}.
Time
Lemma gen_heap_init_to_bigOp \207\131 :
  own (gen_heap_name hG) (\226\151\175 to_gen_heap \207\131) -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i 1 v.
Time Proof.
Time (induction \207\131 using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap m) \226\136\151 mapsto i 1 x)%I with
 "[Hown]" as "[Hrest $]".
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time rewrite to_gen_heap_insert.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (insert_singleton_op (to_gen_heap m) i (1%Qp, to_agree x)) ; last  by
 apply lookup_to_gen_heap_None).
Time rewrite auth_frag_op.
Time iDestruct "Hown" as "(?&?)".
Time iFrame.
Time }
Time by iApply IH\207\131.
Time Qed.
Time
Lemma gen_heap_bigOpM_dom (\207\131 : gmap L V) (q : Qp) :
  ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i q v)
  -\226\136\151 [\226\136\151 set] i \226\136\136 dom (gset L) \207\131, \226\136\131 v, \226\140\156\207\131 !! i = Some v\226\140\157 \226\136\151 mapsto i q v.
Time Proof.
Time iIntros "H".
Time iApply big_sepM_dom.
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hlookup ) "H".
Time iExists _.
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma gen_heap_bigOp_split (\207\131 : gmap L V) (q : Qp) :
  ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i q v)
  -\226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i (q / 2) v)
     \226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i (q / 2) v).
Time Proof.
Time rewrite -big_sepM_sep.
Time (apply big_sepM_mono).
Time iIntros ( ? ? ? ) "($&$)".
Time Qed.
Time End gen_heap.
Time
Definition gen_heap_ctx' {\206\163} {V} {hG : gen_heapG nat V \206\163} :=
  (\226\136\131 \207\131 : gmap nat V, \226\140\156dom (gset nat) \207\131 = addrset\226\140\157 \226\136\151 gen_heap_ctx \207\131)%I.
Time
Lemma gen_heap_update' {\206\163} {V} {hG : gen_heapG nat V \206\163} 
  (l : nat) v1 v2 :
  gen_heap_ctx' -\226\136\151 mapsto l 1 v1 ==\226\136\151 gen_heap_ctx' \226\136\151 mapsto l 1 v2.
Time Proof.
Time iIntros "Hctx Hmapsto".
Time iDestruct "Hctx" as ( \207\131 Hdom ) "H".
Time iDestruct (@gen_heap_valid with "[$] [$]") as % Hlookup.
Time iMod (@gen_heap_update with "[$] [$]") as "(?&$)".
Time (iExists _; iFrame).
Time iPureIntro.
Time rewrite dom_insert_L -Hdom.
Time (cut (l \226\136\136 dom (gset nat) \207\131)).
Time {
Time set_solver +.
Time }
Time (apply elem_of_dom).
Time eauto.
Time Qed.
Time
Inductive addr_status :=
  | Sync : _
  | Unsync : forall (j : nat) {T2} K `{LanguageCtx _ unit T2 OneDisk.l K}, _.
Time Canonical Structure addr_statusC := leibnizO addr_status.
Time Canonical Structure addr_statusF := discreteO addr_status.
Time #[global]Instance addr_status_inhabited : (Inhabited addr_status).
Time Proof.
Time econstructor.
Time exact Sync.
Time Qed.
Time Section refinement_triples.
Time Context `{!exmachG \206\163} `{lockG \206\163} `{!@cfgG OneDisk.Op OneDisk.l \206\163}.
Time Context {hD0Lease : gen_heapG addr nat \206\163}.
Time Context {hD1Lease : gen_heapG addr nat \206\163}.
Time Context {hSync : gen_heapG addr addr_status \206\163}.
Time
Notation "l s\226\134\166{ q } v " := (mapsto (hG:=hSync) l q v)
  (at level 20, q  at level 50, format "l  s\226\134\166{ q }  v") : bi_scope.
Time
Definition LockInv (a : addr) :=
  (\226\136\131 v, lease0 a v \226\136\151 lease1 a v \226\136\151 a s\226\134\166{1 / 2} Sync)%I.
Time
Definition UnlockedInv (a : addr) :=
  (\226\136\131 v0 v1 vstat, lease0 a v0 \226\136\151 lease1 a v1 \226\136\151 a s\226\134\166{1 / 2} vstat)%I.
Time
Definition status_interp (a : addr) v0 v1 (s : addr_status) 
  P :=
  match s with
  | Sync => \226\140\156v0 = v1\226\140\157
  | Unsync j K => j \226\164\135 K (Call (OneDisk.Write_Disk a v0)) \226\136\151 P
  end%I.
Time #[global]
Instance status_interp_timeless  a v0 v1 s P:
 (Timeless P \226\134\146 Timeless (status_interp a v0 v1 s P)).
Time Proof.
Time (destruct s; apply _).
Time Qed.
Time
Definition DurInv (a : addr) v1 P :=
  (\226\136\131 v0 stat,
     a d0\226\134\166 v0 \226\136\151 a d1\226\134\166 v1 \226\136\151 a s\226\134\166{1 / 2} stat \226\136\151 status_interp a v0 v1 stat P)%I.
Time
Definition DurInvSync (a : addr) v1 :=
  (a d0\226\134\166 v1 \226\136\151 a d1\226\134\166 v1 \226\136\151 a s\226\134\166{1 / 2} Sync)%I.
Time Definition durN : namespace := nroot.@"dur_inv".
Time Definition lockN : namespace := nroot.@"lock_inv".
Time
Definition DisksInv P :=
  (\226\136\131 \207\131 : OneDisk.State,
     \226\140\156dom (gset _) (OneDisk.disk_state \207\131) = addrset\226\140\157
     \226\136\151 source_state \207\131
       \226\136\151 gen_heap_ctx' (hG:=hSync)
         \226\136\151 ([\226\136\151 map] a\226\134\166v1 \226\136\136 OneDisk.disk_state \207\131, DurInv a v1 P))%I.
Time
Definition ExecInv :=
  (source_ctx
   \226\136\151 ([\226\136\151 set] a \226\136\136 addrset, \226\136\131 \206\179, is_lock lockN \206\179 a (LockInv a))
     \226\136\151 inv durN (DisksInv Registered))%I.
Time
Definition ExecInner :=
  (([\226\136\151 set] a \226\136\136 addrset, a m\226\134\166 0 \226\136\151 LockInv a) \226\136\151 DisksInv Registered)%I.
Time Definition CrashInv := (source_ctx \226\136\151 inv durN (DisksInv True))%I.
Time
Definition CrashStarter := ([\226\136\151 set] a \226\136\136 addrset, a m\226\134\166 0 \226\136\151 UnlockedInv a)%I.
Time
Definition CrashInner := ((source_ctx \226\136\151 DisksInv True) \226\136\151 CrashStarter)%I.
Time Opaque addrset.
Time
Lemma write_refinement {T} j K `{LanguageCtx OneDisk.Op unit T OneDisk.l K} 
  a v :
  {{{ j \226\164\135 K (Call (OneDisk.Write_Disk a v)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  write a v {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&(#Hsrc&#Hlocks&#Hinv)) H\206\166".
Time rewrite /write.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct lt_dec as [Hlt| Hnlt] ; last 
 first).
Time {
Time iApply wp_bind_proc_subst.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&?)".
Time iDestruct "Hdom1" as % Hdom1.
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (split; auto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time wp_ret.
Time (assert (OneDisk.upd_disk a v \207\131 = \207\131) as ->).
Time {
Time (destruct \207\131 as [d]).
Time rewrite /OneDisk.upd_disk.
Time f_equal.
Time rewrite /OneDisk.upd_default.
Time (pose proof (not_lt_size_not_in_addrset a Hnlt) as Hdom).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -Hdom1 not_elem_of_dom in 
 {} Hdom * =>{+}->).
Time eauto.
Time }
Time iExists _.
Time iFrame.
Time iSplitL "".
Time {
Time iModIntro.
Time iNext.
Time iPureIntro.
Time auto.
Time }
Time iModIntro.
Time iNext.
Time wp_ret.
Time clear.
Time iApply "H\206\166".
Time iFrame.
Time }
Time wp_bind.
Time (apply lt_size_in_addrset in Hlt).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepS_elem_of with "Hlocks")
 as "Hlock" ; first  eauto).
Time iDestruct "Hlock" as ( \206\179 ) "Hlock".
Time iApply (wp_lock with "[$]").
Time iIntros "!> (Hlocked&Hlockinv)".
Time wp_bind.
Time iDestruct "Hlockinv" as ( v' ) "(Hl0&Hl1&Hstatus)".
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1 Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( v0 stat ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time (iDestruct "Hstat" as % Heq; subst).
Time iApply (wp_write_disk0 with "[$]").
Time iIntros "!> (Hd0&Hl0)".
Time
iMod (gen_heap_update' _ _ (Unsync j K) with "[$] [Hstatus Hstatus_auth]") as
 "(?&Hstatus)".
Time {
Time iCombine "Hstatus Hstatus_auth" as "$".
Time }
Time iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
Time iExists _.
Time iFrame.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth Hj Hreg".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time }
Time iModIntro.
Time wp_bind.
Time iInv "Hinv" as "H".
Time clear \207\131 Hdom1 Hlookup Heq.
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1' Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_insert_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( ? ? ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time iApply (wp_write_disk1 with "[$]").
Time iIntros "!> (Hd1&Hl1)".
Time
iMod (gen_heap_update' _ _ Sync with "[$] [Hstatus Hstatus_auth]") as
 "(?&Hstatus)".
Time {
Time iCombine "Hstatus Hstatus_auth" as "$".
Time }
Time iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
Time iDestruct "Hstat" as "(Hj&Hreg)".
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (split; auto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time rewrite upd_disk_dom.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iModIntro.
Time iNext.
Time rewrite /OneDisk.upd_disk /OneDisk.upd_default /= Hlookup.
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time }
Time iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
Time {
Time iFrame "Hlock".
Time iFrame.
Time (iExists _; iFrame).
Time }
Time iIntros "!> _".
Time iApply "H\206\166".
Time iFrame.
Time Qed.
Time
Lemma read_refinement {T} j K `{LanguageCtx OneDisk.Op nat T OneDisk.l K} 
  a :
  {{{ j \226\164\135 K (Call (OneDisk.Read_Disk a)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  read a {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&(#Hsrc&#Hlocks&#Hinv)) H\206\166".
Time rewrite /read.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct lt_dec as [Hlt| Hnlt] ; last 
 first).
Time {
Time iApply wp_bind_proc_subst.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&?)".
Time iDestruct "Hdom1" as % Hdom1.
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (split; auto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time wp_ret.
Time (assert (OneDisk.lookup_disk a \207\131 = 0) as ->).
Time {
Time (destruct \207\131 as [d]).
Time rewrite /OneDisk.lookup_disk /OneDisk.lookup_default.
Time (pose proof (not_lt_size_not_in_addrset a Hnlt) as Hdom).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -Hdom1 not_elem_of_dom in 
 {} Hdom * =>{+}->).
Time eauto.
Time }
Time iExists _.
Time iFrame.
Time iSplitL "".
Time {
Time iModIntro.
Time iNext.
Time iPureIntro.
Time auto.
Time }
Time iModIntro.
Time iNext.
Time wp_ret.
Time clear.
Time iApply "H\206\166".
Time iFrame.
Time }
Time wp_bind.
Time (apply lt_size_in_addrset in Hlt).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepS_elem_of with "Hlocks")
 as "Hlock" ; first  eauto).
Time iDestruct "Hlock" as ( \206\179 ) "Hlock".
Time iApply (wp_lock with "[$]").
Time iIntros "!> (Hlocked&Hlockinv)".
Time wp_bind.
Time iDestruct "Hlockinv" as ( v' ) "(Hl0&Hl1&Hstatus)".
Time wp_bind.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1 Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( ? ? ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time (iDestruct "Hstat" as % Heq; subst).
Time iApply (wp_read_disk0 with "[$]").
Time iIntros ( mv ) "!> (Hd0&Hret)".
Time (destruct mv as [v| ]).
Time -
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (split; auto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time (iDestruct "Hret" as % Heq'; subst).
Time iExists _.
Time iFrame.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time }
Time iModIntro.
Time wp_ret.
Time wp_bind.
Time iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
Time {
Time iFrame "Hlock".
Time iFrame.
Time (iExists _; iFrame).
Time }
Time iIntros "!> _".
Time wp_ret.
Time iApply "H\206\166".
Time iFrame.
Time (assert (OneDisk.lookup_disk a \207\131 = v) as ->).
Time {
Time (destruct \207\131 as [d]).
Time rewrite /OneDisk.lookup_disk /OneDisk.lookup_default.
Time by rewrite Hlookup.
Time }
Time iFrame.
Time -
Time iExists _.
Time iFrame.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time }
Time iModIntro.
Time wp_bind.
Time iInv "Hinv" as "H".
Time clear \207\131 Hdom1 Hlookup Heq.
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1 Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( ? ? ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time (iDestruct "Hstat" as % Heq; subst).
Time iApply (wp_read_disk1_only1 with "[$]").
Time iIntros "!> Hd1".
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (split; auto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time }
Time iModIntro.
Time wp_ret.
Time wp_bind.
Time iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
Time {
Time iFrame "Hlock".
Time iFrame.
Time (iExists _; iFrame).
Time }
Time iIntros "!> _".
Time wp_ret.
Time iApply "H\206\166".
Time iFrame.
Time (assert (OneDisk.lookup_disk a \207\131 = v') as ->).
Time {
Time (destruct \207\131 as [d]).
Time rewrite /OneDisk.lookup_disk /OneDisk.lookup_default.
Time by rewrite Hlookup.
Time }
Time iFrame.
Time Qed.
Time #[global]
Instance DisksInv_Timeless  (P : iProp \206\163) {HT : Timeless P}:
 (Timeless (DisksInv P)).
Time Proof.
Time (apply _).
Time Qed.
Time End refinement_triples.
Time Lemma init_zero_lookup_is_zero k x : init_zero !! k = Some x \226\134\146 x = 0.
Time Proof.
Time (destruct (lt_dec k size)).
Time -
Time (rewrite init_zero_lookup_lt_zero; congruence).
Time -
Time (rewrite init_zero_lookup_ge_None; congruence).
Time Qed.
Time Module repRT<: twodisk_refinement_type.
Time
Definition \206\163 : gFunctors :=
  #[ exmach\206\163; @cfg\206\163 OneDisk.Op OneDisk.l; lock\206\163; gen_heap\206\163 addr addr_status].
Time Existing Instance subG_cfgPreG.
Time
Definition init_absr \207\1311a \207\1311c := TwoDisk.l.(initP) \207\1311c \226\136\167 OneDisk.l.(initP) \207\1311a.
Time Opaque size.
Time Definition OpT := OneDisk.Op.
Time Definition \206\155a := OneDisk.l.
Time Definition impl := ReplicatedDiskImpl.impl.
Time Import TwoDisk.
Time
Instance from_exist_left_sep'  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist ((\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \206\166 a \226\136\151 Q)%I).
Time Proof.
Time rewrite /FromExist.
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&$)".
Time (iExists _; eauto).
Time Qed.
Time Instance CFG : (@cfgPreG OneDisk.Op OneDisk.l \206\163).
Time (apply _).
Time Qed.
Time Instance HEX : (ReplicatedDisk.RefinementAdequacy.exmachPreG \206\163).
Time (apply _).
Time Qed.
Time Instance INV : (Adequacy.invPreG \206\163).
Time (apply _).
Time Qed.
Time
Instance REG : (inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))).
Time (apply _).
Time Qed.
Time #[global]Instance inst_inG1 : (lockG \206\163).
Time Proof.
Time (apply _).
Time Qed.
Time Definition exec_inv := fun H1 H2 => (\226\136\131 hS, @ExecInv \206\163 H2 _ H1 hS)%I.
Time Definition exec_inner := fun H1 H2 => (\226\136\131 hS, @ExecInner \206\163 H2 H1 hS)%I.
Time Definition crash_inner := fun H1 H2 => (\226\136\131 hS, @CrashInner \206\163 H2 H1 hS)%I.
Time Definition crash_inv := fun H1 H2 hS => @CrashInv \206\163 H2 H1 hS.
Time
Definition crash_param :=
  fun (_ : @cfgG OpT \206\155a \206\163) (_ : exmachG \206\163) =>
  (gen_heapG addr addr_status \206\163)%type.
Time
Definition crash_starter :=
  fun (H1 : @cfgG OpT \206\155a \206\163) (H2 : exmachG \206\163) hS => @CrashStarter \206\163 H2 hS.
Time Definition E := nclose sourceN.
Time Definition recv := recv.
Time End repRT.
Time Module repRD:=  twodisk_refinement_definitions repRT.
Time Module repRO: twodisk_refinement_obligations repRT.
Time Module eRD:=  repRD.
Time Import repRT repRD.
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
Time (intros ? ? ?).
Time (apply _).
Time Qed.
Time Lemma nameIncl : nclose sourceN \226\138\134 E.
Time Proof.
Time solve_ndisj.
Time Qed.
Time Lemma recsingle : recover impl = rec_singleton recv.
Time Proof.
Time trivial.
Time Qed.
Time Lemma refinement_op_triples : refinement_op_triples_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "(Hj&Hreg&H)".
Time iDestruct "H" as ( ? ) "H".
Time (destruct op).
Time -
Time iApply (@read_refinement with "[$]").
Time eauto.
Time -
Time iApply (@write_refinement with "[$]").
Time eauto.
Time Qed.
Time Lemma exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx.
Time Proof.
Time (red).
Time (intros).
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&?)".
Time eauto.
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time (intros ? ? hS).
Time iIntros "(H&Hreg&Hstarter)".
Time iDestruct "H" as "(#Hctx&#Hinv)".
Time rewrite /recv.
Time
iAssert
 ([\226\136\151 set] a \226\136\136 addrset, if lt_dec a size then a m\226\134\166 0 \226\136\151 @UnlockedInv _ _ hS a
                       else a m\226\134\166 0 \226\136\151 @LockInv _ _ hS a)%I with "[Hstarter]"
 as "Hprogress".
Time {
Time iApply (big_sepS_mono with "Hstarter").
Time iIntros ( a Hin ) "Hunlocked".
Time (<ssreflect_plugin::ssrtclseq@0> destruct lt_dec ; first  iFrame).
Time exfalso.
Time (eapply not_lt_size_not_in_addrset; eauto).
Time }
Time rewrite /ReplicatedDiskImpl.recv.
Time (assert (Hbound : size <= size) by lia).
Time (remember size as n eqn:Heqn ).
Time rewrite {+2}Heqn in  {} Hbound.
Time clear Heqn.
Time iInduction n as [| n] "IH".
Time -
Time wp_ret.
Time iInv "Hinv" as ">H" "_".
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time iApply fupd_mask_weaken.
Time {
Time solve_ndisj.
Time }
Time
iAssert
 ([\226\136\151 map] a\226\134\166v1 \226\136\136 \207\131.(OneDisk.disk_state), @DurInvSync _ _ hS a v1
                                         \226\136\151 a m\226\134\166 0 \226\136\151 @LockInv _ _ hS a)%I with
 "[Hprogress Hdur]" as "Hprogress".
Time {
Time rewrite -Hdom1.
Time iDestruct (big_sepM_dom with "Hprogress") as "H".
Time iDestruct (big_sepM_sep with "[H Hdur]") as "H".
Time {
Time iFrame.
Time }
Time iApply (big_sepM_mono with "H").
Time iIntros ( a v Hlookup ) "(Hd&(?&Hl))".
Time iDestruct "Hl" as ( v' ) "(Hl0&Hl1&Hstatus)".
Time iDestruct "Hd" as ( v0 stat ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time iFrame.
Time iExists _.
Time iFrame.
Time }
Time iExists _ , _.
Time iFrame.
Time iSplitL "".
Time {
Time iPureIntro.
Time econstructor.
Time }
Time iClear "Hctx".
Time iIntros ( ? ? ? ) "(Hctx&Hstate)".
Time iDestruct (big_sepM_sep with "Hprogress") as "(Hdur&Hprogress)".
Time iDestruct (big_sepM_dom with "Hprogress") as "Hprogress".
Time rewrite Hdom1.
Time iModIntro.
Time iExists hS.
Time iFrame.
Time (iExists _; iFrame).
Time eauto.
Time (iSplitL ""; auto).
Time iApply (big_sepM_mono with "Hdur").
Time iIntros ( a' v' Hlookup ) "(?&?&?)".
Time iExists _ , Sync.
Time iFrame.
Time auto.
Time -
Time wp_bind.
Time rewrite /fixup.
Time unshelve iApply (wp_bind (\206\187 x, Bind x _)).
Time {
Time (apply _).
Time }
Time (assert (Hlt : n < size) by lia).
Time (assert (Hin : n \226\136\136 addrset)).
Time {
Time by apply lt_size_in_addrset.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepS_delete with "Hprogress")
 as "(Hcurr&Hrest)" ; first  eauto).
Time (<ssreflect_plugin::ssrtclseq@0> destruct lt_dec ; last  by lia).
Time iDestruct "Hcurr" as "(Hmem&Hcurr)".
Time iDestruct "Hcurr" as ( v0 v1 ? ) "(Hl0&Hl1&Hstatus)".
Time iInv "Hinv" as ">H".
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hin =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1' Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( v0' stat ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time iApply (wp_read_disk0 with "[$]").
Time iIntros ( mv ) "!> (Hd0&Hret)".
Time (destruct mv as [v| ]).
Time *
Time iSplitL "Hstate Hctx_stat Hdur Hd0 Hd1 Hstatus_auth Hstat".
Time {
Time iExists _.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time by iFrame.
Time }
Time iModIntro.
Time wp_bind.
Time wp_ret.
Time iInv "Hinv" as ">H".
Time clear \207\131 Hdom1 Hlookup.
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hin =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1'' Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_insert_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( v0'' stat' ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time iApply (wp_write_disk1 with "[$]").
Time (iDestruct "Hret" as % Heq; subst).
Time iIntros "!> (Hd1&Hl1)".
Time
iMod (gen_heap_update' _ _ Sync with "Hctx_stat [Hstatus Hstatus_auth]") as
 "(Hctx_stat&Hstatus)".
Time {
Time iCombine "Hstatus Hstatus_auth" as "$".
Time }
Time iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
Time iSplitL "Hstate Hctx_stat Hdur Hd0 Hd1 Hstatus_auth Hstat".
Time {
Time (destruct stat').
Time *
Time iExists \207\131.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iSpecialize ("Hdur" $! v).
Time (iDestruct "Hstat" as % Heq; subst).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_id ; last  auto).
Time iApply "Hdur".
Time iExists _ , _.
Time by iFrame.
Time *
Time iDestruct "Hstat" as "(Hj&Hreg')".
Time iMod (ghost_step_call with "Hj [$] [$]") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (split; auto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time rewrite @upd_disk_dom.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time rewrite /OneDisk.upd_disk /OneDisk.upd_default Hlookup.
Time iApply "Hdur".
Time iExists _ , _.
Time by iFrame.
Time }
Time iModIntro.
Time iApply ("IH" with "[] Hreg [Hrest Hl0 Hl1 Hstatus Hmem]").
Time {
Time iPureIntro.
Time lia.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_delete ; first  eauto).
Time iSplitR "Hrest".
Time {
Time (destruct lt_dec; try lia; [  ]).
Time iFrame.
Time iExists _.
Time iFrame.
Time }
Time {
Time iApply (big_sepS_mono with "Hrest").
Time iIntros ( x Hin' ) "H".
Time (assert (x \226\137\160 n)).
Time {
Time (apply elem_of_difference in Hin' as (?, Hsingle)).
Time (intros Heq; subst).
Time (apply Hsingle, elem_of_singleton; auto).
Time }
Time (do 2 destruct (lt_dec); auto).
Time {
Time lia.
Time }
Time {
Time iDestruct "H" as "($&H)".
Time iDestruct "H" as ( ? ) "(?&?&?)".
Time iExists _ , _ , _.
Time iFrame.
Time }
Time }
Time *
Time iSplitL "Hstate Hctx_stat Hdur Hd0 Hd1 Hstatus_auth Hstat".
Time {
Time iExists _.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time by iFrame.
Time }
Time iModIntro.
Time iApply (wp_write_disk0_only1 _ _ (\226\138\164 \226\136\150 \226\134\145durN) n v0 v1).
Time {
Time trivial.
Time }
Time iInv "Hinv" as ">H" "Hclo".
Time clear \207\131 Hdom1 Hlookup.
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hin =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1'' Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_insert_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( v0'' stat' ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time
iMod (gen_heap_update' _ _ Sync with "Hctx_stat [Hstatus Hstatus_auth]") as
 "(Hctx_stat&Hstatus)".
Time {
Time iCombine "Hstatus Hstatus_auth" as "$".
Time }
Time iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
Time iModIntro.
Time iFrame.
Time iIntros "(Hd0&Hl0)".
Time iMod ("Hclo" with "[Hstate Hctx_stat Hdur Hd0 Hd1 Hstatus_auth Hstat]").
Time {
Time (destruct stat').
Time *
Time iExists _.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iSpecialize ("Hdur" $! v1).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_id ; last  auto).
Time iApply "Hdur".
Time (iDestruct "Hstat" as % Heq; subst).
Time iExists _ , _.
Time by iFrame.
Time *
Time iExists _.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iSpecialize ("Hdur" $! v1).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_id ; last  auto).
Time iApply "Hdur".
Time iExists v1 , Sync.
Time iFrame.
Time rewrite /status_interp.
Time auto.
Time }
Time wp_bind.
Time wp_ret.
Time wp_ret.
Time iModIntro.
Time iApply ("IH" with "[] Hreg [Hrest Hl0 Hl1 Hstatus Hmem]").
Time {
Time iPureIntro.
Time lia.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_delete ; first  eauto).
Time iSplitR "Hrest".
Time {
Time (destruct lt_dec; try lia; [  ]).
Time iFrame.
Time iExists _.
Time iFrame.
Time }
Time {
Time iApply (big_sepS_mono with "Hrest").
Time iIntros ( x Hin' ) "H".
Time (assert (x \226\137\160 n)).
Time {
Time (apply elem_of_difference in Hin' as (?, Hsingle)).
Time (intros Heq; subst).
Time (apply Hsingle, elem_of_singleton; auto).
Time }
Time (do 2 destruct (lt_dec); auto).
Time {
Time lia.
Time }
Time {
Time iDestruct "H" as "($&H)".
Time iDestruct "H" as ( ? ) "(?&?&?)".
Time iExists _ , _ , _.
Time iFrame.
Time }
Time }
Time Qed.
Time Lemma init_wf : \226\136\128 \207\1311a \207\1311c, init_absr \207\1311a \207\1311c \226\134\146 \207\1311c = TwoDisk.init_state.
Time Proof.
Time (intros ? ? (H, ?)).
Time by inversion H.
Time Qed.
Time Lemma init_exec_inner : init_exec_inner_type.
Time Proof.
Time (intros ? ? (H, Hinit) ? ?).
Time (inversion H).
Time (inversion Hinit).
Time subst.
Time iIntros "(Hmem&Hdisk0&Hdisk1&#?&Hstate)".
Time
iMod (gen_heap_strong_init ((\206\187 x, Sync) <$> init_zero)) as ( hS <- )
 "(hS&hSfrag)".
Time iPoseProof (gen_heap_init_to_bigOp (hG:=hS) with "hSfrag") as "hSfrag".
Time iEval rewrite big_sepM_sep in "Hdisk0".
Time iDestruct "Hdisk0" as "(Hd0&HL0)".
Time iEval rewrite big_sepM_sep in "Hdisk1".
Time iDestruct "Hdisk1" as "(Hd1&HL1)".
Time iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
Time rewrite big_opM_fmap.
Time iExists hS.
Time rewrite /ExecInner.
Time iSplitL "Hmem HL0 HL1 hSa".
Time {
Time iModIntro.
Time iApply big_opM_dom.
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hlookup ) "(((?&?)&?)&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time iExists _.
Time iFrame.
Time }
Time iExists _.
Time iFrame "Hstate".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by auto).
Time iSplitL "hS".
Time {
Time iExists _.
Time iFrame "hS".
Time rewrite dom_fmap_L.
Time auto.
Time }
Time iModIntro.
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hlookup ) "((((?&?)&?)&?)&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time auto.
Time Qed.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time iIntros ( ? ? ) "H".
Time iDestruct "H" as ( hS ) "(#Hsrc&#Hlocks&#Hinv)".
Time iInv "Hinv" as ">H" "_".
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iDestruct "Hctx_stat" as ( \207\131S HdomS ) "Hctx_stat".
Time iMod (gen_heap_strong_init \207\131S) as ( hS' <- ) "(hS&hSfrag)".
Time iPoseProof (gen_heap_init_to_bigOp (hG:=hS') with "hSfrag") as "hSfrag".
Time iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
Time iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
Time rewrite ?HdomS.
Time iDestruct (big_sepM_dom with "hSa") as "hSa".
Time
iPoseProof
 (big_sepM_mono _
    (\206\187 k v,
       |={E}=> (\226\136\131 v0 stat, _)
               \226\136\151 (\226\136\131 v0 v1,
                    next_lease (hG:=exm_disk0_inG) k v0
                    \226\136\151 next_lease (hG:=_) k v1))%I with "Hdur") as "Hdur".
Time {
Time iIntros ( ? ? Heq ) "Hinv".
Time rewrite /DurInv.
Time iDestruct "Hinv" as ( v0 stat ) "(Hd0&Hd1&Hstat&Hinterp)".
Time iMod (disk0_next with "[$]") as "(Hd0&Hl0)".
Time iMod (disk1_next with "[$]") as "(Hd1&Hl1)".
Time iModIntro.
Time iCombine "Hd0 Hd1 Hstat Hinterp" as "Hleft".
Time iCombine "Hl0 Hl1" as "Hright".
Time iSplitL "Hleft".
Time *
Time iExists v0 , stat.
Time iApply "Hleft".
Time *
Time iExists v0 , _.
Time iApply "Hright".
Time }
Time iMod (big_sepM_fupd with "Hdur") as "Hdur".
Time rewrite big_sepM_sep.
Time iDestruct "Hdur" as "(Hdur&Hl)".
Time iDestruct (big_sepM_dom with "Hl") as "Hl".
Time iExists hS'.
Time iModIntro.
Time rewrite /CrashInner /CrashInv /CrashStarter.
Time iFrame "Hsrc".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "Hmem Hl hSa" ; last  first).
Time {
Time rewrite Hdom1 addrset_unfold.
Time iApply big_opM_dom.
Time iEval rewrite -big_opM_dom in "Hl".
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time rewrite /UnlockedInv.
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hlookup ) "((Hs&Hl)&H2)".
Time iDestruct "Hs" as ( ? ) "(%&Hs)".
Time iDestruct "Hl" as ( v1 v2 ) "(Hl0&Hl1)".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time iExists _ , _ , _.
Time iFrame.
Time }
Time iExists _.
Time iFrame "Hstate".
Time iDestruct (gen_heap_bigOpM_dom with "hSb") as "hSb".
Time rewrite ?HdomL0 ?HdomL1 ?HdomS.
Time rewrite -?Hdom1.
Time iDestruct (big_sepM_dom with "hSb") as "hSb".
Time iSplitL "".
Time {
Time iPureIntro.
Time auto.
Time }
Time iSplitL "hS".
Time {
Time iExists _.
Time iFrame.
Time by iPureIntro.
Time }
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iDestruct (big_sepM_mono_with_inv with "Hctx_stat H") as "(?&$)".
Time iIntros ( k x Hlookup ) "H".
Time iDestruct "H" as "(Hctx_stat&H&Hdur)".
Time iDestruct "H" as ( stat0 ) "(%&Hs)".
Time iDestruct "Hdur" as ( ? stat ) "(Hd0&Hd1&Hs'&Hstatus)".
Time iDestruct (@gen_heap_valid with "Hctx_stat Hs'") as % ?.
Time
(repeat
  match goal with
  | H1:?x = Some ?y, H2:?x = Some ?z
    |- _ => rewrite H1 in  {} H2; inversion H2; clear H1 H2; subst
  end).
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time (destruct stat; auto).
Time (iDestruct "Hstatus" as "(?&?)"; iFrame).
Time Qed.
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time Proof.
Time iIntros ( ? ? hS ) "H".
Time iDestruct "H" as "(#Hsrc&#Hinv)".
Time iInv "Hinv" as ">H" "_".
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iDestruct "Hctx_stat" as ( \207\131S HdomS ) "Hctx_stat".
Time iMod (gen_heap_strong_init \207\131S) as ( hS' <- ) "(hS&hSfrag)".
Time iPoseProof (gen_heap_init_to_bigOp (hG:=hS') with "hSfrag") as "hSfrag".
Time iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
Time iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
Time rewrite ?HdomS.
Time iDestruct (big_sepM_dom with "hSa") as "hSa".
Time
iPoseProof
 (big_sepM_mono _
    (\206\187 k v,
       |={E}=> (\226\136\131 v0 stat, _)
               \226\136\151 (\226\136\131 v0 v1,
                    next_lease (hG:=exm_disk0_inG) k v0
                    \226\136\151 next_lease (hG:=_) k v1))%I with "Hdur") as "Hdur".
Time {
Time iIntros ( ? ? Heq ) "Hinv".
Time rewrite /DurInv.
Time iDestruct "Hinv" as ( v0 stat ) "(Hd0&Hd1&Hstat&Hinterp)".
Time iMod (disk0_next with "[$]") as "(Hd0&Hl0)".
Time iMod (disk1_next with "[$]") as "(Hd1&Hl1)".
Time iModIntro.
Time iCombine "Hd0 Hd1 Hstat Hinterp" as "Hleft".
Time iCombine "Hl0 Hl1" as "Hright".
Time iSplitL "Hleft".
Time *
Time iExists v0 , stat.
Time iApply "Hleft".
Time *
Time iExists v0 , _.
Time iApply "Hright".
Time }
Time iMod (big_sepM_fupd with "Hdur") as "Hdur".
Time rewrite big_sepM_sep.
Time iDestruct "Hdur" as "(Hdur&Hl)".
Time iDestruct (big_sepM_dom with "Hl") as "Hl".
Time iExists hS'.
Time iModIntro.
Time rewrite /CrashInner /CrashInv /CrashStarter.
Time iFrame "Hsrc".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "Hmem Hl hSa" ; last  first).
Time {
Time rewrite Hdom1 addrset_unfold.
Time iApply big_opM_dom.
Time iEval rewrite -big_opM_dom in "Hl".
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time rewrite /UnlockedInv.
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hlookup ) "((Hs&Hl)&H2)".
Time iDestruct "Hs" as ( ? ) "(%&Hs)".
Time iDestruct "Hl" as ( v1 v2 ) "(Hl0&Hl1)".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time iExists _ , _ , _.
Time iFrame.
Time }
Time iExists _.
Time iFrame "Hstate".
Time iDestruct (gen_heap_bigOpM_dom with "hSb") as "hSb".
Time rewrite ?HdomL0 ?HdomL1 ?HdomS.
Time rewrite -?Hdom1.
Time iDestruct (big_sepM_dom with "hSb") as "hSb".
Time iSplitL "".
Time {
Time iPureIntro.
Time auto.
Time }
Time iSplitL "hS".
Time {
Time iExists _.
Time iFrame.
Time by iPureIntro.
Time }
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iDestruct (big_sepM_mono_with_inv with "Hctx_stat H") as "(?&$)".
Time iIntros ( k x Hlookup ) "H".
Time iDestruct "H" as "(Hctx_stat&H&Hdur)".
Time iDestruct "H" as ( stat0 ) "(%&Hs)".
Time iDestruct "Hdur" as ( ? stat ) "(Hd0&Hd1&Hs'&Hstatus)".
Time iDestruct (@gen_heap_valid with "Hctx_stat Hs'") as % ?.
Time
(repeat
  match goal with
  | H1:?x = Some ?y, H2:?x = Some ?z
    |- _ => rewrite H1 in  {} H2; inversion H2; clear H1 H2; subst
  end).
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time Qed.
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time (red).
Time iIntros ( ? ? ) "(H&?)".
Time iDestruct "H" as ( hInv hS ) "((_&Hinv)&?)".
Time iExists hS.
Time iFrame.
Time by iMod (@inv_alloc \206\163 exm_invG durN _ _ with "Hinv") as "$".
Time Qed.
Time Lemma exec_inner_inv : exec_inner_inv_type.
Time Proof.
Time iIntros ( ? ? ) "(H&?)".
Time iDestruct "H" as ( hInv hS ) "(Hlocks&Hdur)".
Time iExists hS.
Time iFrame.
Time iSplitR "Hdur".
Time -
Time rewrite -big_sepS_fupd.
Time iApply (big_sepS_mono with "Hlocks").
Time iIntros ( a Hin ) "(Hmem&Hlock)".
Time (iApply (lock_init with "Hmem [Hlock]"); auto).
Time -
Time by iMod (@inv_alloc \206\163 exm_invG durN _ _ with "Hdur") as "$".
Time Qed.
Time Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Time Proof.
Time iIntros ( ? ? ) "Hdone H".
Time iDestruct "H" as ( hS ) "(#Hsrc&#Hlocks&#Hinv)".
Time iInv "Hinv" as ">H" "_".
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iExists _ , _.
Time iFrame.
Time iSplitL "".
Time {
Time iPureIntro.
Time econstructor.
Time }
Time iClear "Hsrc".
Time iIntros ( ? ? ? ? ) "(Hctx&Hstate&Hmem)".
Time
iMod (gen_heap_strong_init ((\206\187 _, Sync) <$> init_zero)) as ( hS' <- )
 "(hS&hSfrag)".
Time iPoseProof (gen_heap_init_to_bigOp (hG:=hS') with "hSfrag") as "hSfrag".
Time iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
Time iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
Time rewrite ?HdomS.
Time iDestruct (big_sepM_dom with "hSa") as "hSa".
Time
iPoseProof
 (big_sepM_mono_with_inv _ _
    (\206\187 k v,
       |={\226\138\164}=> ((k d0\226\151\175\226\134\166 v \226\136\151 next_master (hG:=exm_disk0_inG) k v)
                \226\136\151 (k d1\226\151\175\226\134\166 v \226\136\151 next_master (hG:=exm_disk1_inG) k v) \226\136\151 _)
               \226\136\151 (\226\136\131 v,
                    next_lease (hG:=exm_disk0_inG) k v
                    \226\136\151 next_lease (hG:=_) k v))%I with "Hdone Hdur") as
 "(Hdone&Hdur)".
Time {
Time iIntros ( ? ? Heq ) "(Hdone&Hinv)".
Time rewrite /DurInv.
Time iDestruct "Hinv" as ( v0 stat ) "(Hd0&Hd1&Hstat&Hinterp)".
Time (<ssreflect_plugin::ssrtclseq@0> destruct stat ; last  first).
Time {
Time iDestruct "Hinterp" as "(?&Hreg)".
Time (iExFalso; iApply (@AllDone_Register_excl with "Hdone Hreg")).
Time }
Time iFrame.
Time iMod (disk0_next with "[$]") as "(Hd0&Hl0)".
Time iMod (disk1_next with "[$]") as "(Hd1&Hl1)".
Time iModIntro.
Time iDestruct "Hinterp" as % H.
Time subst.
Time iCombine "Hd0 Hd1 Hstat" as "Hleft".
Time iCombine "Hl0 Hl1" as "Hright".
Time iSplitL "Hleft".
Time *
Time iApply "Hleft".
Time *
Time iExists _.
Time iApply "Hright".
Time }
Time iMod (big_sepM_fupd with "Hdur") as "Hdur".
Time rewrite big_sepM_sep.
Time iDestruct "Hdur" as "(Hdur&Hl)".
Time iDestruct (big_sepM_dom with "Hl") as "Hl".
Time iExists hS'.
Time iModIntro.
Time iSplitL "Hmem Hl hSa".
Time {
Time rewrite Hdom1 addrset_unfold.
Time iApply big_opM_dom.
Time iEval rewrite -big_opM_dom in "Hl".
Time iEval rewrite big_opM_dom dom_fmap_L -big_opM_dom in "hSa".
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time rewrite /LockInv.
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hlookup ) "((Hs&Hl)&H2)".
Time iDestruct "Hs" as ( ? Hlookup' ) "Hs".
Time iDestruct "Hl" as ( v ) "(Hl0&Hl1)".
Time rewrite lookup_fmap in  {} Hlookup'.
Time (apply fmap_Some_1 in Hlookup' as (?, (Heq1, Heq2))).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time subst.
Time (iExists _; iFrame).
Time }
Time rewrite big_sepM_fmap.
Time iDestruct (big_sepM_dom with "hSb") as "hSb".
Time
(<ssreflect_plugin::ssrtclseq@0> replace (dom (gset addr) init_zero) with
 addrset ; last  trivial).
Time rewrite -{+2}Hdom1.
Time iDestruct (big_sepM_dom with "hSb") as "hSb".
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iExists _.
Time iFrame.
Time iSplitL "".
Time {
Time iPureIntro.
Time auto.
Time }
Time iSplitL "hS".
Time {
Time iExists _.
Time iFrame.
Time iPureIntro.
Time rewrite dom_fmap_L.
Time auto.
Time }
Time iDestruct (big_sepM_mono_with_inv with "Hdone H") as "(?&$)".
Time iIntros ( k x Hlookup ) "H".
Time iDestruct "H" as "(Hdone&H)".
Time iDestruct "H" as "(?&Hd0&Hd1&Hdur)".
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time eauto.
Time Qed.
Time End repRO.
Time Module repR:=  twodisk_refinement repRT repRO.
Time Import repR.
Time
Lemma rep_crash_refinement_seq {T} \207\1311c \207\1311a (es : proc_seq OneDisk.Op T) :
  repRT.init_absr \207\1311a \207\1311c
  \226\134\146 wf_client_seq es
    \226\134\146 \194\172 proc_exec_seq OneDisk.l es (rec_singleton (Ret ())) (1, \207\1311a) Err
      \226\134\146 \226\136\128 \207\1312c res,
          proc_exec_seq TwoDisk.l
            (compile_proc_seq ReplicatedDiskImpl.impl es)
            (rec_singleton recv) (1, \207\1311c) (Val \207\1312c res)
          \226\134\146 \226\136\131 \207\1312a,
              proc_exec_seq OneDisk.l es (rec_singleton (Ret tt)) 
                (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (apply repR.R.crash_refinement_seq).
Time Qed.
