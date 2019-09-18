Time From iris.algebra Require Import auth gmap list.
Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time
Require Import OneDiskAPI ReplicatedDiskImpl ReplicatedDisk.WeakestPre
  ReplicatedDisk.RefinementAdequacy.
Time
From Armada.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap.
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
Time From Armada.Goose.Examples Require Import MailServer.
Time From Armada.Goose.Proof Require Import Interp.
Time (destruct (_ !! a) as [?| ] eqn:Hlookup).
Time -
Time Require Import Goose.Proof.Interp.
Time From Armada Require AtomicPair.Helpers.
Time From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time rewrite dom_insert_L.
Time (assert (a \226\136\136 dom (gset nat) \207\131.(OneDisk.disk_state))).
Time {
Time (apply elem_of_dom; eauto).
Time From Armada.Goose Require Import Machine.
Time From Armada.Goose Require Import GoZeroValues.
Time Unset Implicit Arguments.
Time
Inductive ghost_init_status {gm : GoModel} {gmwf : GoModelWf gm} :=
  | Uninit : _
  | Started_Init :
      forall (j : nat) {T2} K `{LanguageCtx _ unit T2 Mail.l K}, _
  | Finished_Init : _.
Time }
Time set_solver.
Time
Lemma map_Permutation (A B : Type) (f : A \226\134\146 B) (al : list A) 
  (bl : list B) :
  Permutation.Permutation (map f al) bl
  \226\134\146 \226\136\131 al', Permutation.Permutation al al' \226\136\167 map f al' = bl.
Time Proof.
Time (intros Hperm).
Time (remember (map f al) as bl0 eqn:Heq ).
Time revert Heq.
Time revert al.
Time (<ssreflect_plugin::ssrtclintros@0> induction Hperm =>al Heq).
Time -
Time (destruct al).
Time exists [].
Time eauto.
Time (inversion Heq).
Time -
Time (destruct al as [| a al]; inversion Heq; subst).
Time (simpl in Heq).
Time (edestruct (IHHperm) as (al', (?, ?)); eauto).
Time subst.
Time exists (a :: al').
Time (split; eauto).
Time -
Time (destruct al as [| a [| b al]]; try inversion Heq; subst).
Time (exists (b :: a :: al); split; eauto).
Time econstructor.
Time -
Time (edestruct (IHHperm1) as (al1, (?, ?)); eauto).
Time -
Time auto.
Time Qed.
Time (edestruct (IHHperm2) as (al2, (?, ?)); eauto).
Time Section gen_heap.
Time Context `{hG : gen_heapG L V \206\163}.
Time
Lemma gen_heap_init_to_bigOp \207\131 :
  own (gen_heap_name hG) (\226\151\175 to_gen_heap \207\131) -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i 1 v.
Time Proof.
Time (induction \207\131 using map_ind).
Time -
Time iIntros.
Time (exists al2; split; eauto).
Time (etransitivity; try eassumption; eauto).
Time Qed.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep.
Time Set Default Goal Selector "!".
Time Notation contents := (gmap string (Datatypes.list byte)).
Time
Canonical Structure contentsC {m : GoModel} {wf : GoModelWf m} :=
  leibnizO contents.
Time
Canonical Structure contentsF {m : GoModel} {wf : GoModelWf m} :=
  discreteO contents.
Time
Canonical Structure ghost_init_statusC {m : GoModel} 
  {wf : GoModelWf m} := leibnizO ghost_init_status.
Time rewrite //=.
Time
Canonical Structure ghost_init_statusF {m : GoModel} 
  {wf : GoModelWf m} := discreteO ghost_init_status.
Time
Definition UserDir {model : GoModel} (user : uint64) :=
  ("user" ++ uint64_to_string user)%string.
Time Set Default Proof Using "Type".
Time Section refinement_triples.
Time Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time Context {hGcontents : ghost_mapG contentsC \206\163}.
Time Context {hGinit : ghost_mapG ghost_init_statusC \206\163}.
Time Context {hGTmp : gen_heapG string Filesys.FS.Inode \206\163}.
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time Import Mail.
Time
Definition InboxLockInv (\206\179 : gname) (n : nat) :=
  (\226\136\131 S1 S2,
     ghost_mapsto_auth \206\179 (A:=discreteO contents) S1
     \226\136\151 ghost_mapsto (A:=discreteO contents) \206\179 O S2)%I.
Time
Definition MailboxStatusInterp (uid : uint64) (lk : LockRef) 
  (\206\179 : gname) (ls : MailboxStatus) (msgs : contents) 
  (open : bool) :=
  (if open
   then match ls with
        | MUnlocked =>
            UserDir uid \226\134\166 Unlocked
            \226\136\168 UserDir uid \226\134\166{ - 1} ReadLocked 0 \226\136\151 InboxLockInv \206\179 O
        | MPickingUp =>
            wlocked lk
            \226\136\151 (\226\136\131 S : contents,
                 ghost_mapsto_auth \206\179 (A:=contentsC) S \226\136\151 \226\140\156S \226\138\134 msgs\226\140\157)
        | MLocked => wlocked lk \226\136\151 InboxLockInv \206\179 O \226\136\151 UserDir uid \226\134\166 Unlocked
        end else \226\140\156ls = ls\226\140\157 \226\136\151 UserDir uid \226\134\166 Unlocked)%I.
Time Definition boxN : namespace := nroot.@"inbox_lock".
Time
Definition InboxInv (uid : uint64) (lk : LockRef) 
  (\206\179 : gname) (ls : MailboxStatus)
  (msgs : gmap.gmap string (Datatypes.list byte)) 
  (open : bool) :=
  ((if open then is_lock boxN lk (InboxLockInv \206\179) True else True)
   \226\136\151 MailboxStatusInterp uid lk \206\179 ls msgs open
     \226\136\151 UserDir uid \226\134\166 dom (gset string) msgs
       \226\136\151 ([\226\136\151 map] mid\226\134\166msgData \226\136\136 msgs, \226\136\131 inode (n : nat),
                                        path.mk (UserDir uid) mid \226\134\166 inode
                                        \226\136\151 inode \226\134\166{ n} msgData))%I.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap m) \226\136\151 mapsto i 1 x)%I with
 "[Hown]" as "[Hrest $]".
Time
Definition InboxInv_weak (uid : uint64) (lk : LockRef) 
  (\206\179 : gname) (ls : MailboxStatus)
  (msgs : gmap.gmap string (Datatypes.list byte)) 
  (open : bool) :=
  (MailboxStatusInterp uid lk \206\179 ls msgs open
   \226\136\151 UserDir uid \226\134\166 dom (gset string) msgs
     \226\136\151 ([\226\136\151 map] mid\226\134\166msgData \226\136\136 msgs, \226\136\131 inode (n : nat),
                                      path.mk (UserDir uid) mid \226\134\166 inode
                                      \226\136\151 inode \226\134\166{ n} msgData))%I.
Time #[global]
Instance InboxInv_timeless  uid lk \206\179 ls msgs open':
 (Timeless (InboxInv_weak uid lk \206\179 ls msgs open')).
Time Proof.
Time rewrite /InboxInv_weak.
Time (destruct ls, open'; apply _).
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
Time Qed.
Time
Definition GlobalInv ls (open : bool) : iProp \206\163 :=
  (if open
   then \226\136\131 (lsptr : slice.t LockRef) (q : nat),
          global \226\134\166{ q} Some lsptr \226\136\151 lsptr \226\134\166{ q} (ls, ls) else 
   global \226\134\166 None)%I.
Time
Lemma GlobalInv_split ls :
  GlobalInv ls true
  \226\138\162 GlobalInv ls true
    \226\136\151 (\226\136\131 lsptr, global \226\134\166{ - 1} Some lsptr \226\136\151 lsptr \226\134\166{ - 1} (ls, ls)).
Time Proof.
Time iIntros "HG".
Time iDestruct "HG" as ( lsptr q ) "(HP1&HP2)".
Time iDestruct "HP2" as ( Heq ? ) "HP2".
Time rewrite //= @read_split /ptr_mapsto Count_Typed_Heap.read_split_join.
Time (iExists _; iFrame).
Time iPureIntro.
Time rewrite dom_insert_L -Hdom.
Time (cut (l \226\136\136 dom (gset nat) \207\131)).
Time {
Time set_solver +.
Time iDestruct "HP1" as "(HP1&HR1)".
Time iDestruct "HP2" as "(HP2&HR2)".
Time }
Time (apply elem_of_dom).
Time eauto.
Time Qed.
Time iSplitL "HP1 HP2".
Time {
Time iExists lsptr , (S q).
Time iFrame.
Time by iFrame.
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
Time }
Time iExists _.
Time iFrame.
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
Time by iFrame.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&(#Hsrc&#Hlocks&#Hinv)) H\206\166".
Time Qed.
Time
Definition MsgInv (\206\147 : gmap uint64 gname) ls uid lm 
  (open : bool) : iProp \206\163 :=
  (\226\136\131 lk \206\179,
     \226\140\156\206\147 !! uid = Some \206\179\226\140\157
     \226\136\151 \226\140\156if open then List.nth_error ls uid = Some lk else True\226\140\157
       \226\136\151 InboxInv uid lk \206\179 (fst lm) (snd lm) open)%I.
Time
Definition MsgInv_weak (\206\147 : gmap uint64 gname) uid 
  lm (open : bool) : iProp \206\163 :=
  (\226\136\131 lk \206\179,
     \226\140\156\206\147 !! uid = Some \206\179\226\140\157 \226\136\151 InboxInv_weak uid lk \206\179 (fst lm) (snd lm) open)%I.
Time rewrite /write.
Time #[global]
Instance MsgInv_weak_timeless  \206\147 uid x open:
 (Timeless (MsgInv_weak \206\147 uid x open)).
Time Proof.
Time rewrite /MsgInv_weak.
Time (apply _).
Time Qed.
Time
Definition userRange_ok (s : gset uint64) :=
  forall uid : uint64, (uid < 100 -> uid \226\136\136 s) /\ (uid >= 100 -> \194\172 uid \226\136\136 s).
Time
Definition RootDirInv (\207\131 : Mail.State) : iProp \206\163 :=
  (rootdir
   \226\134\166{ - 1} (set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
   \226\136\151 \226\140\156userRange_ok (dom (gset uint64) \207\131.(messages))\226\140\157)%I.
Time
Lemma RootDirInv_range_ok \207\131 :
  RootDirInv \207\131 -\226\136\151 \226\140\156userRange_ok (dom (gset _) \207\131.(messages))\226\140\157.
Time Proof.
Time by iIntros "(?&$)".
Time Qed.
Time Lemma userRange_ok_eq s s' : userRange_ok s \226\134\146 userRange_ok s' \226\134\146 s = s'.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>Hok1 Hok2).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>i).
Time clear - Hok1 Hok2.
Time (destruct (Hok1 i) as (Hlt1, Hge1)).
Time (destruct (Hok2 i) as (Hlt2, Hge2)).
Time (destruct (lt_dec i 100) as [Hlt| Hnlt]).
Time -
Time intuition.
Time -
Time (assert (i >= 100) by lia).
Time intuition.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct lt_dec as [Hlt| Hnlt] ; last 
 first).
Time {
Time iApply wp_bind_proc_subst.
Time Qed.
Time
Definition InitInv (\206\147 : gmap uint64 gname) \206\179 \207\131 :=
  (\226\136\131 v : ghost_init_status,
     ghost_mapsto_auth \206\179 v
     \226\136\151 match v with
       | Uninit =>
           ghost_mapsto \206\179 O v
           \226\136\151 \226\140\156\207\131.(open) = false\226\140\157
             \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), \226\136\131 \206\179uid,
                                                 \226\140\156
                                                 \206\147 !! uid = Some \206\179uid\226\140\157
                                                 \226\136\151 
                                                 InboxLockInv \206\179uid O)
       | Started_Init j K => j \226\164\135 K (Call Open) \226\136\151 \226\140\156\207\131.(open) = false\226\140\157
       | Finished_Init => \226\140\156\207\131.(open) = true\226\140\157
       end)%I.
Time iInv "Hinv" as "H".
Time
Definition MsgsInv (\206\147 : gmap uint64 gname) (\206\179 : gname) 
  (\207\131 : Mail.State) : iProp \206\163 :=
  (\226\136\131 ls,
     GlobalInv ls \207\131.(open)
     \226\136\151 RootDirInv \207\131
       \226\136\151 InitInv \206\147 \206\179 \207\131
         \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm \207\131.(open)))%I.
Time
Lemma MsgInv_pers_split \206\147 ls uid lm :
  MsgInv \206\147 ls uid lm true
  -\226\136\151 \226\136\131 lk \206\179,
       \226\140\156\206\147 !! uid = Some \206\179\226\140\157
       \226\136\151 \226\140\156List.nth_error ls uid = Some lk\226\140\157
         \226\136\151 is_lock boxN lk (InboxLockInv \206\179) True.
Time Proof.
Time iIntros "HG".
Time iDestruct "HG" as ( lk \206\179 Hlookup1 Hlookup2 ) "(#Hlock&HI)".
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&?)".
Time iExists _ , _.
Time iFrame "%".
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
Time iFrame "Hlock".
Time Qed.
Time
Lemma MsgsInv_pers_split \206\147 \207\131 ls uid v :
  \207\131.(messages) !! uid = Some v
  \226\134\146 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm true)
    -\226\136\151 \226\136\131 lk \206\179,
         \226\140\156\206\147 !! uid = Some \206\179\226\140\157
         \226\136\151 \226\140\156List.nth_error ls uid = Some lk\226\140\157
           \226\136\151 is_lock boxN lk (InboxLockInv \206\179) True.
Time Proof.
Time iIntros ( ? ) "Hm".
Time (iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time iDestruct (MsgInv_pers_split with "Huid") as "$".
Time (intros [v1 Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time Qed.
Time
Lemma MsgInv_weaken \206\147 lks uid lm open :
  MsgInv \206\147 lks uid lm open -\226\136\151 MsgInv_weak \206\147 uid lm open.
Time Proof.
Time iIntros "H".
Time iDestruct "H" as ( lk \206\179 Hlookup ) "(_&Hinbox)".
Time iDestruct "Hcurr" as ( v0 stat ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time iExists _ , _.
Time (iSplitL ""; auto).
Time iDestruct "Hinbox" as "(?&Hmb&?&?)".
Time iFrame.
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time Qed.
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time #[global]
Instance tmp_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo _ _) :=
 {| generic_mapsto := \206\187 l q v, Count_GHeap.mapsto (hG:=hGTmp) l q v |}%I.
Time
Definition TmpInv : iProp \206\163 :=
  (\226\136\131 tmps_map,
     SpoolDir \226\134\166 dom (gset string) tmps_map
     \226\136\151 SpoolDir \226\134\166 Unlocked
       \226\136\151 gen_heap_ctx tmps_map
         \226\136\151 ([\226\136\151 map] name\226\134\166inode \226\136\136 tmps_map, path.mk SpoolDir name \226\134\166 inode))%I.
Time Definition execN : namespace := nroot.@"msgs_inv".
Time #[global]
Instance InboxLockInv_Timeless  \206\179 n: (Timeless (InboxLockInv \206\179 n)).
Time Proof.
Time (apply _).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time Qed.
Time
Definition ExecInv :=
  (\226\136\131 \206\147 \206\179,
     source_ctx
     \226\136\151 inv execN (\226\136\131 \207\131, source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv))%I.
Time
Definition ExecInner :=
  (\226\136\131 \206\147 \206\179 \207\131,
     \226\140\156\207\131.(open) = false\226\140\157 \226\136\151 source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv)%I.
Time
Lemma GlobalInv_unify lsptr ls ls' :
  global \226\134\166{ - 1} Some lsptr
  -\226\136\151 lsptr \226\134\166{ - 1} (ls, ls) -\226\136\151 GlobalInv ls' true -\226\136\151 \226\140\156ls = ls'\226\140\157.
Time Proof.
Time iIntros "Hgptr Hlsptr HG".
Time (iDestruct "Hstat" as % Heq; subst).
Time iDestruct "HG" as ( lsptr' ? ) "(Hgptr'&Hlsptr')".
Time iApply (wp_write_disk0 with "[$]").
Time rewrite //=.
Time
iDestruct (ghost_var_agree2 (A:=discreteO sliceLockC) with "Hgptr Hgptr'") as
 % Heq.
Time (inversion Heq; subst).
Time (iDestruct (slice_agree with "Hlsptr Hlsptr'") as "(?&?)"; eauto).
Time Qed.
Time
Lemma InboxLockInv_set_msgs \206\179 n S :
  InboxLockInv \206\179 n
  ==\226\136\151 ghost_mapsto_auth \206\179 (A:=discreteO contents) S
      \226\136\151 ghost_mapsto (A:=discreteO contents) \206\179 O S.
Time Proof.
Time iIntros "Hlockinv".
Time iDestruct "Hlockinv" as ( ? ? ) "(H1&H2)".
Time
by iMod (ghost_var_update (A:=discreteO contents) with "H1 H2") as "($&$)".
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
Time Qed.
Time
Lemma slice_mapsto_len {T} (s : slice.t T) (ls0 ls : Datatypes.list T) :
  s \226\134\166 (ls0, ls) -\226\136\151 \226\140\156s.(slice.length) = length ls\226\140\157.
Time Proof.
Time iIntros "Hpts".
Time iDestruct "Hpts" as ( ? ? ) "Hpts".
Time iPureIntro.
Time symmetry.
Time (eapply getSliceModel_len_inv; eauto).
Time Qed.
Time
Lemma slice_mapsto_len' {T} (s : slice.t T) (ls : Datatypes.list T) :
  s \226\134\166 ls -\226\136\151 \226\140\156s.(slice.length) = length ls\226\140\157.
Time Proof.
Time iIntros "Hpts".
Time iDestruct "Hpts" as ( ? ? ) "Hpts".
Time iPureIntro.
Time symmetry.
Time (eapply getSliceModel_len_inv; eauto).
Time Qed.
Time
Definition writeBuf {model : GoModel} f (data : slice.t byte) :=
  (Loop
     (fun buf =>
      if compare_to (slice.length buf) 4096 Lt
      then _ <- FS.append f buf; LoopRet tt
      else _ <- FS.append f (slice.take 4096 buf);
           Continue (slice.skip 4096 buf)) data)%proc.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth Hj Hreg".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time
Lemma slice_take_split {A} k data (bs0 bs : List.list A) 
  q :
  k \226\137\164 data.(slice.length)
  \226\134\146 data \226\134\166{ q} (bs0, bs)
    -\226\136\151 slice.take k data \226\134\166{ q} (bs0, take k bs)
       \226\136\151 (slice.take k data \226\134\166{ q} (bs0, take k bs) -\226\136\151 data \226\134\166{ q} (bs0, bs)).
Time Proof.
Time iIntros ( Hlen ) "H".
Time iFrame.
Time iDestruct "H" as ( HgetSlice ) "H".
Time iSplitL "H".
Time iFrame.
Time *
Time iFrame.
Time iPureIntro.
Time move : {}HgetSlice {}.
Time rewrite /Data.getSliceModel //=.
Time rewrite /sublist_lookup /mguard /option_guard.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by inversion 1).
Time (<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by lia).
Time (inversion 1).
Time subst.
Time f_equal.
Time rewrite take_take.
Time f_equal.
Time lia.
Time *
Time iIntros "H".
Time iDestruct "H" as ( HgetSlice' ) "H".
Time (simpl).
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma skipn_firstn_comm' {A} (m n : nat) (l : Datatypes.list A) :
  drop m (take n l) = take (n - m) (drop m l).
Time Proof.
Time revert n l.
Time (induction m; intros [] []; rewrite ?skipn_O -?minus_n_O ?take_nil //=).
Time Qed.
Time
Lemma slice_skip_split {A} k data (bs0 bs : List.list A) 
  q :
  k \226\137\164 data.(slice.length)
  \226\134\146 data \226\134\166{ q} (bs0, bs)
    -\226\136\151 slice.skip k data \226\134\166{ q} (bs0, drop k bs)
       \226\136\151 (slice.skip k data \226\134\166{ q} (bs0, drop k bs) -\226\136\151 data \226\134\166{ q} (bs0, bs)).
Time Proof.
Time iIntros ( Hlen ) "H".
Time iDestruct "H" as ( HgetSlice ) "H".
Time iSplitL "H".
Time *
Time iFrame.
Time iPureIntro.
Time move : {}HgetSlice {}.
Time rewrite /Data.getSliceModel //=.
Time rewrite /sublist_lookup /mguard /option_guard.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by inversion 1).
Time clear.
Time iClear "Hlocks".
Time (<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by lia).
Time auto.
Time }
Time iModIntro.
Time wp_bind.
Time (inversion 1).
Time subst.
Time f_equal.
Time rewrite skipn_firstn_comm' drop_drop //.
Time *
Time iIntros "H".
Time iDestruct "H" as ( HgetSlice' ) "H".
Time iInv "Hinv" as "H".
Time (simpl).
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma wp_writeBuf f data inode bs0 bs1 bs2 q :
  {{{ f \226\134\166 (inode, Write) \226\136\151 inode \226\134\166 bs1 \226\136\151 data \226\134\166{ q} (bs0, bs2) }}} 
  writeBuf f data {{{ RET tt; f \226\134\166 (inode, Write)
                              \226\136\151 inode \226\134\166 (bs1 ++ bs2) \226\136\151 data \226\134\166{ q} (bs0, bs2)}}}.
Time clear \207\131 Hdom1 Hlookup Heq.
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time Proof.
Time rewrite /writeBuf.
Time rewrite -MAX_WRITE_LEN_unfold.
Time iIntros ( \206\166 ) "(Hf&Hinode&Hdata) H\206\166".
Time iL\195\182b as "IH" forall ( data bs1 bs2 q ).
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time wp_loop.
Time (intros [v1' Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_insert_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time (destruct compare_to).
Time -
Time wp_bind.
Time iDestruct "Hcurr" as ( ? ? ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time iAssert \226\140\156length bs2 < MAX_WRITE_LEN\226\140\157%I with "[-]" as "%".
Time {
Time iDestruct "Hdata" as "(%&?)".
Time iPureIntro.
Time (erewrite getSliceModel_len_inv; eauto).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_append with "[$]") ; first  by
 lia).
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time iApply (wp_write_disk1 with "[$]").
Time iIntros "!> H".
Time (do 2 wp_ret).
Time by iApply "H\206\166".
Time -
Time wp_bind.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (slice_take_split MAX_WRITE_LEN with "Hdata") as "(Htake&Hwand)" ; first  by
 lia).
Time iApply (wp_append with "[$]").
Time iIntros "!> (Hd1&Hl1)".
Time
iMod (gen_heap_update' _ _ Sync with "[$] [Hstatus Hstatus_auth]") as
 "(?&Hstatus)".
Time {
Time rewrite take_length.
Time lia.
Time }
Time iIntros "!> (Hf&Hinode&Hdata)".
Time iDestruct ("Hwand" with "Hdata") as "Hdata".
Time wp_ret.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (slice_skip_split MAX_WRITE_LEN with "Hdata") as "(Hdrop&Hwand)" ; first  by
 lia).
Time iApply ("IH" with "Hf Hinode Hdrop [H\206\166 Hwand]").
Time iIntros "!> (Hf&Hinode&Hdata)".
Time iDestruct ("Hwand" with "Hdata") as "Hdata".
Time iApply "H\206\166".
Time iFrame.
Time rewrite -app_assoc take_drop //.
Time Qed.
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
Time
Definition readMessage_handle f :=
  (fileContents <- Data.newPtr (slice.t byte);
   initData <- Data.newSlice byte 0;
   _ <-
   Loop
     (fun pf =>
      buf <- FS.readAt f pf.(partialFile.off) 512;
      newData <- Data.sliceAppendSlice pf.(partialFile.data) buf;
      if compare_to (slice.length buf) 512 Lt
      then _ <- Data.writePtr fileContents newData; LoopRet tt
      else Continue
             {|
             partialFile.off := pf.(partialFile.off) + slice.length buf;
             partialFile.data := newData |})
     {| partialFile.off := 0; partialFile.data := initData |};
   fileData <- Data.readPtr fileContents;
   fileStr <- Data.bytesToString fileData; _ <- FS.close f; Ret fileStr)%proc.
Time
Lemma readMessage_unfold_open userDir name :
  readMessage userDir name =
  (let! f <- FS.open userDir name; readMessage_handle f)%proc.
Time Proof.
Time auto.
Time Qed.
Time Opaque readMessage.
Time
Lemma take_length_lt {A} (l : Datatypes.list A) (n : nat) :
  length (take n l) < n \226\134\146 take n l = l.
Time Proof.
Time (intros Hlen).
Time (apply take_ge).
Time rewrite take_length in  {} Hlen.
Time lia.
Time Qed.
Time
Lemma wp_readMessage_handle f inode ls q2 :
  {{{ f \226\134\166 (inode, Read) \226\136\151 inode \226\134\166{ q2} ls }}} readMessage_handle f {{{ RET 
  bytes_to_string ls; inode \226\134\166{ q2} ls}}}.
Time Proof.
Time rewrite /readMessage_handle.
Time (<ssreflect_plugin::ssrtclintros@0> generalize 512 =>k).
Time iIntros ( \206\166 ) "(Hf&Hinode) H\206\166".
Time wp_bind.
Time iApply (wp_newAlloc with "[//]").
Time iIntros ( fileContents ) "!> HfC".
Time wp_bind.
Time iApply (@wp_newSlice with "[//]").
Time iIntros ( fileSlice ) "!> HfS".
Time (simpl repeat).
Time replace [] with take 0 ls by auto.
Time (<ssreflect_plugin::ssrtclintros@0> generalize 0 =>idx).
Time wp_bind.
Time iAssert (fileSlice \226\134\166 take idx ls)%I with "[HfS]" as "HfS".
Time {
Time (iExists _; eauto).
Time }
Time iL\195\182b as "IH" forall ( fileSlice idx ).
Time wp_loop.
Time wp_bind.
Time iApply (wp_readAt with "[$]").
Time rewrite upd_disk_dom.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iModIntro.
Time iNext.
Time rewrite /OneDisk.upd_disk /OneDisk.upd_default /= Hlookup.
Time iApply "Hdur".
Time iExists _ , _.
Time iIntros ( s ) "!> (Hf&Hinode&Hs)".
Time iFrame.
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time }
Time iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
Time {
Time iFrame "Hlock".
Time wp_bind.
Time iApply (wp_sliceAppendSlice with "[HfS Hs]").
Time iFrame.
Time {
Time iFrame.
Time (iExists _; iFrame).
Time }
Time iIntros "!> _".
Time iApply "H\206\166".
Time iFrame.
Time Qed.
Time }
Time (simpl).
Time clear fileSlice.
Time iIntros ( fileSlice ) "!> (HfS&Hs)".
Time iDestruct (slice_mapsto_len with "Hs") as % ->.
Time iClear "Hs".
Time (destruct lt_dec as [Hlt| Hnlt]).
Time -
Time wp_bind.
Time iApply (wp_writePtr with "[$]").
Time iIntros "!> HfC".
Time wp_ret.
Time iNext.
Time wp_ret.
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time iIntros "!> HfC".
Time wp_bind.
Time iApply (wp_bytesToString' with "HfS").
Time iIntros "!> _".
Time wp_bind.
Time iApply (wp_close with "Hf").
Time iIntros "!> _".
Time wp_ret.
Time (apply take_length_lt in Hlt).
Time rewrite Hlt.
Time rewrite take_drop.
Time iApply "H\206\166".
Time iFrame.
Time -
Time wp_ret.
Time iNext.
Time
Lemma read_refinement {T} j K `{LanguageCtx OneDisk.Op nat T OneDisk.l K} 
  a :
  {{{ j \226\164\135 K (Call (OneDisk.Read_Disk a)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  read a {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&(#Hsrc&#Hlocks&#Hinv)) H\206\166".
Time iApply ("IH" with "[$] [$] [$] [$]").
Time rewrite /read.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct lt_dec as [Hlt| Hnlt] ; last 
 first).
Time {
Time iApply wp_bind_proc_subst.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&?)".
Time rewrite take_take_drop.
Time
(<ssreflect_plugin::ssrtclseq@0>
 assert (length (take k (drop idx ls)) = k) as -> ; last  by eauto).
Time iDestruct "Hdom1" as % Hdom1.
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time
(<ssreflect_plugin::ssrtclseq@0> cut (length (take k (drop idx ls)) \226\137\164 k) ;
 first  by lia).
Time (eapply firstn_le_length).
Time Qed.
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
Time
Lemma createMessages_length msgs : length (createMessages msgs) = length msgs.
Time Proof.
Time by rewrite map_length.
Time Qed.
Time
Lemma nth_error_map {A B : Type} (f : A \226\134\146 B) (n : nat) 
  l (b : B) :
  nth_error (map f l) n = Some b \226\134\146 \226\136\131 a, f a = b \226\136\167 nth_error l n = Some a.
Time Proof.
Time revert l.
Time (<ssreflect_plugin::ssrtclintros@0> induction n =>l //=).
Time *
Time (<ssreflect_plugin::ssrtclintros@0> destruct l as [| a l] =>//=).
Time (intros).
Time (exists a; split; congruence).
Time *
Time (<ssreflect_plugin::ssrtclintros@0> destruct l as [| a l] =>//=).
Time (intros).
Time eauto.
Time Qed.
Time
Lemma take_snoc_S {A} (ls : List.list A) (i : nat) 
  a : nth_error ls i = Some a \226\134\146 take (i + 1) ls = take i ls ++ [a].
Time Proof.
Time (intros Hin).
Time revert ls Hin.
Time (<ssreflect_plugin::ssrtclintros@0> induction i =>ls Hin).
Time -
Time rewrite //=.
Time (destruct ls; inversion Hin; subst).
Time (simpl).
Time by rewrite firstn_O.
Time -
Time rewrite //=.
Time (destruct ls; inversion Hin).
Time (simpl).
Time f_equal.
Time eauto.
Time Qed.
Time
Lemma writeTmp_unfold_writeBuf msg :
  writeTmp msg =
  (let! (f, name) <- createTmp; _ <- writeBuf f msg; _ <- close f; Ret name)%proc.
Time Proof.
Time trivial.
Time Qed.
Time Opaque writeTmp.
Time #[global]
Instance ghost_init_status_inhabited : (Inhabited ghost_init_status).
Time Proof.
Time econstructor.
Time exact Uninit.
Time Qed.
Time Lemma userRange_in_elim s k : userRange_ok s \226\134\146 k \226\136\136 s \226\134\146 k < NumUsers.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>Hrange ?).
Time (destruct (lt_dec k NumUsers) as [?| Hn]; auto).
Time (assert (k \226\137\165 NumUsers) by lia).
Time (exfalso; eapply Hrange; eauto).
Time Qed.
Time
Lemma nth_error_snoc {A : Type} (l : List.list A) 
  (a : A) : nth_error (l ++ [a]) (length l) = Some a.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> induction l =>//=).
Time Qed.
Time
Lemma nth_error_snoc_ne {A : Type} (l : List.list A) 
  (a : A) k : k \226\137\160 length l \226\134\146 nth_error (l ++ [a]) k = nth_error l k.
Time Proof.
Time (intros Hneq).
Time (destruct (lt_dec k (length l)) as [?| Hgt]).
Time -
Time rewrite nth_error_app1 //.
Time -
Time (assert (length l < k) by lia).
Time etransitivity.
Time *
Time (eapply nth_error_None).
Time rewrite app_length //=.
Time lia.
Time *
Time symmetry.
Time (eapply nth_error_None).
Time lia.
Time Qed.
Time
Lemma open_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} :
  {{{ j \226\164\135 K (Call Open) \226\136\151 Registered \226\136\151 ExecInv }}} MailServer.Open {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 \206\179 ) "(#Hsource&#Hinv)".
Time rewrite /MailServer.Open.
Time wp_bind.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iIntros ( mv ) "!> (Hd0&Hret)".
Time iDestruct "Hmsgs" as ( ls ) "(Hglobal&>Hrootdir&Hinit&Hm)".
Time (destruct mv as [v| ]).
Time -
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time iDestruct (RootDirInv_range_ok with "Hrootdir") as % Hrange_ok.
Time iDestruct "Hinit" as ( init_stat ) "Hinit".
Time iMod (open_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)".
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
Time {
Time solve_ndisj.
Time }
Time (destruct init_stat; swap 1 3).
Time {
Time iDestruct "Hinit" as ">(?&%)".
Time exfalso.
Time congruence.
Time }
Time {
Time iDestruct "Hinit" as ">(?&Hj'&%)".
Time iMod (open_open_step_inv with "Hj Hj' [$] [$]").
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
Time {
Time solve_ndisj.
Time }
Time iModIntro.
Time wp_ret.
Time wp_bind.
Time }
Time eauto.
Time iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
Time }
Time iDestruct "Hinit" as ">(Hauth&Hfrag&%&Hghosts)".
Time {
Time iFrame "Hlock".
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  by auto).
Time iFrame.
Time iIntros ( locks0 ) "!> Hlocks0".
Time (iExists _; iFrame).
Time }
Time iIntros "!> _".
Time iExists _.
Time iFrame.
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
Time iExists _.
Time iFrame.
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
Time
iMod (ghost_var_update (A:=ghost_init_statusC) with "[$] [$]") as
 "(Hauth&Hfrag)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time (iDestruct "Hstat" as % Heq; subst).
Time iApply (wp_read_disk1_only1 with "[$]").
Time iSplitL "Hauth Hj".
Time {
Time iExists (Started_Init _ _).
Time iFrame.
Time iIntros "!> Hd1".
Time eauto.
Time }
Time iModIntro.
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply @wp_newSlice ; first  by auto).
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time iIntros ( locks ) "!> Hlocks".
Time wp_bind.
Time iApply (wp_writePtr with "[$]").
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
Time iIntros "!> Hlocks0".
Time (simpl repeat).
Time wp_bind.
Time (remember (@nil LockRef) as lock_list eqn:Heq_lock_list ).
Time
(<ssreflect_plugin::ssrtclseq@0> replace 0 with length lock_list 
  at 1 ; last  first).
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
Time {
Time rewrite Heq_lock_list //.
Time }
Time iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
Time
iAssert
 ([\226\136\151 set] k \226\136\136 dom (gset _) \207\131.(messages), \226\136\131 \206\179uid : gname,
                                           \226\140\156\206\147 !! k = Some \206\179uid\226\140\157
                                           \226\136\151 match nth_error lock_list k with
                                             | Some lk =>
                                                 is_lock boxN lk
                                                 (InboxLockInv \206\179uid) True
                                             | None => InboxLockInv \206\179uid 0
                                             end)%I with "[Hghosts]" as
 "Hghosts".
Time iFrame.
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_mono ; last  auto).
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
Time iIntros ( k Hin ) "H".
Time iDestruct "H" as ( \206\179uid ) "(Heq&Hlock)".
Time (iExists _; iFrame).
Time rewrite Heq_lock_list.
Time (destruct k; auto).
Time }
Time
(assert (Hlen : length lock_list <= NumUsers) by
  (rewrite Heq_lock_list; cbn[length]; lia)).
Time clear Heq_lock_list.
Time iL\195\182b as "IH" forall ( lock_list locks Hlen ).
Time wp_loop.
Time (destruct equal).
Time -
Time iClear "IH".
Time wp_ret.
Time wp_ret.
Time iIntros "!>".
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time iIntros "!> Hlocks0".
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131' ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iDestruct "Hmsgs" as ( ls' ) "(Hglobal&>Hrootdir&Hinit&Hm)".
Time iDestruct (RootDirInv_range_ok with "Hrootdir") as % Hrange_ok'.
Time iDestruct "Hinit" as ( init_stat ) "Hinit".
Time iDestruct "Hinit" as "(>Hauth&Hinit)".
Time
iDestruct (ghost_var_agree (A:=ghost_init_statusC) with "Hauth Hfrag") as %
 Heq.
Time #[global]
Instance DisksInv_Timeless  (P : iProp \206\163) {HT : Timeless P}:
 (Timeless (DisksInv P)).
Time subst.
Time iDestruct "Hinit" as ">(Hj&Hopen')".
Time iDestruct "Hopen'" as % Hopen'.
Time rewrite Hopen'.
Time (simpl GlobalInv).
Time iDestruct "Hglobal" as ">Hglobal".
Time Proof.
Time (apply _).
Time iApply (wp_setX with "[$]").
Time Qed.
Time End refinement_triples.
Time iIntros "!> Hglobal".
Time rewrite (userRange_ok_eq _ _ Hrange_ok Hrange_ok').
Time
iAssert
 ([\226\136\151 set] k \226\136\136 dom (gset uint64) \207\131'.(messages), \226\136\131 \206\179uid lk,
                                                 \226\140\156
                                                 \206\147 !! k = Some \206\179uid\226\140\157
                                                 \226\136\151 
                                                 \226\140\156
                                                 lock_list !! k = Some lk\226\140\157
                                                 \226\136\151 
                                                 is_lock boxN lk
                                                 (InboxLockInv \206\179uid) True)%I
 with "[Hghosts]" as "Hghosts".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_mono ; last  eauto).
Time iIntros ( k Hin ) "H".
Time iDestruct "H" as ( \206\179uid Heq ) "H".
Time iExists \206\179uid.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct nth_error as [lk| ] eqn:Heq_nth_error ; last  first).
Time {
Time exfalso.
Time rewrite nth_error_None in  {} Heq_nth_error *.
Time (eapply userRange_in_elim in Hin; auto).
Time rewrite e.
Time lia.
Time }
Time iExists lk.
Time (iSplitL ""; auto).
Time (iSplitL ""; auto).
Time iPureIntro.
Time rewrite -nth_error_lookup //.
Time }
Time iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (do 2 eexists; split).
Time {
Time rewrite /reads Hopen'.
Time eauto.
Time }
Time (do 2 econstructor; split; econstructor).
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
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
Time iExists lock_list.
Time iFrame.
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
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "Hj H\206\166 Hreg" ; last  first).
Time {
Time iModIntro.
Time (iApply "H\206\166"; iFrame).
Time }
Time iExists _ , O.
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
iMod (ghost_var_update (A:=ghost_init_statusC) with "Hauth Hfrag") as
 "(Hauth&Hfrag)".
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( v0' stat ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time iSplitL "Hrootdir".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time {
Time iModIntro.
Time rewrite /RootDirInv.
Time (simpl).
Time (rewrite dom_fmap_L //; eauto).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time }
Time iSplitL "Hauth".
Time {
Time iExists Finished_Init.
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time iFrame.
Time eauto.
Time }
Time iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
Time iApply (wp_read_disk0 with "[$]").
Time iDestruct (big_sepM_sep with "[Hm Hghosts]") as "Hm".
Time {
Time iFrame.
Time }
Time iModIntro.
Time iNext.
Time rewrite big_sepM_fmap.
Time (iApply big_sepM_mono; iFrame).
Time iIntros ( k (mstat, msgs) Hin ) "(H1&H2)".
Time iIntros ( mv ) "!> (Hd0&Hret)".
Time iDestruct "H1" as ( \206\179' lk' ? ? ) "H".
Time (simpl).
Time iDestruct "H2" as ( ? ? _ _ _ ) "((Hinterp&?)&?&Hin)".
Time iExists _ , _.
Time rewrite nth_error_lookup.
Time (iSplitL ""; auto).
Time (destruct mv as [v| ]).
Time *
Time iSplitL "Hstate Hctx_stat Hdur Hd0 Hd1 Hstatus_auth Hstat".
Time {
Time iExists _.
Time iFrame.
Time (iSplitL ""; auto).
Time iFrame.
Time -
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time by iFrame.
Time iIntros "!> Hlocks0".
Time wp_bind.
Time (assert (length lock_list \226\136\136 dom (gset uint64) \207\131.(messages))).
Time {
Time (eapply Hrange_ok).
Time move : {}Hlen {}n {}.
Time rewrite /NumUsers.
Time (inversion 1; eauto).
Time *
Time congruence.
Time *
Time subst.
Time lia.
Time }
Time iModIntro.
Time }
Time iDestruct (big_sepS_delete with "Hghosts") as "(Huid&Hghosts)".
Time wp_bind.
Time wp_ret.
Time iInv "Hinv" as ">H".
Time {
Time eauto.
Time }
Time iDestruct "Huid" as ( \206\179uid Heq_\206\179uid ) "Hlockinv".
Time (assert (nth_error lock_list (length lock_list) = None) as ->).
Time {
Time (apply nth_error_None).
Time trivial.
Time }
Time
iApply (wp_newLock boxN _ _ (InboxLockInv \206\179uid) True%I with "[Hlockinv]").
Time {
Time iFrame.
Time iSplitL "".
Time -
Time iModIntro.
Time by iIntros ( i ) "$".
Time -
Time iModIntro.
Time clear \207\131 Hdom1 Hlookup.
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time by iIntros ( i ) "(?&$)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hin =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time }
Time iIntros ( lk ) "!> #His_lock".
Time (intros [v1'' Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_insert_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time iDestruct "Hcurr" as ( v0'' stat' ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time wp_bind.
Time iApply (wp_sliceAppend with "[$]").
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time iApply (wp_write_disk1 with "[$]").
Time iIntros ( locks' ) "!> Hlocks'".
Time wp_bind.
Time iApply (wp_writePtr with "[$]").
Time (iDestruct "Hret" as % Heq; subst).
Time iIntros "!> Hlocks0".
Time iIntros "!> (Hd1&Hl1)".
Time
iMod (gen_heap_update' _ _ Sync with "Hctx_stat [Hstatus Hstatus_auth]") as
 "(Hctx_stat&Hstatus)".
Time wp_ret.
Time
(<ssreflect_plugin::ssrtclseq@0> replace (length lock_list + 1) with
 length (lock_list ++ [lk]) ; last  first).
Time {
Time rewrite app_length //=.
Time }
Time iApply ("IH" with "[] [$] [$] [$] [$] [$] [Hghosts]").
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
Time iPureIntro.
Time rewrite app_length //=.
Time (inversion Hlen; eauto).
Time *
Time congruence.
Time *
Time subst.
Time rewrite /NumUsers.
Time lia.
Time }
Time iApply (big_sepS_delete with "[Hghosts]").
Time {
Time eauto.
Time }
Time {
Time iSplitL "".
Time -
Time iExists \206\179uid.
Time (iSplitL ""; auto).
Time rewrite nth_error_snoc //.
Time -
Time iApply (big_sepS_mono with "Hghosts").
Time iIntros ( k Hin ) "H".
Time iDestruct "H" as ( \206\179uid' ? ) "H".
Time iExists \206\179uid'.
Time (iSplitL ""; auto).
Time (rewrite nth_error_snoc_ne; eauto).
Time set_solver.
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
Time Qed.
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
Time
Lemma wp_createTmp \206\147 \206\179 :
  {{{ inv execN
        (\226\136\131 \207\131 : l.(OpState),
           source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv) }}} createTmp {{{ 
  (f : File)name(inode : Inode),  RET (f, name); name \226\134\166 inode
                                                 \226\136\151 
                                                 inode \226\134\166 []
                                                 \226\136\151 
                                                 f \226\134\166 (inode, Write)}}}.
Time Proof.
Time iIntros ( \206\166 ) "#Hinv H\206\166".
Time rewrite /createTmp.
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
Time iIntros ( id ) "!> _".
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  auto).
Time iIntros ( finalName ) "!> HfinalName".
Time (simpl repeat).
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  auto).
Time iIntros ( finalFile ) "!> HfinalFile".
Time wp_bind.
Time iL\195\182b as "IH" forall ( id ).
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iSpecialize ("Hdur" $! v1).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_id ; last  auto).
Time wp_loop.
Time iApply "Hdur".
Time iExists v1 , Sync.
Time wp_bind.
Time iFrame.
Time rewrite /ExecInv.
Time (iFastInv "Hinv" "H").
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
iDestruct "Htmp" as ( tmps_map ) "(Hspool&Hspool_unlocked&Htmp_auth&Htmps)".
Time rewrite /status_interp.
Time
(destruct
  (decide (gmodel.(@uint64_to_string) id \226\136\136 dom (gset string) tmps_map))
  as [Hin| Hfresh]).
Time auto.
Time }
Time wp_bind.
Time wp_ret.
Time *
Time iApply (wp_create_not_new with "[Hspool]").
Time wp_ret.
Time {
Time iFrame.
Time eauto.
Time iModIntro.
Time }
Time iIntros ( ? ) "!> Hspool".
Time iApply ("IH" with "[] Hreg [Hrest Hl0 Hl1 Hstatus Hmem]").
Time {
Time iPureIntro.
Time lia.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_delete ; first  eauto).
Time iSplitR "Hrest".
Time {
Time (destruct lt_dec; try lia; [  ]).
Time iExists _.
Time iFrame.
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
Time iExists _.
Time iFrame.
Time iModIntro.
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
Time iIntros ( id' ) "!> _".
Time wp_ret.
Time iNext.
Time iApply ("IH" with "H\206\166 [$] [$]").
Time *
Time iApply (wp_create_new with "[Hspool]").
Time {
Time iFrame.
Time eauto.
Time }
Time iIntros ( inode f ) "!> (Hf&Hinode&Hspool&Hpath)".
Time
iMod
 (gen_heap_alloc tmps_map (gmodel.(@uint64_to_string) id) inode
 with "Htmp_auth") as "(Htmp_auth&Htmp_frag)".
Time {
Time (eapply not_elem_of_dom; eauto).
Time }
Time iExists _.
Time iFrame.
Time iPoseProof (big_sepM_insert_2 with "[Hpath] Htmps") as "Htmps".
Time {
Time iApply "Hpath".
Time }
Time iExists _.
Time iFrame.
Time rewrite dom_insert_L comm_L.
Time iFrame.
Time iModIntro.
Time wp_bind.
Time Lemma init_wf : \226\136\128 \207\1311a \207\1311c, init_absr \207\1311a \207\1311c \226\134\146 \207\1311c = TwoDisk.init_state.
Time iApply (wp_writePtr with "HfinalName").
Time iIntros "!> HfinalName".
Time wp_bind.
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
Time iApply (wp_writePtr with "HfinalFile").
Time
iMod (gen_heap_strong_init ((\206\187 x, Sync) <$> init_zero)) as ( hS <- )
 "(hS&hSfrag)".
Time iPoseProof (gen_heap_init_to_bigOp (hG:=hS) with "hSfrag") as "hSfrag".
Time iEval rewrite big_sepM_sep in "Hdisk0".
Time iIntros "!> HfinalFile".
Time iDestruct "Hdisk0" as "(Hd0&HL0)".
Time iEval rewrite big_sepM_sep in "Hdisk1".
Time wp_ret.
Time iDestruct "Hdisk1" as "(Hd1&HL1)".
Time iNext.
Time iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
Time rewrite big_opM_fmap.
Time wp_ret.
Time wp_bind.
Time iExists hS.
Time rewrite /ExecInner.
Time iSplitL "Hmem HL0 HL1 hSa".
Time {
Time iModIntro.
Time iApply big_opM_dom.
Time iApply (wp_readPtr with "HfinalName").
Time iIntros "!> HfinalName".
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time wp_bind.
Time iApply (wp_readPtr with "HfinalFile").
Time iIntros "!> _".
Time wp_ret.
Time (iApply "H\206\166"; by iFrame).
Time iApply (big_sepM_mono with "H").
Time iIntros ( k x Hlookup ) "(((?&?)&?)&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time Qed.
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
Time
Lemma TmpInv_path_acc name inode :
  name \226\134\166 inode
  -\226\136\151 TmpInv
     -\226\136\151 name \226\134\166 inode
        \226\136\151 path.mk SpoolDir name \226\134\166 inode
          \226\136\151 (path.mk SpoolDir name \226\134\166 inode -\226\136\151 TmpInv).
Time Proof.
Time iIntros "Hn Htmp".
Time rewrite /TmpInv.
Time iDestruct "Htmp" as ( tmp_map ) "(?&?&Htmp_auth&Hpaths)".
Time iDestruct "Hdom1" as % Hdom1.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iDestruct (@gen_heap_valid with "[$] [$]") as % Hlookup.
Time iIntros ( ? ? ) "Hmem".
Time iDestruct "Hctx_stat" as ( \207\131S HdomS ) "Hctx_stat".
Time iMod (gen_heap_strong_init \207\131S) as ( hS' <- ) "(hS&hSfrag)".
Time
(iDestruct (@big_sepM_lookup_acc with "[$]") as "(Hpath&Hpaths)"; eauto).
Time iPoseProof (gen_heap_init_to_bigOp (hG:=hS') with "hSfrag") as "hSfrag".
Time iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
Time iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
Time rewrite ?HdomS.
Time iDestruct (big_sepM_dom with "hSa") as "hSa".
Time iFrame.
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
Time iIntros.
Time iExists _.
Time iFrame.
Time by iApply "Hpaths".
Time Qed.
Time iMod (disk1_next with "[$]") as "(Hd1&Hl1)".
Time
Lemma MailboxStatusInterp_insert uid lk \206\179 mstat mbox 
  name body :
  mbox !! name = None
  \226\134\146 MailboxStatusInterp uid lk \206\179 mstat mbox true
    -\226\136\151 MailboxStatusInterp uid lk \206\179 mstat (<[name:=body]> mbox) true.
Time Proof.
Time iIntros ( Hfresh ) "Hinterp".
Time (destruct mstat; auto).
Time iDestruct "Hinterp" as "($&HS)".
Time iDestruct "HS" as ( S ) "(Hauth&%)".
Time (iExists _; iFrame).
Time iPureIntro.
Time (<ssreflect_plugin::ssrtclseq@0> etransitivity ; first  eauto).
Time (apply insert_subseteq; eauto).
Time Qed.
Time
Lemma TmpInv_path_delete name inode :
  name \226\134\166 inode
  -\226\136\151 TmpInv
     -\226\136\151 |==> \226\136\131 S : gset string,
               path.mk SpoolDir name \226\134\166 inode
               \226\136\151 SpoolDir \226\134\166 S
                 \226\136\151 SpoolDir \226\134\166 Unlocked
                   \226\136\151 (SpoolDir \226\134\166 (S \226\136\150 {[name]})
                      -\226\136\151 SpoolDir \226\134\166 Unlocked -\226\136\151 TmpInv).
Time Proof.
Time iIntros "Hn Htmp".
Time rewrite /TmpInv.
Time iDestruct "Htmp" as ( tmp_map ) "(?&?&Htmp_auth&Hpaths)".
Time iDestruct (@gen_heap_valid with "[$] [$]") as % Hlookup.
Time iMod (@gen_heap_dealloc with "[$] [$]") as "Htmp_auth".
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
Time (iDestruct (big_sepM_delete with "Hpaths") as "(Hcurr&Hpaths)"; eauto).
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
Time iExists _.
Time iFrame.
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iIntros "!> ??".
Time iExists (map_delete name tmp_map).
Time rewrite dom_delete_L.
Time iFrame.
Time rewrite /UnlockedInv.
Time iApply (big_sepM_mono with "H").
Time Qed.
Time iIntros ( k x Hlookup ) "((Hs&Hl)&H2)".
Time iDestruct "Hs" as ( ? ) "(%&Hs)".
Time iDestruct "Hl" as ( v1 v2 ) "(Hl0&Hl1)".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time
Lemma InitInv_open_update \206\147 \206\179 \207\131 \207\131' :
  \207\131.(open) = true \226\134\146 \207\131'.(open) = true \226\134\146 InitInv \206\147 \206\179 \207\131 -\226\136\151 InitInv \206\147 \206\179 \207\131'.
Time Proof.
Time iIntros ( Ho1 Ho2 ) "H".
Time iDestruct "H" as ( v ) "(?&H)".
Time (destruct v).
Time -
Time iDestruct "H" as "(?&%&?)".
Time congruence.
Time -
Time iDestruct "H" as "(?&%)".
Time congruence.
Time -
Time rewrite /InitInv.
Time iExists _ , _ , _.
Time iExists Finished_Init.
Time iFrame.
Time eauto.
Time Qed.
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
Time
Lemma deliver_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid msg :
  {{{ j \226\164\135 K (deliver uid msg) \226\136\151 Registered \226\136\151 ExecInv }}} 
  MailServer.Deliver uid msg {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
Time wp_bind.
Time wp_ret.
Time }
Time iSplitL "hS".
Time {
Time iExists _.
Time iFrame.
Time rewrite -fupd_wp.
Time by iPureIntro.
Time }
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iDestruct (big_sepM_mono_with_inv with "Hctx_stat H") as "(?&$)".
Time iIntros ( k x Hlookup ) "H".
Time rewrite /deliver.
Time iDestruct "H" as "(Hctx_stat&H&Hdur)".
Time
iMod
 (deliver_start_step_inv_do j
    (\206\187 x, K (Bind x (\206\187 x, Call (Deliver_End uid msg))))
 with "Hj Hsource Hstate") as ( s alloc vs s' Heq ) "(Hj&Hstate)".
Time iDestruct "H" as ( stat0 ) "(%&Hs)".
Time iDestruct "Hdur" as ( ? stat ) "(Hd0&Hd1&Hs'&Hstatus)".
Time iDestruct (@gen_heap_valid with "Hctx_stat Hs'") as % ?.
Time
(repeat
  match goal with
  | H1:?x = Some ?y, H2:?x = Some ?z
    |- _ => rewrite H1 in  {} H2; inversion H2; clear H1 H2; subst
  end).
Time {
Time solve_ndisj.
Time iFrame.
Time }
Time iMod (ghost_step_bind_ret with "Hj Hsource") as "Hj".
Time {
Time solve_ndisj.
Time }
Time (destruct Heq as (Heq1, (Heq2, Heq3))).
Time iExists _.
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time
iDestruct (big_sepDM_insert_acc (dec:=sigPtr_eq_dec) with "Hheap") as
 "((Hp&%)&Hheap)".
Time {
Time eauto.
Time }
Time
iAssert
 (\226\150\183 HeapInv
      (RecordSet.set heap
         (RecordSet.set Data.allocs (updDyn msg.(slice.ptr) (s', alloc))) \207\131)
  \226\136\151 msg.(slice.ptr) \226\134\166{ - 1} alloc)%I with "[Hp Hheap]" as "($&Hp)".
Time {
Time (destruct s; inversion Heq3).
Time (destruct stat; auto).
Time (iDestruct "Hstatus" as "(?&?)"; iFrame).
Time *
Time (simpl).
Time iDestruct (Count_Typed_Heap.read_split_join with "Hp") as "(Hp&$)".
Time Qed.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  eauto).
Time (iApply "Hheap"; eauto).
Time *
Time (simpl).
Time iDestruct (Count_Typed_Heap.read_split_join with "Hp") as "(Hp&$)".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  eauto).
Time (iApply "Hheap"; eauto).
Time }
Time iModIntro.
Time iModIntro.
Time rewrite writeTmp_unfold_writeBuf.
Time wp_bind.
Time wp_bind.
Time iApply (wp_createTmp with "Hinv").
Time iIntros ( f name inode ) "!> (Hghost&Hinode&Hf)".
Time wp_bind.
Time iApply (wp_writeBuf with "[Hf Hinode Hp]").
Time {
Time iFrame.
Time eauto.
Time }
Time iIntros "!> (Hf&Hinode&Hp)".
Time wp_bind.
Time iApply (wp_close with "[$]").
Time iIntros "!> _".
Time wp_ret.
Time rewrite app_nil_l.
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
Time iIntros ( id ) "!> _".
Time wp_bind.
Time iL\195\182b as "IH" forall ( id ).
Time wp_loop.
Time wp_bind.
Time iInv "Hinv" as "H".
Time clear \207\131 Heq1 Heq2 Heq3.
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
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
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time iDestruct (gen_heap_bigOp_split with "hSfrag") as "(hSa&hSb)".
Time }
Time iDestruct (gen_heap_bigOpM_dom with "hSa") as "hSa".
Time
iMod (deliver_end_step_inv j K with "Hj Hsource Hstate") as ( (
 mstat, mbox) msg_stat' alloc' vs' lstatus Heq ) "(Hj&Hstate)".
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
Time {
Time solve_ndisj.
Time }
Time (destruct Heq as (He1, (Heq2, (Heq3, Heq4)))).
Time rewrite /MsgsInv.
Time rewrite Hopen.
Time iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time iMod (disk1_next with "[$]") as "(Hd1&Hl1)".
Time (iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "Huid" as ( lk \206\179 ) "(>%&>%&#Hlock&Hinbox)".
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
Time iDestruct "Hinbox" as "(Hmbox&>Hdircontents&Hmsgs)".
Time rewrite big_sepM_sep.
Time iDestruct (TmpInv_path_acc with "[$] [$]") as "(Hghost&Hpath&Htmp)".
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
Time
(destruct
  (decide (("msg" ++ uint64_to_string id)%string \226\136\136 dom (gset string) mbox))
  as [Hin| Hfresh]).
Time -
Time iApply (wp_link_not_new with "[Hpath Hdircontents]").
Time }
Time iSplitL "hS".
Time {
Time iExists _.
Time iFrame.
Time by iPureIntro.
Time }
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time {
Time iFrame.
Time eauto.
Time }
Time iIntros "!> (Hpath&Hdircontents)".
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
Time iDestruct ("Htmp" with "Hpath") as "Htmp".
Time iFrame.
Time iDestruct ("Hm" with "[Hmsgs Hmbox Hdircontents]") as "Hm".
Time {
Time iExists _ , _.
Time (iFrame; eauto).
Time }
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_id ; last  eauto).
Time iExists _.
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time Qed.
Time rewrite Hopen.
Time iExists _.
Time iFrame.
Time iModIntro.
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
Time iIntros ( id' ) "!> _".
Time wp_ret.
Time iNext.
Time iApply ("IH" with "[$] [$] [$] [$] [$] [$]").
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
Time rewrite -fupd_big_sepS.
Time -
Time iClear "IH".
Time iApply (wp_link_new with "[Hpath Hdircontents]").
Time {
Time iFrame.
Time eauto.
Time }
Time iIntros "!> (Hpath&Hpathnew&Hdircontents)".
Time iDestruct ("Htmp" with "Hpath") as "Htmp".
Time iDestruct (big_sepM_insert_2 with "[Hpathnew Hinode] Hmsgs") as "Hmsgs".
Time {
Time (simpl).
Time iExists _ , _.
Time iFrame.
Time replace (0 : Z) with O : Z by auto.
Time iFrame.
Time }
Time
iDestruct
 ("Hm" $! (mstat, <[("msg" ++ uint64_to_string id)%string:=vs]> mbox)
 with "[Hmsgs Hmbox Hdircontents]") as "Hm".
Time {
Time iExists _ , _.
Time iFrame.
Time rewrite dom_insert_L comm_L.
Time iFrame.
Time iFrame "Hlock".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  eauto).
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  eauto).
Time (simpl).
Time (iApply MailboxStatusInterp_insert; eauto).
Time (eapply not_elem_of_dom; eauto).
Time }
Time iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (apply opened_step; auto).
Time econstructor.
Time eexists.
Time split.
Time -
Time rewrite /lookup /readSome.
Time rewrite He1.
Time eauto.
Time -
Time (do 2 eexists; split).
Time {
Time (econstructor; eauto).
Time (eapply not_elem_of_dom; eauto).
Time }
Time (do 2 eexists; split).
Time {
Time rewrite /readUnlockSlice.
Time (do 2 eexists; split).
Time {
Time rewrite /readSome Heq2 //.
Time }
Time (do 2 eexists; split).
Time {
Time rewrite /readSome Heq4 //.
Time }
Time (do 2 eexists; split).
Time {
Time econstructor.
Time }
Time {
Time rewrite /readSome Heq3 //.
Time }
Time }
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time (iDestruct (HeapInv_agree_slice with "[$] [$]") as % (?, ?); eauto).
Time subst.
Time iExists _.
Time iFrame.
Time iSplitL "Hheap Hm Hglobal Hp Hrootdir Hinit".
Time {
Time iExists _.
Time iFrame.
Time (simpl open).
Time rewrite Hopen.
Time iFrame.
Time
iDestruct (big_sepDM_insert_acc (dec:=sigPtr_eq_dec) with "Hheap") as
 "((Hlookup&%)&Hclose)".
Time {
Time eauto.
Time }
Time (iDestruct (InitInv_open_update with "[$]") as "$"; auto).
Time iSplitL "Hrootdir".
Time {
Time iModIntro.
Time rewrite /RootDirInv.
Time (simpl).
Time (rewrite dom_insert_L_in //; eauto).
Time {
Time (eapply elem_of_dom).
Time (eexists; eauto).
Time }
Time }
Time iApply "Hclose".
Time (iSplitR ""; auto).
Time iModIntro.
Time (destruct msg_stat'; inversion Heq4; [  ]).
Time (simpl).
Time iDestruct "Hp" as ( ? ? ) "Hp".
Time iDestruct (Count_Typed_Heap.read_split_join with "[$]") as "H".
Time (destruct num; inv_step; eauto).
Time }
Time wp_ret.
Time wp_ret.
Time iModIntro.
Time iNext.
Time rewrite /delete.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( ? ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
iMod (TmpInv_path_delete with "[$] Htmp") as ( S )
 "(Hpath&Hdir&Hdirlock&Hwand)".
Time iApply (wp_delete with "[$]").
Time iIntros "!> (?&?)".
Time iDestruct ("Hwand" with "[$] [$]") as "Htmp".
Time iExists _.
Time iFrame.
Time iApply "H\206\166".
Time by iFrame.
Time Qed.
Time
Lemma delete_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid msg :
  {{{ j \226\164\135 K (Call (Delete uid msg)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  MailServer.Delete uid msg {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
Time wp_bind.
Time wp_ret.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
Time iDestruct "Hread" as ( lsptr ) "(Hglobal_read&Hlsptr)".
Time
iMod (delete_step_inv with "Hj Hsource Hstate") as ( v body (
 Heq1, Heq2) ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time (iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "Huid" as ( lk \206\179 ) "(>%&>%&#Hlock&>Hinbox)".
Time iDestruct "Hinbox" as "(Hmbox&Hdircontents&Hmsgs)".
Time iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time eexists.
Time split.
Time -
Time rewrite /lookup /readSome.
Time rewrite Heq1.
Time eauto.
Time -
Time (simpl).
Time (do 2 eexists; split).
Time *
Time rewrite Heq2 //=.
Time *
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time
(iDestruct (big_sepM_delete with "Hmsgs") as "(Hcurr_msg&Hmsgs)"; eauto).
Time iDestruct "Hmbox" as "(Hlocked&Hlockinv&Hdirlock)".
Time iDestruct "Hcurr_msg" as ( inode q ) "(Hpath&Hinode)".
Time iApply (wp_delete with "[Hpath Hdircontents Hdirlock]").
Time {
Time iFrame.
Time }
Time iIntros "!> (Hdircontents&Hdirlock)".
Time iExists _.
Time iFrame.
Time iModIntro.
Time iSplitR "H\206\166 Hreg Hj".
Time -
Time iNext.
Time iExists _.
Time iFrame.
Time (simpl open).
Time rewrite Hopen.
Time iFrame.
Time (iDestruct (InitInv_open_update with "[$]") as "$"; auto).
Time iSplitL "Hrootdir".
Time {
Time rewrite /RootDirInv //=.
Time rewrite dom_insert_L_in //.
Time (eapply elem_of_dom).
Time eauto.
Time }
Time iApply "Hm".
Time iExists _ , _.
Time iFrame.
Time (do 2 (iSplitL ""; eauto)).
Time iFrame "Hlock".
Time rewrite dom_delete_L.
Time iFrame.
Time -
Time iApply "H\206\166".
Time iFrame.
Time Qed.
Time
Lemma lock_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid :
  {{{ j \226\164\135 K (Call (Lock uid)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  MailServer.Lock uid {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
Time wp_bind.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
Time iDestruct "Hread" as ( lsptr ) "(Hglobal_read&Hlsptr)".
Time (iApply (wp_getX with "[$]"); iIntros "!> Hglobal_read").
Time
iMod (lock_step_inv with "Hj Hsource Hstate") as ( v Heq ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (MsgsInv_pers_split with "Hm") as
 "#Huid" ; first  eauto).
Time iDestruct "Huid" as ( lk \206\179 H\206\147lookup Hnth ) "#Hlock".
Time iExists _.
Time iFrame.
Time iExists _.
Time rewrite Hopen.
Time iFrame.
Time iModIntro.
Time wp_bind.
Time iApply (wp_sliceRead with "[$]").
Time {
Time eauto.
Time }
Time iIntros "!> Hlsptr".
Time iApply wp_fupd.
Time iApply (wp_lockAcquire_writer with "Hlock").
Time {
Time set_solver +.
Time }
Time iIntros "!> (Hlockinv&Hlocked)".
Time iInv "Hinv" as "H".
Time clear \207\131 Hopen Heq v.
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls' ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time
iMod (lock_step_inv with "Hj Hsource Hstate") as ( v Heq ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time iDestruct (GlobalInv_unify with "[$] [$] [$]") as % <-.
Time (iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "Huid" as ( lk' \206\179' ) "(>Heq1&>Heq2&Hinbox)".
Time iDestruct "Heq1" as % Heq1.
Time iDestruct "Heq2" as % Heq2.
Time iDestruct "Hinbox" as "(_&Hmbox&Hdircontents&Hmsgs)".
Time (assert (lk' = lk) by congruence).
Time subst.
Time (assert (\206\179' = \206\179) by congruence).
Time subst.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hmbox" as "[>Hmbox|Hmbox]" ;
 last  first).
Time {
Time iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
Time iDestruct "Hauth" as ( S ? ) "(Hauth&?)".
Time iExFalso.
Time iDestruct "Hlockinv" as ( S' ? ) "(Hauth'&?)".
Time iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
Time }
Time iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time eexists.
Time split.
Time -
Time rewrite /lookup /readSome.
Time rewrite Heq.
Time eauto.
Time -
Time (simpl).
Time (do 2 eexists; split; constructor).
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time (simpl open).
Time rewrite Hopen.
Time iSplitR "Hj H\206\166 Hreg".
Time {
Time iModIntro.
Time iNext.
Time iExists _.
Time iFrame.
Time iSplitL "Hrootdir".
Time {
Time rewrite /RootDirInv //=.
Time rewrite dom_insert_L_in //.
Time (eapply elem_of_dom).
Time eauto.
Time }
Time iSplitL "Hinit".
Time {
Time (iApply InitInv_open_update; eauto).
Time }
Time iApply "Hm".
Time rewrite /MsgInv.
Time iExists _ , _.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by done).
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by done).
Time rewrite /InboxInv.
Time by iFrame.
Time }
Time iModIntro.
Time iModIntro.
Time iApply "H\206\166".
Time by iFrame.
Time Qed.
Time
Lemma unlock_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid :
  {{{ j \226\164\135 K (Call (Unlock uid)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  MailServer.Unlock uid {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
Time wp_bind.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
Time iDestruct "Hread" as ( lsptr ) "(Hglobal_read&Hlsptr)".
Time (iApply (wp_getX with "[$]"); iIntros "!> Hglobal_read").
Time
iMod (unlock_step_inv with "Hj Hsource Hstate") as ( v Heq ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time (iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "Huid" as ( lk \206\179 ) "(%&%&#Hlock&Hinbox)".
Time iDestruct "Hinbox" as "(Hmbox&Hdircontents&Hmsgs)".
Time iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time eexists.
Time split.
Time -
Time rewrite /lookup /readSome.
Time rewrite Heq.
Time eauto.
Time -
Time (simpl).
Time (do 2 eexists; split; econstructor).
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time iExists _.
Time (simpl open).
Time rewrite Hopen.
Time iFrame.
Time iDestruct "Hmbox" as "(Hwlock&Hlockinv&Hunlocked)".
Time iSplitL "Hm Hmsgs Hdircontents Hunlocked Hrootdir Hinit".
Time {
Time iModIntro.
Time iNext.
Time (iDestruct (InitInv_open_update with "[$]") as "$"; auto).
Time iSplitL "Hrootdir".
Time {
Time rewrite /RootDirInv //=.
Time (rewrite dom_insert_L_in; eauto).
Time (eapply elem_of_dom; eauto).
Time }
Time iApply "Hm".
Time iExists _ , _.
Time (do 2 (iSplitL ""; eauto)).
Time iFrame.
Time iFrame "Hlock".
Time }
Time iModIntro.
Time wp_bind.
Time iApply (wp_sliceRead with "[$]").
Time {
Time eauto.
Time }
Time iIntros "!> Hlsptr".
Time (iApply (wp_lockRelease_writer with "[Hwlock Hlockinv]"); swap 1 2).
Time {
Time (iFrame "Hlock"; iFrame).
Time }
Time {
Time set_solver +.
Time }
Time iIntros "!> _".
Time iApply "H\206\166".
Time iFrame.
Time Qed.
Time
Lemma pickup_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid :
  {{{ j \226\164\135 K (pickup uid) \226\136\151 Registered \226\136\151 ExecInv }}} 
  Pickup uid {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
Time wp_bind.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv' with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
Time iDestruct "Hread" as ( lsptr ) "(Hglobal_read&Hlsptr)".
Time (iApply (wp_getX with "[$]"); iIntros "!> Hglobal_read").
Time iMod (pickup_step_inv with "[$] [$] [$]") as ( (v, Heq) ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (MsgsInv_pers_split with "Hm") as
 "#Huid" ; first  eauto).
Time iDestruct "Huid" as ( lk \206\179 H\206\147lookup Hnth ) "#Hlock".
Time iExists _.
Time iFrame.
Time iExists _.
Time rewrite Hopen.
Time iFrame.
Time iModIntro.
Time wp_bind.
Time iApply (wp_sliceRead with "[$]").
Time {
Time eauto.
Time }
Time iIntros "!> Hlsptr".
Time wp_bind.
Time iApply (wp_lockAcquire_writer with "Hlock").
Time {
Time set_solver +.
Time }
Time iIntros "!> (Hlockinv&Hlocked)".
Time wp_bind.
Time wp_ret.
Time wp_bind.
Time wp_bind.
Time iInv "Hinv" as "H".
Time clear \207\131 Hopen Heq v.
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv' with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls' ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time iMod (pickup_step_inv with "[$] [$] [$]") as ( (v, Heq) ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time iDestruct (GlobalInv_unify with "[$] [$] [$]") as % <-.
Time (iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "Huid" as ( lk' \206\179' ) "(>Heq1&>Heq2&Hinbox)".
Time iDestruct "Heq1" as % Heq1.
Time iDestruct "Heq2" as % Heq2.
Time iDestruct "Hinbox" as "(_&Hmbox&Hdircontents&Hmsgs)".
Time (assert (lk' = lk) by congruence).
Time subst.
Time (assert (\206\179' = \206\179) by congruence).
Time subst.
Time (destruct v as (status, msgs)).
Time (destruct status).
Time {
Time iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
Time iDestruct "Hauth" as ( S ) "(Hauth&%)".
Time iExFalso.
Time iDestruct "Hlockinv" as ( S' ? ) "(Hauth'&?)".
Time iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
Time }
Time {
Time iDestruct "Hmbox" as ">(Hlocked'&Hauth&?)".
Time iDestruct "Hauth" as ( S ? ) "(Hauth&?)".
Time iExFalso.
Time iDestruct "Hlockinv" as ( S' ? ) "(Hauth'&?)".
Time iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hmbox" as "[>Hmbox|Hmbox]" ;
 last  first).
Time {
Time iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
Time iDestruct "Hauth" as ( S ? ) "(Hauth&?)".
Time iExFalso.
Time iDestruct "Hlockinv" as ( S' ? ) "(Hauth'&?)".
Time iApply (@ghost_var_auth_valid contentsC with "Hauth Hauth'").
Time }
Time iApply (wp_list_start with "Hmbox").
Time iIntros "!> Hmbox".
Time iModIntro.
Time iExists _.
Time iFrame.
Time iExists _.
Time iFrame.
Time replace 0%Z with O : Z by auto.
Time iPoseProof (@Count_Heap.read_split_join1 with "Hmbox") as "(Hrl&Hmbox)".
Time rewrite ?Hopen.
Time iFrame.
Time iSplitL "Hm Hmbox Hdircontents Hmsgs Hlockinv".
Time {
Time iNext.
Time iApply "Hm".
Time iExists _ , _.
Time iFrame "%".
Time iFrame "Hlock".
Time iFrame.
Time iRight.
Time iFrame.
Time }
Time iInv "Hinv" as "H".
Time clear \207\131 Hopen Heq Heq1 Heq2 msgs.
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
(iMod (is_opened_step_inv' with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls' ) "(>Hglobal&Hrootdir&Hinit&Hm)".
Time iMod (pickup_step_inv with "[$] [$] [$]") as ( (v, Heq) ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time iDestruct (GlobalInv_unify with "[$] [$] [$]") as % <-.
Time (iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "Huid" as ( lk' \206\179' ) "(>Heq1&>Heq2&Hinbox)".
Time iDestruct "Heq1" as % Heq1.
Time iDestruct "Heq2" as % Heq2.
Time iDestruct "Hinbox" as "(_&Hmbox&>Hdircontents&Hmsgs)".
Time (assert (lk' = lk) by congruence).
Time subst.
Time (assert (\206\179' = \206\179) by congruence).
Time subst.
Time (destruct v as (status, msgs)).
Time (destruct status).
Time {
Time iDestruct "Hmbox" as ">(Hlocked'&Hauth)".
Time iExFalso.
Time iApply (wlocked_wlocked with "Hlocked Hlocked'").
Time }
Time {
Time iDestruct "Hmbox" as ">(Hlocked'&Hauth&?)".
Time iExFalso.
Time iApply (wlocked_wlocked with "Hlocked Hlocked'").
Time }
Time iDestruct "Hmbox" as "[>Hmbox|>Hmbox]".
Time {
Time iExFalso.
Time (iApply (@Count_Heap.mapsto_valid_generic with "Hrl Hmbox"); lia).
Time }
Time iDestruct "Hmbox" as "(Hrl'&Hlockinv)".
Time iPoseProof (@Count_Heap.read_split_join1 with "[Hrl Hrl']") as "Hrl".
Time {
Time iFrame.
Time }
Time iApply (wp_list_finish with "[$]").
Time iIntros ( s lmsg_names ) "!> (Hperm&Hslice_list&Hdircontents&Hdirlock)".
Time iDestruct "Hperm" as % Hperm.
Time rewrite -map_to_list_dom_perm in  {} Hperm *.
Time (intros Hperm).
Time symmetry in Hperm.
Time
(<ssreflect_plugin::ssrtclseq@0>
 edestruct (map_Permutation) as (msgs', (Hperm', Hmsgs'_map)) ; first  by
 eauto).
Time
iMod
 (ghost_step_call _ _ (\206\187 x, K (Bind x (\206\187 x, Call (Pickup_End uid x)))) msgs'
 with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (eapply opened_step; auto).
Time econstructor.
Time eexists.
Time split.
Time -
Time rewrite /lookup /readSome.
Time rewrite Heq.
Time eauto.
Time -
Time (simpl).
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  first).
Time *
Time (econstructor; eauto).
Time by symmetry.
Time *
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time
iMod (InboxLockInv_set_msgs _ _ msgs with "[$]") as
 "(Hcontents_auth&Hcontents_frag)".
Time iModIntro.
Time iExists _.
Time iFrame.
Time iExists _.
Time (simpl open).
Time rewrite Hopen.
Time iFrame.
Time replace 0%Z with O : Z by auto.
Time iSplitL "Hm Hlocked Hcontents_auth Hdircontents Hmsgs Hrootdir Hinit".
Time {
Time iNext.
Time (iDestruct (InitInv_open_update with "[$]") as "$"; auto).
Time iSplitL "Hrootdir".
Time {
Time rewrite /RootDirInv dom_insert_L_in //.
Time {
Time (eapply elem_of_dom; eauto).
Time }
Time }
Time iApply "Hm".
Time iExists _ , _.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by eauto).
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by eauto).
Time iFrame "Hlock".
Time iFrame.
Time (iExists _; iFrame).
Time eauto.
Time }
Time wp_bind.
Time iApply (wp_newAlloc with "[//]").
Time iIntros ( messages0 ) "!> Hmessages0".
Time wp_bind.
Time iApply (wp_newSlice with "[//]").
Time iIntros ( messages' ) "!> Hmessages".
Time wp_bind.
Time iApply (wp_writePtr with "[$]").
Time iIntros "!> Hmessages0".
Time wp_bind.
Time (simpl repeat).
Time iDestruct (slice_mapsto_len with "Hslice_list") as % ->.
Time (remember [] as lmsgs_read eqn:Heq_lmsgs_read ).
Time (assert (length lmsg_names = length msgs')).
Time {
Time by rewrite -Hmsgs'_map map_length.
Time }
Time (assert (Hread_ind : lmsgs_read = createMessages (take O msgs'))).
Time {
Time by eauto.
Time }
Time
(assert (Hk : exists k, 0 + k = length lmsg_names) by
  (exists (length lmsg_names); lia)).
Time revert Hk.
Time (assert (Hlen : length lmsgs_read = 0) by rewrite Heq_lmsgs_read //=).
Time move : {}Hlen {}.
Time (assert (\226\136\131 i, i = 0) as (i, Heq_i) by eauto).
Time rewrite -{+1}Heq_i.
Time rewrite -{+1}Heq_i.
Time rewrite -[a in Loop _ a]Heq_i.
Time rewrite -Heq_i in  {} Hread_ind.
Time
replace (messages'.(slice.length) = 0) with messages'.(slice.length) = i
 by congruence.
Time (<ssreflect_plugin::ssrtclintros@0> clear Heq_i =>Hlen).
Time clear Heq_lmsgs_read.
Time (intros (k, Hk)).
Time iMod (ghost_step_bind_ret with "Hj Hsource") as "Hj".
Time {
Time solve_ndisj.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iInduction k as [
 | k] "IH" forall ( messages' i lmsgs_read Hread_ind Hlen Hk ) ; last  first).
Time -
Time wp_loop.
Time (destruct equal as [Heq_bad| ]).
Time {
Time exfalso.
Time rewrite Heq_bad in  {} Hk.
Time lia.
Time }
Time (assert (i < length lmsg_names)).
Time {
Time lia.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (nth_error lmsg_names i) as [curr_name| ] eqn:Heq_name1 ; last 
 first).
Time {
Time exfalso.
Time (eapply nth_error_Some; eauto).
Time }
Time wp_bind.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_sliceRead with "Hslice_list") ;
 first  eauto).
Time iIntros "!> Hslice_list".
Time wp_bind.
Time rewrite readMessage_unfold_open.
Time wp_bind.
Time clear \207\131 Hopen Heq.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time
iMod (pickup_end_step_inv with "Hj Hsource Hstate") as ( v Heq )
 "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time rewrite /MsgsInv ?Hopen.
Time iDestruct "Hmsgs" as ( ls' ) "(>Hglobal&Hopen&Hinit&Hm)".
Time iDestruct (GlobalInv_unify with "[$] [$] [$]") as % <-.
Time (iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct "Huid" as ( lk' \206\179' ) "(>Heq1&>Heq2&Hinbox)".
Time iDestruct "Heq1" as % Heq1'.
Time iDestruct "Heq2" as % Heq2'.
Time iDestruct "Hinbox" as "(Hlock'&Hmbox&>Hdircontents&>Hmsgs)".
Time (assert (lk' = lk) by congruence).
Time subst.
Time (assert (\206\179' = \206\179) by congruence).
Time subst.
Time iDestruct "Hmbox" as ">(Hwlock&Hlockinv)".
Time iDestruct "Hlockinv" as ( S ) "(Hauth&Hsubset)".
Time iDestruct "Hsubset" as % Hsubset.
Time
iDestruct (ghost_var_agree (A:=contentsC) with "Hauth Hcontents_frag") as % ?.
Time subst.
Time
(assert
  (\226\136\131 body,
     msgs !! curr_name = Some body
     \226\136\167 nth_error msgs' i = Some (curr_name, body))
  as (body, (Hmsgs_curr_name, Hmsgs'_curr_name))).
Time {
Time (apply nth_error_map in Heq_name1 as (mbody, (Heq_body, Hnth_name1))).
Time (apply nth_error_In in Hnth_name1 as Hin).
Time (destruct mbody as (?, body)).
Time (simpl in Heq_body).
Time subst.
Time exists body.
Time (apply elem_of_list_In in Hin).
Time split.
Time *
Time rewrite -Hperm' in  {} Hin *.
Time (apply elem_of_map_to_list).
Time *
Time eauto.
Time }
Time
(iDestruct (big_sepM_lookup_acc with "Hmsgs") as "(Hcurr_msg&Hmsgs)"; eauto).
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> eapply lookup_weaken ; last  eassumption).
Time eauto.
Time }
Time iDestruct "Hcurr_msg" as ( inode q ) "(Hpath&Hinode)".
Time iApply (wp_open with "[$]").
Time iIntros ( fh ) "!> (Hpath&Hfh)".
Time
iPoseProof (@Count_GHeap.read_split_join with "Hinode") as
 "(Hinode_inv&Hinode)".
Time iExists _.
Time iFrame.
Time rewrite ?Hopen.
Time iFrame.
Time iSplitL "Hm Hinode_inv Hmsgs Hglobal Hauth Hwlock Hdircontents Hpath".
Time {
Time iModIntro.
Time iNext.
Time iExists _.
Time iFrame.
Time iApply "Hm".
Time iExists _ , _.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by eauto).
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by eauto).
Time iFrame "Hlock".
Time iExists _.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by eauto).
Time iApply "Hmsgs".
Time iExists _ , (S q).
Time iFrame.
Time }
Time iModIntro.
Time iApply (wp_readMessage_handle with "[$]").
Time iIntros "!> Hinode".
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time iIntros "!> Hmessages0".
Time wp_bind.
Time iApply (wp_sliceAppend with "Hmessages").
Time rename messages' into messages_old.
Time iIntros ( messages' ) "!> Hmessages".
Time wp_bind.
Time iApply (wp_writePtr with "Hmessages0").
Time iIntros "!> Hmessages0".
Time wp_ret.
Time iNext.
Time iApply ("IH" with "[] [] [] [$] H\206\166 [$] [$] [$] [$] [$] [$] [$] [$]").
Time *
Time iPureIntro.
Time rewrite -(map_app _ _ [(curr_name, body)]).
Time f_equal.
Time (erewrite take_snoc_S; eauto).
Time *
Time iPureIntro.
Time rewrite app_length Hlen //=.
Time *
Time iPureIntro.
Time lia.
Time -
Time wp_loop.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite right_id in  {} Hk *
 =>Hlen_names).
Time rewrite Hlen_names.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct equal as [_| ] ; last  by
 congruence).
Time (assert (i = length msgs')).
Time {
Time congruence.
Time }
Time (assert (lmsgs_read = createMessages msgs')).
Time {
Time subst.
Time rewrite map_length.
Time by rewrite firstn_all.
Time }
Time subst.
Time rewrite map_length.
Time rewrite firstn_all.
Time wp_ret.
Time iNext.
Time iInv "Hinv" as "H".
Time clear \207\131 Hopen Heq.
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iDestruct (slice_mapsto_non_null with "[Hmessages]") as % ?.
Time {
Time (iExists _; eauto).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (HeapInv_non_alloc_inv _ _ 0 with "[$] [Hmessages]") as % ? ; first  auto).
Time {
Time (iDestruct "Hmessages" as "(?&?)"; iFrame).
Time }
Time
iMod (pickup_end_step_inv with "Hj Hsource Hstate") as ( v Heq )
 "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)";
  auto).
Time {
Time (simpl; auto).
Time }
Time {
Time solve_ndisj.
Time }
Time iDestruct "Hmessages" as ( malloc Hmalloc ) "Hmessages".
Time
iMod (ghost_step_call _ _ _ messages' with "Hj Hsource Hstate") as
 "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (apply opened_step; auto).
Time econstructor.
Time (do 2 eexists).
Time {
Time rewrite /lookup /readSome.
Time rewrite Heq.
Time eauto.
Time }
Time reduce.
Time (do 2 eexists).
Time split.
Time {
Time (simpl).
Time econstructor.
Time }
Time (do 2 eexists).
Time split.
Time {
Time (simpl).
Time econstructor.
Time }
Time (do 2 eexists).
Time split.
Time {
Time econstructor.
Time eauto.
Time }
Time eexists (_, _),_.
Time split.
Time {
Time econstructor.
Time (split; eauto).
Time }
Time (do 2 eexists).
Time split.
Time {
Time econstructor.
Time }
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time wp_ret.
Time iExists _.
Time iFrame.
Time (simpl open).
Time rewrite Hopen.
Time iSplitR "Hj Hmessages0 H\206\166 Hreg".
Time {
Time iModIntro.
Time iNext.
Time iSplitL "Hmsgs Hcontents_frag Hdirlock".
Time {
Time (simpl).
Time rewrite /MsgsInv.
Time iDestruct "Hmsgs" as ( l0 ) "(?&Hrootdir&Hinit&Hmap)".
Time iExists _.
Time iFrame.
Time (simpl).
Time (iDestruct (InitInv_open_update with "[$]") as "$"; auto).
Time iSplitL "Hrootdir".
Time {
Time rewrite /RootDirInv //= dom_insert_L_in //.
Time (eapply elem_of_dom; eauto).
Time }
Time (iApply (big_sepM_insert_override_2 with "Hmap"); eauto).
Time rewrite /MsgInv.
Time (simpl).
Time iIntros "H".
Time iDestruct "H" as ( lk' \206\179' ) "(%&%&(?&Hinterp&?&?))".
Time iExists _ , _.
Time iFrame.
Time iDestruct "Hinterp" as "(?&Hinterp)".
Time iFrame.
Time iDestruct "Hinterp" as ( S ) "(Hauth&_)".
Time iFrame "%".
Time iExists _ , _.
Time iFrame.
Time (assert (\206\179' = \206\179) as -> by congruence).
Time iFrame.
Time }
Time (unfold HeapInv).
Time (simpl).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite big_sepDM_updDyn ; last  first).
Time {
Time intuition.
Time }
Time (iFrame; eauto).
Time }
Time iModIntro.
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time iIntros "!> Hptr".
Time wp_ret.
Time iApply "H\206\166".
Time iFrame.
Time Time Qed.
Time End refinement_triples.
