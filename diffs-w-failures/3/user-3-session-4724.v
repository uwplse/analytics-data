Time From iris.algebra Require Import auth gmap list.
Time From iris.algebra Require Import auth gmap frac agree csum excl.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.ThreadReg
  CSL.Leased_Heap.
Time Require Export CSL.Refinement.
Time Require Import StatDb.Impl ExMach.WeakestPre ExMach.RefinementAdequacy.
Time From iris.algebra Require Export functions csum.
Time From iris.base_logic.lib Require Export invariants gen_heap.
Time From iris.proofmode Require Export tactics.
Time Require Export TwoDiskAPI.
Time Set Default Proof Using "Type".
Time Import TwoDisk.
Time Canonical Structure diskIdC := leibnizO diskId.
Time
Class disk_statusG (\206\163 : gFunctors) : Set :=
 Disk_statusG {disk_status_inG :>
                inG \206\163 (csumR (exclR unitO) (agreeR diskIdC));
               disk_status_name : gname}.
Time Arguments disk_status_name {_}.
Time Section disk_status.
Time Context `{tr : disk_statusG \206\163}.
Time
Definition is_OnlyDisk (id : diskId) :=
  own (disk_status_name tr) (Cinr (to_agree id)).
Time
Definition to_status (ds : DisksState) :=
  match ds with
  | OnlyDisk id _ => Cinr (to_agree id)
  | BothDisks _ _ => Cinl (Excl tt)
  end.
Time
Definition disk_status_ctx ds := own (disk_status_name tr) (to_status ds).
Time
Lemma disk_status_agree id ds :
  disk_status_ctx ds -\226\136\151 is_OnlyDisk id -\226\136\151 \226\136\131 d, \226\140\156ds = OnlyDisk id d\226\140\157.
Time Proof.
Time iIntros "H1 H2".
Time iDestruct (own_valid_2 with "H1 H2") as % H.
Time (destruct ds; eauto).
Time Unset Implicit Arguments.
Time Definition recv : proc ExMach.Op _ := Ret tt.
Time Set Default Proof Using "Type".
Time Section refinement_triples.
Time
Context `{!exmachG \206\163} `{lockG \206\163} `{!@cfgG DB.Op DB.l \206\163}
 `{!inG \206\163 (authR (optionUR (exclR (listO natO))))}.
Time Import ExMach.
Time
Definition DBInnerInv \206\179 :=
  (\226\136\131 l : list nat, own \206\179 (\226\151\143 Excl' l) \226\136\151 source_state l)%I.
Time
Definition DBLockInv \206\179 :=
  (\226\136\131 l : list nat,
     own \206\179 (\226\151\175 Excl' l)
     \226\136\151 sum_addr m\226\134\166 fold_right plus O l \226\136\151 count_addr m\226\134\166 length l)%I.
Time
Definition DBCrashInner :=
  (\226\136\131 l, source_state l \226\136\151 lock_addr m\226\134\166 O \226\136\151 sum_addr m\226\134\166 O \226\136\151 count_addr m\226\134\166 O)%I.
Time Definition lN : namespace := nroot.@"lock".
Time Definition iN : namespace := nroot.@"inner".
Time
Definition DBInv :=
  (source_ctx
   \226\136\151 (\226\136\131 \206\1791 \206\1792,
        is_lock lN \206\1791 lock_addr (DBLockInv \206\1792) \226\136\151 inv iN (DBInnerInv \206\1792)))%I.
Time Definition CrashInv := (source_ctx \226\136\151 inv iN DBCrashInner)%I.
Time
Lemma init_ghost_list :
  (|==> \226\136\131 \206\179, own \206\179 (\226\151\143 Excl' (nil : list nat) \226\139\133 \226\151\175 Excl' nil) : iProp \206\163)%I.
Time Proof.
Time (iMod (@own_alloc _ _ _ (\226\151\143 Excl' nil \226\139\133 \226\151\175 Excl' nil)); eauto).
Time rewrite -Cinr_op in  {} H.
Time (apply agree_op_inv' in H).
Time (inversion H; subst).
Time eauto.
Time Qed.
Time {
Time (apply auth_both_valid; done).
Time
Lemma disk_status_update_both disk0 disk1 ds :
  disk_status_ctx (BothDisks disk0 disk1) ==\226\136\151 disk_status_ctx ds.
Time Proof.
Time iIntros "Hown".
Time (iMod (own_update with "Hown") as "$"; eauto).
Time }
Time Qed.
Time
Lemma add_refinement {T} j K `{LanguageCtx DB.Op unit T DB.l K} 
  n :
  {{{ j \226\164\135 K (Call (DB.Add n)) \226\136\151 Registered \226\136\151 DBInv }}} 
  add n {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&#Hsource_inv&Hinv) H\206\166".
Time {
Time (simpl).
Time apply : {}cmra_update_exclusive {}.
Time (destruct ds; econstructor).
Time }
Time Qed.
Time
Lemma disk_status_update_only id d d' :
  disk_status_ctx (OnlyDisk id d) ==\226\136\151 disk_status_ctx (OnlyDisk id d').
Time Proof.
Time iIntros "Hown".
Time trivial.
Time Qed.
Time End disk_status.
Time
Class exmachG \206\163 :=
 ExMachG {exm_invG : invG \206\163;
          exm_mem_inG :> gen_heapG nat nat \206\163;
          exm_disk0_inG :> leased_heapG nat nat \206\163;
          exm_disk1_inG :> leased_heapG nat nat \206\163;
          exm_status_inG :> disk_statusG \206\163;
          exm_treg_inG :> tregG \206\163}.
Time
Lemma gen_heap_strong_init `{H : gen_heapPreG L V \206\163} 
  \207\131s :
  (|==> \226\136\131 (H0 : gen_heapG L V \206\163) (Hpf : @gen_heap_inG _ _ _ _ _ H0 =
                                        gen_heap_preG_inG),
          gen_heap_ctx \207\131s \226\136\151 own (gen_heap_name H0) (\226\151\175 to_gen_heap \207\131s))%I.
Time iDestruct "Hinv" as ( \206\1791 \206\1792 ) "(#Hlockinv&#Hinv)".
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131s \226\139\133 \226\151\175 to_gen_heap \207\131s)) as ( \206\179 ) "(?&?)".
Time {
Time (apply auth_both_valid; split; auto).
Time (wp_lock "(Hlocked&HDB)").
Time exact : {}to_gen_heap_valid {}.
Time }
Time iMod (own_alloc (\226\151\143 to_gen_meta \226\136\133)) as ( \206\179m ) "Hm".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_meta_valid {}.
Time }
Time iModIntro.
Time iExists (GenHeapG L V \206\163 _ _ _ _ _ \206\179 \206\179m) , eq_refl.
Time iFrame.
Time iDestruct "HDB" as ( l ) "(Hsource_tok&Hsum&Hcount)".
Time (do 3 wp_step).
Time iExists _.
Time iFrame.
Time eauto.
Time Qed.
Time
Definition disk_state_interp {\206\163} (hM : gen_heapG addr nat \206\163)
  (hD0 hD1 : leased_heapG addr nat \206\163) (hStatus : disk_statusG \206\163) :=
  (\206\187 s,
     \226\136\131 mem disk0 disk1,
       gen_heap_ctx mem (hG:=hM)
       \226\136\151 gen_heap_ctx disk0 (hG:=leased_heap_heapG hD0)
         \226\136\151 gen_heap_ctx disk1 (hG:=leased_heap_heapG hD1)
           \226\136\151 disk_status_ctx (disks_state s)
             \226\136\151 \226\140\156mem = mem_state s
                \226\136\167 match disks_state s with
                  | BothDisks disk0' disk1' =>
                      disk0 = disk0' \226\136\167 disk1 = disk1'
                  | OnlyDisk d0 disk0' => disk0 = disk0'
                  | OnlyDisk d1 disk1' => disk1 = disk1'
                  end \226\136\167 state_wf s\226\140\157)%I.
Time
Definition ex_mach_interp {\206\163} {hM : gen_heapG addr nat \206\163}
  {hD0 hD1 : leased_heapG addr nat \206\163} hS {tr : tregG \206\163} :=
  (\206\187 s, thread_count_interp (fst s) \226\136\151 disk_state_interp hM hD0 hD1 hS (snd s))%I.
Time
Definition ex_mach_interp' `{exmachG \206\163} :=
  @ex_mach_interp _ exm_mem_inG exm_disk0_inG exm_disk1_inG exm_status_inG
    exm_treg_inG.
Time
Instance exmachG_irisG  `{exmachG \206\163}: (irisG TwoDisk.Op TwoDisk.l \206\163) := {
 iris_invG :=exm_invG; state_interp :=ex_mach_interp'}.
Time
Definition mem_mapsto_vs k v k' :=
  match Nat.compare k' k with
  | Lt => None
  | Eq => Some v
  | Gt => Some 0
  end.
Time #[global]
Notation "l m\226\134\166{ q } v " := (mapsto (hG:=exm_mem_inG) l q v)
  (at level 20, q  at level 50, format "l  m\226\134\166{ q } v") : bi_scope.
Time #[global]
Notation "l m\226\134\166 v " := (mapsto (hG:=exm_mem_inG) l 1 v) 
  (at level 20) : bi_scope.
Time #[global]
Notation "l d0\226\151\175\226\134\166 v " := (mapsto (hG:=leased_heap_heapG exm_disk0_inG) l 1 v)
  (at level 20) : bi_scope.
Time #[global]
Notation "l d0\226\134\166 v " :=
  (mapsto (hG:=leased_heap_heapG exm_disk0_inG) l 1 v
   \226\136\151 master (hG:=exm_disk0_inG) l v)%I (at level 20) : bi_scope.
Time #[global]
Notation "l d1\226\151\175\226\134\166 v " := (mapsto (hG:=leased_heap_heapG exm_disk1_inG) l 1 v)
  (at level 20) : bi_scope.
Time #[global]
Notation "l d1\226\134\166 v " :=
  (mapsto (hG:=leased_heap_heapG exm_disk1_inG) l 1 v
   \226\136\151 master (hG:=exm_disk1_inG) l v)%I (at level 20) : bi_scope.
Time Definition lease0 `{exmachG \206\163} := lease (hG:=exm_disk0_inG).
Time Definition lease1 `{exmachG \206\163} := lease (hG:=exm_disk1_inG).
Time Section lifting.
Time Context `{exmachG \206\163}.
Time Lemma nat_compare_lt_Lt : \226\136\128 n m : nat, n < m \226\134\146 (n ?= m) = Lt.
Time Proof.
Time (intros).
Time by apply nat_compare_lt.
Time Qed.
Time Lemma nat_compare_gt_Gt : \226\136\128 n m : nat, n > m \226\134\146 (n ?= m) = Gt.
Time Proof.
Time (intros).
Time by apply nat_compare_gt.
Time Qed.
Time
Lemma mem_init_to_bigOp mem :
  own (i:=@gen_heap_inG _ _ _ _ _ exm_mem_inG) (gen_heap_name exm_mem_inG)
    (\226\151\175 to_gen_heap mem) -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 mem, i m\226\134\166 v.
Time Proof.
Time (induction mem using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time
iAssert
 (own (i:=@gen_heap_inG _ _ _ _ _ exm_mem_inG) (gen_heap_name exm_mem_inG)
    (\226\151\175 to_gen_heap m) \226\136\151 i m\226\134\166 x)%I with "[Hown]" as "[Hrest $]".
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite to_gen_heap_insert
 insert_singleton_op ; last  by apply lookup_to_gen_heap_None).
Time rewrite auth_frag_op.
Time iDestruct "Hown" as "(?&?)".
Time iFrame.
Time }
Time by iApply IHmem.
Time Qed.
Time wp_bind.
Time Import Reg_wp.
Time
Lemma thread_reg1 :
  \226\136\128 n \207\131,
    state_interp (n, \207\131)
    -\226\136\151 thread_count_interp n
       \226\136\151 disk_state_interp exm_mem_inG exm_disk0_inG exm_disk1_inG
           exm_status_inG \207\131.
Time Proof.
Time eauto.
Time Qed.
Time
Lemma thread_reg2 :
  \226\136\128 n \207\131,
    thread_count_interp n
    \226\136\151 disk_state_interp exm_mem_inG exm_disk0_inG exm_disk1_inG
        exm_status_inG \207\131 -\226\136\151 state_interp (n, \207\131).
Time Proof.
Time auto.
Time iInv "Hinv" as ( l' ) ">(Htok&Hsource)".
Time Qed.
Time
Lemma wp_spawn {T} s E (e : proc _ T) \206\166 :
  \226\150\183 Registered
  -\226\136\151 \226\150\183 (Registered -\226\136\151 WP (let! _ <- e; Unregister)%proc @ s; \226\138\164 {{ _, True }})
     -\226\136\151 \226\150\183 (Registered -\226\136\151 \206\166 tt) -\226\136\151 WP Spawn e @ s; E {{ \206\166 }}.
Time Proof.
Time (eapply wp_spawn; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_unregister s E :
  {{{ \226\150\183 Registered }}} Unregister @ s; E {{{ RET tt; True}}}.
Time Proof.
Time (eapply wp_unregister; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_wait s E : {{{ \226\150\183 Registered }}} Wait @ s; E {{{ RET tt; AllDone}}}.
Time Proof.
Time (eapply wp_wait; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_write_mem s E i v' v :
  {{{ \226\150\183 i m\226\134\166 v' }}} write_mem i v @ s; E {{{ RET tt; 
  i m\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  by destruct s).
Time
iDestruct (own_valid_2 with "Htok Hsource_tok") as %
 [<-%leibniz_equiv%Excl_included _]%auth_both_valid.
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time
iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
Time (inversion Hstep; subst).
Time (inversion H0).
Time subst.
Time (inversion Hstep; subst).
Time iDestruct "Hown" as "(?&Hown)".
Time rewrite /disk_state_interp.
Time iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown1&Hownd0&Hownd1&?&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time {
Time (intros).
Time eexists.
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  by eauto).
Time iMod (@gen_heap_update with "Hown1 Hi") as "[Hown1 Hi]".
Time (econstructor; eauto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time
iMod
 (own_update_2 _ _ _ (\226\151\143 Excl' (n :: l) \226\139\133 \226\151\175 Excl' (n :: l))
 with "Htok Hsource_tok") as "[Hfull ?]".
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time {
Time by apply auth_update, option_local_update, exclusive_local_update.
Time }
Time wp_step.
Time iModIntro.
Time iSplitL "Hfull Hsource".
Time {
Time iNext.
Time iExists _.
Time iFrame.
Time }
Time iAssert (DBLockInv \206\1792) with "[-H\206\166 Hreg Hlocked Hj]" as "HDB".
Time {
Time (iExists _; simpl).
Time (do 2 iFrame).
Time }
Time (wp_unlock "[-H\206\166 Hreg Hj]"; eauto).
Time (iApply ("H\206\166" with ""); iFrame).
Time Qed.
Time
Lemma avg_refinement {T} j K `{LanguageCtx DB.Op nat T DB.l K} :
  {{{ j \226\164\135 K (Call DB.Avg) \226\136\151 DBInv }}} avg {{{ n,  RET n; 
  j \226\164\135 K (Ret n)}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&#Hsource_inv&Hinv) H\206\166".
Time iDestruct "Hinv" as ( \206\1791 \206\1792 ) "(#Hlockinv&#Hinv)".
Time (wp_lock "(Hlocked&HDB)").
Time iDestruct "HDB" as ( l ) "(Hsource_tok&Hsum&Hcount)".
Time wp_step.
Time wp_bind.
Time iInv "Hinv" as ( l' ) ">(Htok&Hsource)".
Time
iDestruct (own_valid_2 with "Htok Hsource_tok") as %
 [<-%leibniz_equiv%Excl_included _]%auth_both_valid.
Time
iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
Time iExists _ , disk0 , disk1.
Time {
Time (intros).
Time eexists.
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  by eauto).
Time (econstructor; eauto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time wp_step.
Time iFrame.
Time iPureIntro.
Time split_and !.
Time *
Time rewrite /upd_mem /upd_default -Heq_mem Hin_bound //.
Time *
Time (simpl in *).
Time (destruct \207\131.(disks_state); eauto).
Time *
Time (split; intuition; eauto).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /upd_mem /upd_default //= =>i').
Time specialize (Hsize i').
Time (destruct (mem_state \207\131 !! i) eqn:Heq; rewrite Heq).
Time **
Time (case (decide (i = i'))).
Time ***
Time (intros ->).
Time (simpl in *).
Time rewrite -Hsize lookup_insert.
Time (split; eauto).
Time ***
Time (intros ?).
Time rewrite lookup_insert_ne //=.
Time **
Time (apply Hsize).
Time -
Time iApply "H\206\166".
Time eauto.
Time Qed.
Time iModIntro.
Time iSplitL "Htok Hsource".
Time {
Time iNext.
Time iExists _.
Time iFrame.
Time }
Time iAssert (DBLockInv \206\1792) with "[-H\206\166 Hlocked Hj]" as "HDB".
Time {
Time (iExists _; iFrame).
Time }
Time (wp_unlock "[-H\206\166 Hj]"; eauto).
Time
Lemma wp_read_mem s E i v :
  {{{ \226\150\183 i m\226\134\166 v }}} read_mem i @ s; E {{{ RET v; i m\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  by destruct s).
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time wp_ret.
Time by iApply "H\206\166".
Time Qed.
Time (inversion Hstep; subst).
Time (inversion H0).
Time subst.
Time (inversion Hstep; subst).
Time (inversion Hstep; subst).
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown1&Hown2&?&?&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time
Lemma init_mem_split :
  (([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i m\226\134\166 v)
   -\226\136\151 lock_addr m\226\134\166 0 \226\136\151 sum_addr m\226\134\166 0 \226\136\151 count_addr m\226\134\166 0)%I.
Time Proof.
Time iIntros "Hmem".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (big_opM_delete _ _ 0 0) ; last 
 first).
Time {
Time rewrite /ExMach.mem_state.
Time (apply init_zero_lookup_lt_zero).
Time rewrite /size.
Time lia.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (big_opM_delete _ _ 1 0) ; last 
 first).
Time {
Time rewrite /ExMach.mem_state.
Time (<ssreflect_plugin::ssrtclseq@0> rewrite lookup_delete_ne ; last  auto).
Time (apply init_zero_lookup_lt_zero).
Time rewrite /size.
Time lia.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (big_opM_delete _ _ 2 0) ; last 
 first).
Time iExists _ , disk0 , disk1.
Time (iFrame; iPureIntro; split_and !; eauto).
Time {
Time rewrite /ExMach.mem_state.
Time (<ssreflect_plugin::ssrtclseq@0> rewrite lookup_delete_ne ; last  auto).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite lookup_delete_ne ; last  auto).
Time (apply init_zero_lookup_lt_zero).
Time rewrite /size.
Time lia.
Time }
Time iDestruct "Hmem" as "(?&?&?&_)".
Time iFrame.
Time Qed.
Time End refinement_triples.
Time rewrite /state_wf.
Time (split_and; intuition; eauto).
Time -
Time rewrite /lookup_mem /lookup_default -Heq_mem Hin_bound.
Time by iApply "H\206\166".
Time Qed.
Time Lemma cas_non_stuck i v1 v2 \207\131 : \194\172 TwoDisk.l.(step) (CAS i v1 v2) \207\131 Err.
Time Proof.
Time (intros Hstuck).
Time (destruct Hstuck as [Hread| (v', (?, (Hread, Hrest)))]).
Time -
Time (inversion Hread).
Time -
Time
(destruct nat_eq_dec; subst; [ apply bind_pure_no_err in Hrest |  ];
  inversion Hrest).
Time Qed.
Time
Lemma wp_cas_fail s E i v1 v2 v3 :
  v1 \226\137\160 v2 \226\134\146 {{{ \226\150\183 i m\226\134\166 v1 }}} cas i v2 v3 @ s; E {{{ RET v1; i m\226\134\166 v1}}}.
Time Proof.
Time iIntros ( Hneq \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (eapply snd_lift_non_err, cas_non_stuck).
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown1&Hown2&?&?&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time (assert (Hlookup : \207\131.(mem_state) !! i = Some v1)).
Time {
Time rewrite -Heq_mem.
Time (apply Hin_bound).
Time }
Time (inversion Hstep; subst).
Time (inversion H2 as (v', (\207\1312', (Hread, Hrest))); subst).
Time rewrite /lookup_mem /lookup_default /reads Hlookup in  {} Hread.
Time (inversion Hread; subst).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct nat_eq_dec ; first  by exfalso).
Time (inversion Hrest; subst).
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time Module sRT<: exmach_refinement_type.
Time Definition OpT := DB.Op.
Time Definition \206\155a := DB.l.
Time
Definition helper\206\163 : gFunctors :=
  #[ GFunctor (authR (optionUR (exclR (listO natO))))].
Time
Instance subG_helper\206\163 :
 (subG helper\206\163 \206\163 \226\134\146 inG \206\163 (authR (optionUR (exclR (listO natO))))).
Time Proof.
Time solve_inG.
Time Qed.
Time
Definition \206\163 : gFunctors :=
  #[ Adequacy.exmach\206\163; @cfg\206\163 DB.Op DB.l; lock\206\163; helper\206\163].
Time Definition impl := StatDb.Impl.impl.
Time Existing Instance subG_cfgPreG.
Time Instance CFG : (@cfgPreG DB.Op DB.l \206\163).
Time (apply _).
Time Qed.
Time Instance HEX : (ExMach.Adequacy.exmachPreG \206\163).
Time (apply _).
Time Qed.
Time Instance INV : (Adequacy.invPreG \206\163).
Time (apply _).
Time Qed.
Time
Instance REG : (inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))).
Time (apply _).
Time Qed.
Time Definition crash_inner := fun H1 H2 => (@DBCrashInner \206\163 H2 H1)%I.
Time
Definition exec_inner :=
  fun (H1 : @cfgG OpT \206\155a \206\163) H2 =>
  (\226\136\131 v,
     lock_addr m\226\134\166 v
     \226\136\151 (\226\136\131 \206\179, (\226\140\156v = 0\226\140\157 -\226\136\151 @DBLockInv \206\163 H2 _ \206\179) \226\136\151 @DBInnerInv _ _ _ \206\179))%I.
Time
Definition crash_param := fun (_ : @cfgG OpT \206\155a \206\163) (_ : exmachG \206\163) => unit.
Time
Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv \206\163 H2 H1.
Time
Definition crash_starter :=
  fun H1 H2 (_ : crash_param H1 H2) => True%I : iProp \206\163.
Time Definition exec_inv := fun H1 H2 => (@DBInv \206\163 H2 _ H1 _)%I.
Time Definition E := nclose sourceN.
Time Definition init_absr \207\1311a \207\1311c := ExMach.l.(initP) \207\1311c \226\136\167 DB.l.(initP) \207\1311a.
Time Definition recv : proc ExMach.Op unit := Ret tt.
Time End sRT.
Time Module sRD:=  exmach_refinement_definitions sRT.
Time Module sRO: exmach_refinement_obligations sRT.
Time Module eRD:=  exmach_refinement_definitions sRT.
Time Import sRT.
Time Import sRD.
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
Time Lemma recsingle : recover impl = rec_singleton recv.
Time Proof.
Time trivial.
Time Qed.
Time Lemma refinement_op_triples : refinement_op_triples_type.
Time Proof.
Time rewrite /refinement_op_triples_type.
Time (intros).
Time iIntros "(?&?&HDB)".
Time (destruct op).
Time -
Time iApply (add_refinement with "[$]").
Time iNext.
Time iIntros ( ? ) "H".
Time iFrame.
Time -
Time iApply (avg_refinement with "[$]").
Time iNext.
Time iIntros ( ? ) "H".
Time iFrame.
Time Qed.
Time Lemma exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx.
Time Proof.
Time (iIntros ( ? ? ) "(?&?)"; eauto).
Time iExists _ , disk0 , disk1.
Time (iFrame; iPureIntro; split_and !; eauto).
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time rewrite /recv_triple_type.
Time (intros).
Time iIntros "((#Hctx&#Hinv)&_&_)".
Time wp_ret.
Time iInv "Hinv" as ( l ) ">(?&?&?&?)" "_".
Time rewrite /source_inv.
Time (split_and !; intuition eauto).
Time -
Time by iApply "H\206\166".
Time Qed.
Time iMod init_ghost_list as ( \206\1792 ) "[Hauth Hfrag]".
Time iApply (fupd_mask_weaken _ _).
Time {
Time solve_ndisj.
Time }
Time iExists l , nil.
Time iFrame.
Time
Lemma wp_cas_suc s E i v1 v2 :
  {{{ \226\150\183 i m\226\134\166 v1 }}} cas i v1 v2 @ s; E {{{ RET v1; 
  i m\226\134\166 v2}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto using snd_lift_non_err, cas_non_stuck).
Time }
Time iIntros ( v2' (n2, \207\1312) Hstep ) "!>".
Time iDestruct "Hown" as "(?&Hown)".
Time iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown1&Hown2&?&?&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (?, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time (assert (Hlookup : \207\131.(mem_state) !! i = Some v1)).
Time {
Time rewrite -Heq_mem.
Time (apply Hin_bound).
Time }
Time (inversion Hstep; subst).
Time (inversion H2 as (v', (\207\1312', (Hread, Hrest))); subst).
Time (inversion Hread; subst).
Time
rewrite /lookup_mem /lookup_default /reads Hlookup in  {} Hread  {} Hrest.
Time (<ssreflect_plugin::ssrtclseq@0> destruct nat_eq_dec ; last  by eauto).
Time iSplitL "".
Time {
Time (iPureIntro; econstructor).
Time }
Time iClear "Hctx Hinv".
Time iIntros ( ? ? ? ) "(#Hctx&Hstate)".
Time (destruct Hrest as ([], (?, (Hputs, Hpure)))).
Time rewrite /DBLockInv.
Time iModIntro.
Time iExists _.
Time iFrame.
Time (inversion Hpure; subst).
Time (inversion Hputs; inversion Hpure; subst).
Time iMod (@gen_heap_update with "Hown1 Hi") as "(Hown1&Hi)".
Time iModIntro.
Time iSplitR "Hi H\206\166".
Time -
Time iFrame.
Time iExists \206\1792.
Time (iSplitR "Hauth Hstate"; iIntros; iExists nil; iFrame).
Time Qed.
Time Lemma init_wf : \226\136\128 \207\1311a \207\1311c, init_absr \207\1311a \207\1311c \226\134\146 ExMach.state_wf \207\1311c.
Time Proof.
Time (intros ? ? (H, ?)).
Time (inversion H).
Time subst.
Time (eapply ExMach.init_state_wf).
Time Qed.
Time Lemma init_exec_inner : init_exec_inner_type.
Time Proof.
Time rewrite /init_exec_inner_type.
Time (intros ? ? (H, Hinit) ? ?).
Time (inversion H).
Time (inversion Hinit).
Time subst.
Time iIntros "(Hmem&?&#?&Hstate)".
Time iMod init_ghost_list as ( \206\1792 ) "[Hauth Hfrag]".
Time iPoseProof (init_mem_split with "Hmem") as "(?&?&?)".
Time iModIntro.
Time iExists _.
Time iFrame.
Time iExists \206\1792.
Time (iSplitR "Hauth Hstate"; iIntros; iExists nil; iFrame).
Time Qed.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time rewrite /exec_inv_preserve_crash_type.
Time (intros).
Time iIntros "(#Hctx&#Hinv)".
Time iDestruct "Hinv" as ( \206\1791 \206\1792 ) "(Hlock&#Hinv)".
Time rewrite /DBCrashInner.
Time iInv "Hinv" as ">Hopen" "_".
Time iDestruct "Hopen" as ( l ) "(?&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iModIntro.
Time (iExists l; iFrame).
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
Time iFrame.
Time Qed.
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time Proof.
Time rewrite /crash_inv_preserve_crash_type.
Time (intros).
Time iIntros "(#Hctx&#Hinv)".
Time rewrite /DBCrashInner.
Time iInv "Hinv" as ">Hopen" "_".
Time iExists _ , disk0 , disk1.
Time iFrame.
Time iDestruct "Hopen" as ( l ) "(?&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iPureIntro.
Time split_and !.
Time *
Time rewrite /upd_mem /upd_default //= Hin_bound //.
Time *
Time done.
Time *
Time (split; intuition; eauto).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /upd_mem /upd_default //= =>i').
Time specialize (Hsize i').
Time (destruct (mem_state \207\1312' !! i) eqn:Heq; rewrite Heq).
Time iIntros ( ? ? ) "Hmem".
Time **
Time (case (decide (i = i'))).
Time ***
Time (intros ->).
Time iModIntro.
Time (simpl in *).
Time rewrite -Hsize lookup_insert.
Time iExists l.
Time iFrame.
Time (split; eauto).
Time ***
Time (intros ?).
Time rewrite lookup_insert_ne //=.
Time **
Time (apply Hsize).
Time -
Time iApply "H\206\166".
Time eauto.
Time Qed.
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
Time iFrame.
Time Qed.
Time
Lemma wf_range_pres_update (m : gmap addr nat) i v :
  wf_range m \226\134\146 wf_range (upd_default i v m).
Time Proof.
Time (intros Hwf i').
Time rewrite -Hwf.
Time rewrite /upd_default.
Time (destruct (decide (i = i'))).
Time -
Time subst.
Time (destruct (m !! i') as [?| ] eqn:Heq; rewrite Heq).
Time *
Time rewrite lookup_insert //=.
Time (split; eauto).
Time *
Time rewrite -Heq.
Time eauto.
Time -
Time (destruct (m !! i) as [?| ] eqn:Heq; rewrite ?Heq).
Time *
Time rewrite lookup_insert_ne //=.
Time *
Time eauto.
Time Qed.
Time Hint Resolve wf_range_pres_update: twodb.
Time
Lemma wf_disk0_update id0 i v x :
  wf_disk (disk0 x) \226\134\146 wf_disk (disk0 (upd_disk id0 i v x)).
Time Proof.
Time (destruct x as (?, ds)).
Time
(destruct ds; try destruct id0; try destruct id;
  <ssreflect_plugin::ssrtclintros@0> auto =>//=; eauto 
  with twodb).
Time Qed.
Time
Lemma wf_disk1_update id0 i v x :
  wf_disk (disk1 x) \226\134\146 wf_disk (disk1 (upd_disk id0 i v x)).
Time Proof.
Time (destruct x as (?, ds)).
Time
(destruct ds; try destruct id0; try destruct id;
  <ssreflect_plugin::ssrtclintros@0> auto =>//=; eauto 
  with twodb).
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time rewrite /crash_inner_inv_type.
Time (intros).
Time iIntros "H".
Time iDestruct "H" as "(Hinv&#Hsrc)".
Time iDestruct "Hinv" as ( invG ) "Hinv".
Time rewrite /DBCrashInner /CrashInv.
Time iDestruct "Hinv" as ( l ) "(?&?)".
Time Qed.
Time
Lemma wf_disk0_fail id0 x :
  wf_disk (disk0 x) \226\134\146 wf_disk (disk0 (maybe_fail_disk id0 x)).
Time Proof.
Time (destruct x as (?, ds)).
Time
(destruct ds; try destruct id0; try destruct id;
  <ssreflect_plugin::ssrtclintros@0> auto =>//=; eauto 
  with twodb).
Time iMod (@inv_alloc \206\163 exm_invG iN _ DBCrashInner with "[-]").
Time Qed.
Time
Lemma wf_disk1_fail id0 x :
  wf_disk (disk1 x) \226\134\146 wf_disk (disk1 (maybe_fail_disk id0 x)).
Time Proof.
Time (destruct x as (?, ds)).
Time
(destruct ds; try destruct id0; try destruct id;
  <ssreflect_plugin::ssrtclintros@0> auto =>//=; eauto 
  with twodb).
Time Qed.
Time
Lemma disk_fail_only_one \207\131 \207\131' id d u :
  disks_state \207\131 = OnlyDisk id d \226\134\146 disk_fail \207\131 (Val \207\131' u) \226\134\146 \207\131 = \207\131'.
Time {
Time iNext.
Time Proof.
Time (intros Hds).
Time (inversion 1; inversion H1; subst; eauto).
Time -
Time (inversion H2).
Time subst.
Time (destruct \207\131).
Time (destruct disks_state0).
Time subst.
Time (simpl in *).
Time congruence.
Time (simpl in *).
Time (inversion Hds).
Time subst.
Time (simpl).
Time (destruct id; simpl; rewrite //=).
Time -
Time (inversion H2).
Time subst.
Time (destruct \207\131).
Time (destruct disks_state0).
Time subst.
Time (simpl in *).
Time congruence.
Time (simpl in *).
Time (iExists l; iFrame).
Time (inversion Hds).
Time subst.
Time (simpl).
Time (destruct id; simpl; rewrite //=).
Time Qed.
Time Lemma disk_fail_non_err \207\131 : \194\172 disk_fail \207\131 Err.
Time Proof.
Time (inversion 1 as [Hp| Hor]).
Time (inversion Hp).
Time (inversion Hor as [Hp| Hp]; inversion Hp).
Time Qed.
Time
Hint Resolve wf_disk0_fail wf_disk1_fail wf_disk0_update wf_disk1_update
  disk_fail_non_err: twodb.
Time
Ltac
 inv_step :=
  repeat
   (match goal with
    | H:unit |- _ => destruct H
    | H:and_then _ _ _ Err
      |- _ =>
          let Hhd_err := fresh "Hhd_err" in
          let Hhd := fresh "Hhd" in
          let Htl_err := fresh "Htl_err" in
          inversion H as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; clear H
    | H:such_that _ _ _ |- _ => inversion H; subst; clear H
    | H:pure _ _ _ |- _ => inversion H; subst; clear H
    | H:puts _ _ _ |- _ => inversion H; subst; clear H
    | H:reads _ _ _ |- _ => inversion H; subst; clear H
    | H:Some _ = Some _ |- _ => apply Some_inj in H; subst
    | H:Cinl _ = Cinl _ |- _ => inversion H; clear H; subst
    | H:(?a, ?b) = (?c, ?d) |- _ => apply pair_inj in H as (?, ?); subst
    | H:disk_fail _ Err |- _ => exfalso; eapply disk_fail_non_err; eauto
    | H:l.(Layer.sem).(Proc.step) ?op _ (Val _ _)
      |- _ =>
          let Hhd := fresh "Hhd" in
          let Htl := fresh "Htl" in
          destruct H as (?, (?, (Hhd, Htl)))
    | H:l.(Layer.sem).(Proc.step) ?op _ (Val _ _) |- _ => inversion H; subst
    end; auto with twodb).
Time
Ltac
 inv_case :=
  match goal with
  | H:rel_or _ _ _ _
    |- _ => let Hcase := fresh "Hcase" in
            inversion H as [Hcase| Hcase]
  end.
Time
Lemma disk_status_ctx_upd id0 i v x :
  disk_status_ctx (disks_state (upd_disk id0 i v x)) =
  disk_status_ctx (disks_state x).
Time Proof.
Time rewrite /disk_status_ctx /to_status.
Time (destruct x as (?, []); destruct id0; try destruct id; rewrite //=).
Time }
Time iModIntro.
Time iFrame.
Time Qed.
Time
Definition status_token (ds : DisksState) : iProp \206\163 :=
  match ds with
  | BothDisks _ _ => True%I
  | OnlyDisk id _ => is_OnlyDisk id
  end.
Time iExists tt.
Time iFrame "Hsrc".
Time
Lemma disk_status_update \207\131 \207\131' u :
  disk_fail \207\131 (Val \207\131' u)
  \226\134\146 disk_status_ctx \207\131.(disks_state)
    ==\226\136\151 disk_status_ctx \207\131'.(disks_state) \226\136\151 status_token \207\131'.(disks_state).
Time Proof.
Time (intros Hfail).
Time (destruct \207\131 as (?, [])).
Time Qed.
Time *
Time
(inversion Hfail; inv_step; try inv_case; inv_step;
  <ssreflect_plugin::ssrtclintros@0> eauto =>//=; iIntros "H"; eauto; iMod
  (disk_status_update_both with "[$]") as "H"; eauto).
Time Lemma exec_inner_inv : exec_inner_inv_type.
Time Proof.
Time rewrite /exec_inner_inv_type.
Time (intros).
Time iIntros "H".
Time iDestruct "H" as "(Hinv&#Hsrc)".
Time iDestruct "Hinv" as ( invG v ) "Hinv".
Time iDestruct "Hinv" as "(?&Hinv)".
Time iDestruct "Hinv" as ( \206\1792 ) "(Hlock&Hinner)".
Time
iMod
 (@lock_init \206\163 (ExMachG _ exm_invG exm_mem_inG exm_disk_inG _) _ lN lock_addr
    _ (DBLockInv \206\1792) with "[$] [-Hinner]") as ( \206\1791 ) "H".
Time {
Time iFrame.
Time }
Time iMod (@inv_alloc \206\163 exm_invG iN _ (DBInnerInv \206\1792) with "[Hinner]").
Time {
Time iFrame.
Time }
Time iModIntro.
Time rewrite /DBInv.
Time iFrame "Hsrc".
Time iExists \206\1791 , \206\1792.
Time iFrame.
Time Qed.
Time Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Time Proof.
Time iIntros ( ? ? ) "? (?&H)".
Time iDestruct "H" as ( \206\1791 \206\1792 ) "(Hlock&Hinv)".
Time iInv "Hinv" as ( l' ) ">(Htok&Hsource)" "_".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (lock_crack with "Hlock") as ">H" ;
 first  by solve_ndisj).
Time *
Time (eapply disk_fail_only_one in Hfail; subst; eauto).
Time Qed.
Time
Lemma wp_write_disk0' s E i v' v :
  {{{ \226\150\183 i d0\226\151\175\226\134\166 v' }}} write_disk d0 i v @ s; E {{{ RET tt; 
  i d0\226\151\175\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iDestruct "H" as ( v ) "(?&?)".
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (apply snd_lift_non_err).
Time (inversion 1; inv_step).
Time (repeat deex).
Time inv_step.
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (iExists _ , nil; eauto).
Time (inversion Hstep; subst).
Time inv_step.
Time iFrame.
Time iDestruct "Hown" as "(?&Hown)".
Time
iDestruct "Hown" as ( mems disk0 disk1 ) "(Hmem&Hown0&Hown1&Hstatus&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (?, Hsize))).
Time iDestruct (gen_heap_valid with "Hown0 Hi") as % Hin_bound.
Time iMod (@gen_heap_update with "Hown0 Hi") as "[Hown0 Hi]".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by eauto).
Time iIntros ( ? ? ? ? ) "(?&Hstate&Hmem)".
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
Time iSplitR "Hi H\206\166".
Time iMod init_ghost_list as ( \206\1792' ) "[Hauth Hfrag]".
Time {
Time (simpl in Heq_disk).
Time (destruct \207\131.(disks_state) as [?| ?] eqn:Heq_state).
Time -
Time (simpl).
Time rewrite Heq_state.
Time iMod (disk_status_update_both with "Hstatus") as "$".
Time iModIntro.
Time iExists O.
Time iFrame.
Time iFrame.
Time iExists \206\1792'.
Time rewrite /DBInnerInv /DBLockInv.
Time iSplitR "Hstate Hauth".
Time {
Time iIntros.
Time (iExists _; iFrame).
Time }
Time {
Time (iExists _; iFrame).
Time }
Time Qed.
Time End sRO.
Time Module sR:=  exmach_refinement sRT sRO.
Time Import sR.
Time
Lemma exmach_crash_refinement_seq {T} \207\1311c \207\1311a (es : proc_seq DB.Op T) :
  sRT.init_absr \207\1311a \207\1311c
  \226\134\146 wf_client_seq es
    \226\134\146 \194\172 proc_exec_seq DB.l es (rec_singleton (Ret ())) (1, \207\1311a) Err
      \226\134\146 \226\136\128 \207\1312c res,
          proc_exec_seq ExMach.l (compile_proc_seq StatDb.Impl.impl es)
            (rec_singleton recv) (1, \207\1311c) (Val \207\1312c res)
          \226\134\146 \226\136\131 \207\1312a,
              proc_exec_seq DB.l es (rec_singleton (Ret tt)) 
                (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (apply sR.R.crash_refinement_seq).
Time Qed.
Time Print Assumptions exmach_crash_refinement_seq.
Time iExists _ , (<[i:=v]> disk0) , disk1.
Time iFrame.
Time iFrame.
Time (simpl).
Time (intuition; eauto).
Time subst.
Time (inversion Hhd).
Time {
Time iPureIntro.
Time (split_and !; eauto; inv_step).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite Heq_state =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> destruct x0 =>//=).
Time (simpl in *).
Time subst.
Time (simpl; intuition; eauto).
Time rewrite /upd_default.
Time *
Time rewrite /upd_disk /upd_default Hin_bound //.
Time *
Time (split_and !; intuition eauto with twodb).
Time }
Time (inv_case; inv_step).
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time *
Time rewrite /upd_disk /upd_default Hin_bound //.
Time *
Time (split_and !; intuition eauto with twodb).
Time }
Time -
Time (destruct id).
Time *
Time subst.
Time rewrite Heq_state.
Time (simpl).
Time iFrame.
Time (simpl).
Time rewrite /disk_state_interp.
Time iFrame.
Time iExists _ , (<[i:=v]> d) , disk1.
Time iFrame.
Time iFrame.
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time inv_step.
Time rewrite disk_status_ctx_upd Heq_state.
Time iFrame.
Time iPureIntro.
Time (split_and !; eauto).
Time **
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /upd_disk /upd_default Heq_state
 =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> destruct x0 =>//=).
Time (simpl in *).
Time subst.
Time (simpl; intuition; eauto).
Time rewrite Hin_bound //.
Time **
Time (split_and !; intuition eauto with twodb).
Time *
Time subst.
Time rewrite Heq_state.
Time (simpl).
Time iFrame.
Time (simpl).
Time rewrite /disk_state_interp.
Time iFrame.
Time iExists _ , (<[i:=v]> disk0) , d.
Time iFrame.
Time iFrame.
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time inv_step.
Time rewrite disk_status_ctx_upd Heq_state.
Time iFrame.
Time iPureIntro.
Time (split_and !; eauto).
Time **
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /upd_disk /upd_default Heq_state
 =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> destruct x0 =>//=).
Time (simpl in *).
Time subst.
Time (simpl; intuition; eauto).
Time **
Time (split_and !; intuition eauto with twodb).
Time }
Time by iApply "H\206\166".
Time Qed.
Time
Lemma wp_write_disk0 s E i v' v v0 :
  {{{ \226\150\183 i d0\226\134\166 v' \226\136\151 \226\150\183 lease0 i v0 }}} write_disk d0 i v @ s; E {{{ RET tt; 
  i d0\226\134\166 v \226\136\151 lease0 i v}}}.
Time Proof.
Time iIntros ( \206\166 ) "(>(Hi&Hmaster)&>Hlease) H\206\166".
Time rewrite /lease0.
Time
iMod (master_lease_update (hG:=exm_disk0_inG) i v' v0 v with "[$] [$]") as
 "(?&?)".
Time iApply (wp_write_disk0' with "[$]").
Time iNext.
Time iIntros.
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_read_disk0' s E i v :
  {{{ \226\150\183 i d0\226\151\175\226\134\166 v }}} read_disk d0 i @ s; E {{{ mv, RET mv; 
  i d0\226\151\175\226\134\166 v \226\136\151 match mv with
             | None => is_OnlyDisk d1
             | Some v' => \226\140\156v = v'\226\140\157
             end}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (apply snd_lift_non_err).
Time (inversion 1; inv_step).
Time (repeat deex).
Time inv_step.
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iDestruct "Hown" as "(?&Hown)".
Time
iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown0 Hi") as % Hin_bound.
Time (simpl in Heq_disk).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (disk_status_update with "Hstatus") as
 "($&Htok)" ; first  eauto).
Time (destruct \207\131.(disks_state) as [?| ?] eqn:Heq_state).
Time -
Time (simpl).
Time iFrame.
Time iSplitR "Hi H\206\166 Htok".
Time *
Time iExists _ , disk0 , disk1.
Time iFrame.
Time iFrame.
Time (simpl).
Time (intuition; eauto).
Time subst.
Time (inversion Hhd).
Time {
Time iPureIntro.
Time (split_and !; eauto; inv_step).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite Heq_state =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time (inv_case; inv_step).
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time *
Time (inversion Hhd).
Time {
Time rewrite /lookup_disk /get_disk /TwoDisk.disk0.
Time inv_step.
Time rewrite Heq_state.
Time rewrite /lookup_default.
Time intuition.
Time subst.
Time rewrite Hin_bound.
Time (iApply "H\206\166"; eauto).
Time }
Time (inv_case; inv_step).
Time {
Time rewrite /lookup_disk /get_disk /maybe_fail_disk Heq_state //=.
Time (iApply "H\206\166"; eauto).
Time }
Time {
Time rewrite /lookup_disk /get_disk /maybe_fail_disk Heq_state //=.
Time rewrite /lookup_default.
Time intuition.
Time subst.
Time rewrite Hin_bound.
Time (iApply "H\206\166"; eauto).
Time }
Time -
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time (simpl).
Time iFrame.
Time iSplitR "Hi H\206\166 Htok".
Time *
Time iExists _ , disk0 , disk1.
Time iFrame.
Time iFrame.
Time (simpl).
Time (intuition; eauto).
Time subst.
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time *
Time
rewrite /lookup_disk /get_disk /TwoDisk.disk0 /TwoDisk.disk1 ?Heq_state //=.
Time
(destruct id; rewrite /lookup_default; intuition; subst; rewrite ?Hin_bound;
  iApply "H\206\166"; eauto).
Time Qed.
Time
Lemma wp_read_disk0_only0' s E i v :
  {{{ \226\150\183 i d0\226\151\175\226\134\166 v \226\136\151 \226\150\183 is_OnlyDisk d0 }}} read_disk d0 i @ s; E {{{ RET 
  Some v; i d0\226\151\175\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) "(>Hi&>His_only) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (apply snd_lift_non_err).
Time (inversion 1; inv_step).
Time (repeat deex).
Time inv_step.
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iDestruct "Hown" as "(?&Hown)".
Time
iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown0 Hi") as % Hin_bound.
Time iDestruct (disk_status_agree with "[$] [$]") as % Hstatus.
Time (destruct Hstatus as (disk0', Heq)).
Time (simpl in *).
Time rewrite Heq in  {} Heq_disk.
Time subst.
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time iFrame.
Time iSplitR "Hi H\206\166".
Time *
Time iExists _ , disk0' , disk1.
Time iFrame.
Time iPureIntro.
Time (split_and !; eauto; inv_step).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite Heq =>//=).
Time (split_and !; intuition eauto with twodb).
Time *
Time rewrite /lookup_disk /get_disk /TwoDisk.disk0.
Time inv_step.
Time rewrite Heq.
Time rewrite /lookup_default.
Time intuition.
Time subst.
Time rewrite Hin_bound.
Time (iApply "H\206\166"; eauto).
Time Qed.
Time
Lemma wp_read_disk0 s E i v :
  {{{ \226\150\183 i d0\226\134\166 v }}} read_disk d0 i @ s; E {{{ mv, RET mv; 
  i d0\226\134\166 v \226\136\151 match mv with
            | None => is_OnlyDisk d1
            | Some v' => \226\140\156v = v'\226\140\157
            end}}}.
Time Proof.
Time iIntros ( \206\166 ) ">(Hi&?) H\206\166".
Time iApply (wp_read_disk0' with "[$]").
Time iNext.
Time iIntros ( ? ) "(?&?)".
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_read_disk0_only0 s E i v :
  {{{ \226\150\183 i d0\226\134\166 v \226\136\151 \226\150\183 is_OnlyDisk d0 }}} read_disk d0 i @ s; E {{{ RET 
  Some v; i d0\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) "(>(Hi&?)&?) H\206\166".
Time iApply (wp_read_disk0_only0' with "[$]").
Time iNext.
Time iIntros "?".
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_write_disk1' s E i v' v :
  {{{ \226\150\183 i d1\226\151\175\226\134\166 v' }}} write_disk d1 i v @ s; E {{{ RET tt; 
  i d1\226\151\175\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (apply snd_lift_non_err).
Time (inversion 1; inv_step).
Time (repeat deex).
Time inv_step.
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iDestruct "Hown" as "(?&Hown)".
Time
iDestruct "Hown" as ( mems disk0 disk1 ) "(Hmem&Hown0&Hown1&Hstatus&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (?, Hsize))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time iMod (@gen_heap_update with "Hown1 Hi") as "[Hown1 Hi]".
Time iSplitR "Hi H\206\166".
Time {
Time (simpl in Heq_disk).
Time (destruct \207\131.(disks_state) as [?| ?] eqn:Heq_state).
Time -
Time (simpl).
Time rewrite Heq_state.
Time iMod (disk_status_update_both with "Hstatus") as "$".
Time iFrame.
Time iExists _ , disk0 , (<[i:=v]> disk1).
Time iFrame.
Time iFrame.
Time (simpl).
Time (intuition; eauto).
Time subst.
Time (inversion Hhd).
Time {
Time iPureIntro.
Time (split_and !; eauto; inv_step).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite Heq_state =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> destruct x0 =>//=).
Time (simpl in *).
Time subst.
Time (simpl; intuition; eauto).
Time rewrite /upd_default.
Time *
Time rewrite /upd_disk /upd_default Hin_bound //.
Time *
Time (split_and !; intuition eauto with twodb).
Time }
Time (inv_case; inv_step).
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time *
Time rewrite /upd_disk /upd_default Hin_bound //.
Time *
Time (split_and !; intuition eauto with twodb).
Time }
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time -
Time (destruct id).
Time *
Time subst.
Time rewrite Heq_state.
Time (simpl).
Time iFrame.
Time (simpl).
Time rewrite /disk_state_interp.
Time iFrame.
Time iExists _ , d , (<[i:=v]> disk1).
Time iFrame.
Time iFrame.
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time inv_step.
Time rewrite disk_status_ctx_upd Heq_state.
Time iFrame.
Time iPureIntro.
Time (split_and !; eauto).
Time **
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /upd_disk /upd_default Heq_state
 =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> destruct x0 =>//=).
Time (simpl in *).
Time subst.
Time (simpl; intuition; eauto).
Time **
Time (split_and !; intuition eauto with twodb).
Time *
Time subst.
Time rewrite Heq_state.
Time (simpl).
Time iFrame.
Time (simpl).
Time rewrite /disk_state_interp.
Time iFrame.
Time iExists _ , disk0 , (<[i:=v]> d).
Time iFrame.
Time iFrame.
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time inv_step.
Time rewrite disk_status_ctx_upd Heq_state.
Time iFrame.
Time iPureIntro.
Time (split_and !; eauto).
Time **
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /upd_disk /upd_default Heq_state
 =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> destruct x0 =>//=).
Time (simpl in *).
Time subst.
Time (simpl; intuition; eauto).
Time rewrite Hin_bound //.
Time **
Time (split_and !; intuition eauto with twodb).
Time }
Time by iApply "H\206\166".
Time Qed.
Time
Lemma wp_write_disk1 s E i v' v v0 :
  {{{ \226\150\183 i d1\226\134\166 v' \226\136\151 \226\150\183 lease1 i v0 }}} write_disk d1 i v @ s; E {{{ RET tt; 
  i d1\226\134\166 v \226\136\151 lease1 i v}}}.
Time Proof.
Time iIntros ( \206\166 ) "(>(Hi&Hmaster)&>Hlease) H\206\166".
Time iMod (master_lease_update i v' v0 v with "[$] [$]") as "(?&?)".
Time iApply (wp_write_disk1' with "[$]").
Time iNext.
Time iIntros.
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_read_disk1' s E i v :
  {{{ \226\150\183 i d1\226\151\175\226\134\166 v }}} read_disk d1 i @ s; E {{{ mv, RET mv; 
  i d1\226\151\175\226\134\166 v \226\136\151 match mv with
             | None => is_OnlyDisk d0
             | Some v' => \226\140\156v = v'\226\140\157
             end}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (apply snd_lift_non_err).
Time (inversion 1; inv_step).
Time (repeat deex).
Time inv_step.
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iDestruct "Hown" as "(?&Hown)".
Time
iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time (simpl in Heq_disk).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (disk_status_update with "Hstatus") as
 "($&Htok)" ; first  eauto).
Time (destruct \207\131.(disks_state) as [?| ?] eqn:Heq_state).
Time -
Time (simpl).
Time iFrame.
Time iSplitR "Hi H\206\166 Htok".
Time *
Time iExists _ , disk0 , disk1.
Time iFrame.
Time iFrame.
Time (simpl).
Time (intuition; eauto).
Time subst.
Time (inversion Hhd).
Time {
Time iPureIntro.
Time (split_and !; eauto; inv_step).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite Heq_state =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time (inv_case; inv_step).
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time {
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time }
Time *
Time (inversion Hhd).
Time {
Time rewrite /lookup_disk /get_disk /TwoDisk.disk1.
Time inv_step.
Time rewrite Heq_state.
Time rewrite /lookup_default.
Time intuition.
Time subst.
Time rewrite Hin_bound.
Time (iApply "H\206\166"; eauto).
Time }
Time (inv_case; inv_step).
Time {
Time rewrite /lookup_disk /get_disk /maybe_fail_disk Heq_state //=.
Time rewrite /lookup_default.
Time intuition.
Time subst.
Time rewrite Hin_bound.
Time (iApply "H\206\166"; eauto).
Time }
Time {
Time rewrite /lookup_disk /get_disk /maybe_fail_disk Heq_state //=.
Time (iApply "H\206\166"; eauto).
Time }
Time -
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time (simpl).
Time iFrame.
Time iSplitR "Hi H\206\166 Htok".
Time *
Time iExists _ , disk0 , disk1.
Time iFrame.
Time iFrame.
Time (simpl).
Time (intuition; eauto).
Time subst.
Time iPureIntro.
Time (split_and !; eauto).
Time
(subst; <ssreflect_plugin::ssrtclintros@0> rewrite /maybe_fail_disk Heq_state
  =>//=).
Time (split_and !; intuition eauto with twodb).
Time *
Time
rewrite /lookup_disk /get_disk /TwoDisk.disk0 /TwoDisk.disk1 ?Heq_state //=.
Time
(destruct id; rewrite /lookup_default; intuition; subst; rewrite ?Hin_bound;
  iApply "H\206\166"; eauto).
Time Qed.
Time
Lemma wp_read_disk1 s E i v :
  {{{ \226\150\183 i d1\226\134\166 v }}} read_disk d1 i @ s; E {{{ mv, RET mv; 
  i d1\226\134\166 v \226\136\151 match mv with
            | None => is_OnlyDisk d0
            | Some v' => \226\140\156v = v'\226\140\157
            end}}}.
Time Proof.
Time iIntros ( \206\166 ) ">(Hi&?) H\206\166".
Time iApply (wp_read_disk1' with "[$]").
Time iNext.
Time iIntros ( ? ) "(?&?)".
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_write_disk0_only1' {T} s E1 E2 i v v' (p : proc Op T) 
  \206\166 :
  to_val p = None
  \226\134\146 (|={E1,E2}=> (i d0\226\151\175\226\134\166 v \226\136\151 is_OnlyDisk d1)
                 \226\136\151 (i d0\226\151\175\226\134\166 v' -\226\136\151 |={E2,E1}=> WP p @ s; E1 {{ \206\166 }}))
    -\226\136\151 WP p @ s; E1 {{ \206\166 }}.
Time Proof.
Time iIntros ( ? ) "Hfupd".
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_lift_pre_step ; first  auto).
Time iIntros ( (n, \207\131) ) "Hown".
Time iMod "Hfupd".
Time iDestruct "Hfupd" as "((Hi&Honly)&Hwand)".
Time iDestruct "Hown" as "(?&Hown)".
Time
iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown0 Hi") as % Hin_bound.
Time iDestruct (disk_status_agree with "[$] [$]") as % Hstatus.
Time (destruct Hstatus as (disk1', Heq)).
Time (simpl in *).
Time rewrite Heq in  {} Heq_disk.
Time subst.
Time iMod (@gen_heap_update with "Hown0 Hi") as "[Hown0 Hi]".
Time iMod ("Hwand" with "Hi").
Time iFrame.
Time (iExists _ , _ , _; iFrame).
Time (simpl).
Time rewrite Heq.
Time eauto.
Time Qed.
Time
Lemma wp_write_disk0_only1 {T} s E1 E2 i v v' v0 (p : proc Op T) 
  \206\166 :
  to_val p = None
  \226\134\146 (|={E1,E2}=> (i d0\226\134\166 v \226\136\151 lease0 i v0 \226\136\151 is_OnlyDisk d1)
                 \226\136\151 (i d0\226\134\166 v' \226\136\151 lease0 i v'
                    -\226\136\151 |={E2,E1}=> WP p @ s; E1 {{ \206\166 }}))
    -\226\136\151 WP p @ s; E1 {{ \206\166 }}.
Time Proof.
Time iIntros ( ? ) "H".
Time (iApply wp_write_disk0_only1'; auto).
Time iMod "H" as "(((?&?)&?&?)&Hwand)".
Time
iMod (master_lease_update (hG:=exm_disk0_inG) i v v0 v' with "[$] [$]") as
 "(?&?)".
Time iModIntro.
Time iFrame.
Time iIntros.
Time iApply "Hwand".
Time iFrame.
Time Qed.
Time
Lemma wp_read_disk1_only1' s E i v :
  {{{ \226\150\183 i d1\226\151\175\226\134\166 v \226\136\151 \226\150\183 is_OnlyDisk d1 }}} read_disk d1 i @ s; E {{{ RET 
  Some v; i d1\226\151\175\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) "(>Hi&>His_only) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (apply snd_lift_non_err).
Time (inversion 1; inv_step).
Time (repeat deex).
Time inv_step.
Time }
Time iIntros ( e2 (n2, \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iDestruct "Hown" as "(?&Hown)".
Time
iDestruct "Hown" as ( mems disk0 disk1 ) "(Hown_mem&Hown0&Hown1&Hstatus&Hp)".
Time iDestruct "Hp" as % (Heq_mem, (Heq_disk, (Hsize, ?))).
Time iDestruct (gen_heap_valid with "Hown1 Hi") as % Hin_bound.
Time iDestruct (disk_status_agree with "[$] [$]") as % Hstatus.
Time (destruct Hstatus as (disk1', Heq)).
Time (simpl in *).
Time rewrite Heq in  {} Heq_disk.
Time subst.
Time (eapply disk_fail_only_one in Hhd; eauto).
Time subst.
Time iFrame.
Time iSplitR "Hi H\206\166".
Time *
Time iExists _ , disk0 , disk1'.
Time iFrame.
Time iPureIntro.
Time (split_and !; eauto; inv_step).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite Heq =>//=).
Time (split_and !; intuition eauto with twodb).
Time *
Time rewrite /lookup_disk /get_disk /TwoDisk.disk1.
Time inv_step.
Time rewrite Heq.
Time rewrite /lookup_default.
Time intuition.
Time subst.
Time rewrite Hin_bound.
Time (iApply "H\206\166"; eauto).
Time Qed.
Time
Lemma wp_read_disk1_only1 s E i v :
  {{{ \226\150\183 i d1\226\134\166 v \226\136\151 \226\150\183 is_OnlyDisk d1 }}} read_disk d1 i @ s; E {{{ RET 
  Some v; i d1\226\134\166 v}}}.
Time Proof.
Time iIntros ( \206\166 ) "(>(Hi&?)&?) H\206\166".
Time iApply (wp_read_disk1_only1' with "[$]").
Time iNext.
Time iIntros "?".
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time Lemma disk0_lease_agree i v1 v2 : i d0\226\134\166 v1 -\226\136\151 lease0 i v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "(_&?) ?".
Time iApply (master_lease_agree with "[$] [$]").
Time Qed.
Time
Lemma disk0_next i v :
  i d0\226\134\166 v
  ==\226\136\151 (i d0\226\151\175\226\134\166 v \226\136\151 next_master (hG:=exm_disk0_inG) i v)
      \226\136\151 next_lease (hG:=exm_disk0_inG) i v.
Time Proof.
Time iIntros "(?&?)".
Time by iMod (master_next with "[$]") as "($&$)".
Time Qed.
Time Lemma disk1_lease_agree i v1 v2 : i d1\226\134\166 v1 -\226\136\151 lease1 i v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "(_&?) ?".
Time iApply (master_lease_agree with "[$] [$]").
Time Qed.
Time
Lemma disk1_next i v :
  i d1\226\134\166 v
  ==\226\136\151 (i d1\226\151\175\226\134\166 v \226\136\151 next_master (hG:=exm_disk1_inG) i v)
      \226\136\151 next_lease (hG:=exm_disk1_inG) i v.
Time Proof.
Time iIntros "(?&?)".
Time by iMod (master_next with "[$]") as "($&$)".
Time Qed.
Time End lifting.
Time Class lockG \206\163 := LockG {lock_tokG :> inG \206\163 (exclR unitO)}.
Time Definition lock\206\163 : gFunctors := #[ GFunctor (exclR unitO)].
Time Instance subG_lock\206\163  {\206\163}: (subG lock\206\163 \206\163 \226\134\146 lockG \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Section lock.
Time Context `{!exmachG \206\163} `{!lockG \206\163}.
Time
Definition lock_inv (\206\179 : gname) (i : addr) (P : iProp \206\163) : 
  iProp \206\163 := (i m\226\134\166 0 \226\136\151 P \226\136\151 own \206\179 (Excl ()) \226\136\168 (\226\136\131 v, i m\226\134\166 v \226\136\151 \226\140\156v \226\137\160 0\226\140\157))%I.
Time
Definition is_lock (N : namespace) (\206\179 : gname) (i : addr) 
  (P : iProp \206\163) : iProp \206\163 := (inv N (lock_inv \206\179 i P))%I.
Time Definition locked (\206\179 : gname) : iProp \206\163 := own \206\179 (Excl ()).
Time #[global]
Instance is_lock_persistent  N \206\179 i R: (Persistent (is_lock N \206\179 i R)).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance locked_timless  \206\179: (Timeless (locked \206\179)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma lock_init N i v (R : iProp \206\163) E :
  i m\226\134\166 v -\226\136\151 (\226\140\156v = 0\226\140\157 -\226\136\151 R) ={E}=\226\136\151 \226\136\131 \206\179, is_lock N \206\179 i R.
Time Proof.
Time iIntros "Hl HR".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (Excl ())) as ( \206\179 ) "Hexcl"
 ; first  done).
Time iMod (inv_alloc N _ (lock_inv \206\179 i R) with "[-]").
Time {
Time iNext.
Time (destruct (nat_eq_dec v 0)).
Time *
Time subst.
Time (iLeft; iFrame).
Time (iApply "HR"; auto).
Time *
Time iRight.
Time iExists _.
Time iFrame.
Time eauto.
Time }
Time (iModIntro; iExists _; done).
Time Qed.
Time
Lemma lock_init_unlocked N i (R : iProp \206\163) E :
  i m\226\134\166 0 -\226\136\151 R ={E}=\226\136\151 \226\136\131 \206\179, is_lock N \206\179 i R.
Time Proof.
Time iIntros "Hl HR".
Time iApply (lock_init with "Hl").
Time (iIntros "_"; iFrame).
Time Qed.
Time
Lemma lock_crack N i (R : iProp \206\163) \206\179 E :
  \226\134\145N \226\138\134 E \226\134\146 is_lock N \206\179 i R ={E,E \226\136\150 \226\134\145N}=\226\136\151 \226\150\183 (\226\136\131 v, i m\226\134\166 v \226\136\151 (\226\140\156v = 0\226\140\157 -\226\136\151 R)).
Time Proof.
Time (intros).
Time rewrite /is_lock.
Time iIntros "Hinv".
Time iInv "Hinv" as "[(?&?&?)|HR]" "_".
Time -
Time iModIntro.
Time iExists 0.
Time iNext.
Time (iFrame; iIntros; auto).
Time -
Time iModIntro.
Time iNext.
Time iDestruct "HR" as ( v ) "(?&%)".
Time iExists v.
Time iFrame.
Time (iIntros; congruence).
Time Qed.
Time
Lemma wp_lock N \206\179 i (R : iProp \206\163) :
  {{{ is_lock N \206\179 i R }}} lock i {{{ RET tt; locked \206\179 \226\136\151 R}}}.
Time Proof.
Time iIntros ( \206\166 ) "#Hlock H\206\166".
Time iL\195\182b as "IH".
Time (wp_loop; wp_bind).
Time iInv N as "[HL|>HUL]".
Time -
Time iDestruct "HL" as "(>H&?&>?)".
Time iApply (wp_cas_suc with "[$]").
Time (iIntros "!> Hl !>"; iFrame).
Time iSplitL "Hl".
Time {
Time iRight.
Time iNext.
Time iExists _.
Time iFrame.
Time eauto.
Time }
Time rewrite //=.
Time wp_ret.
Time wp_ret.
Time (iApply "H\206\166"; iFrame).
Time -
Time iDestruct "HUL" as ( v ) "(?&%)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_cas_fail with "[$]") ; first 
 done).
Time (iIntros "!> Hl !>"; iFrame).
Time iSplitL "Hl".
Time {
Time iRight.
Time iNext.
Time iExists _.
Time iFrame.
Time eauto.
Time }
Time rewrite //=.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct nat_eq_dec ; first  by congruence).
Time wp_ret.
Time (iApply "IH"; eauto).
Time Qed.
Time
Lemma wp_unlock N \206\179 i (R : iProp \206\163) :
  {{{ is_lock N \206\179 i R \226\136\151 locked \206\179 \226\136\151 R }}} unlock i {{{ RET tt; True}}}.
Time Proof.
Time iIntros ( \206\166 ) "(#Hlock&Hlocked&HR) H\206\166".
Time iInv N as "[HL|>HUL]".
Time -
Time iDestruct "HL" as "(>H&?&>Htok)".
Time
(<ssreflect_plugin::ssrtclintros@0> iDestruct
 (own_valid_2 with "Htok Hlocked") as % H =>//=).
Time -
Time iDestruct "HUL" as ( v ) "(?&%)".
Time (iApply (wp_write_mem with "[$]"); iIntros "!> H !>").
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "H\206\166" ; last  by iApply "H\206\166").
Time iLeft.
Time iFrame.
Time Qed.
Time
Lemma wp_unlock' N \206\179 i (R : iProp \206\163) :
  is_lock N \206\179 i R -\226\136\151 {{{ locked \206\179 \226\136\151 R }}} unlock i {{{ RET tt; True}}}.
Time Proof.
Time iIntros "#Hlock".
Time iAlways.
Time iIntros ( \206\166 ) "(Hlocked&HR) H\206\166".
Time iApply (wp_unlock with "[-H\206\166]").
Time {
Time iFrame "Hlock".
Time iFrame.
Time }
Time eauto.
Time Qed.
Time End lock.
