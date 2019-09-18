Time From iris.algebra Require Import auth gmap frac agree.
Time From iris.algebra Require Import auth gmap list.
Time From iris.algebra Require Import auth gmap list.
Time Require Import Goose.Proof.Interp.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time Require Export CSL.Refinement CSL.NamedDestruct.
Time
Require Import AtomicPairAPI AtomicPair.ImplLog ExMach.WeakestPre
  ExMach.RefinementAdequacy.
Time Require Import AtomicPair.Helpers.
Time Set Default Proof Using "All".
Time Unset Implicit Arguments.
Time From Tactical Require Import UnfoldLemma.
Time #[local]
Ltac
 destruct_ex_commit_inner H :=
  iDestruct H as ">H"; iDestruct "H" as ( ? ? ? ? ) "H".
Time #[local]
Ltac
 destruct_commit_inner' H :=
  iLDestruct H; repeat unify_ghost; repeat unify_lease.
Time #[local]
Ltac
 destruct_commit_inner H :=
  destruct_ex_commit_inner H; destruct_commit_inner' H.
Time #[local]
Ltac
 recommit' :=
  try iFrame "Hmain_inv"; try iFrame "Hlog_inv"; try iFrame "Hsrc_inv";
   try iFrame "Hcommit_inv".
Time #[local]Ltac recommit := iExists _ , _ , _ , _; iNamed recommit'.
Time #[local]
Ltac
 destruct_pairs :=
  repeat
   match goal with
   | H:nat * nat |- _ => destruct H; simpl fst; simpl snd
   | |- nat * nat => eexists; shelve
   end.
Time
Tactic Notation "handle_pairs" tactic(H) :=
 (destruct_pairs; unshelve H; destruct_pairs).
Time Section refinement_triples.
Time
Context `{!exmachG \206\163} `{lockG \206\163} `{!@cfgG AtomicPair.Op AtomicPair.l \206\163}
 `{!inG \206\163 (authR (optionUR (exclR (prodO natO natO))))}
 `{!inG \206\163
      (authR
         (optionUR (exclR (prodO natO (prodO natO (procTC AtomicPair.Op))))))}.
Time Import ExMach.
Time Record ghost_names :={\206\179flag : gname; \206\179src : gname}.
Time
Definition someone_writing P (p : nat * nat)
  (je : prodO natO (procTC AtomicPair.Op)) :=
  (\226\136\131 (K : proc AtomicPair.Op unit \226\134\146 proc AtomicPair.Op (projT1 (snd je))) 
     `{LanguageCtx AtomicPair.Op unit (projT1 (snd je)) AtomicPair.l K},
     P
     \226\136\151 \226\140\156projT2 (snd je) = K (Call (AtomicPair.Write p))\226\140\157
       \226\136\151 fst je \226\164\135 projT2 (snd je))%I.
Time
Definition someone_writing_unfold P p je :=
  unfold_lemma (someone_writing P p je).
Time #[global]
Instance someone_writing_timeless :
 (Timeless P \226\134\146 Timeless (someone_writing P p je)).
Time Proof.
Time (apply _).
Time
Require Import OneDiskAPI ReplicatedDiskImpl ReplicatedDisk.WeakestPre
  ReplicatedDisk.RefinementAdequacy.
Time Qed.
Time #[global]Opaque someone_writing.
Time
Definition FlagInv (\206\147 : ghost_names) flag :=
  (named "Hflag_auth" (own (\206\179flag \206\147) (\226\151\143 Excl' flag))
   \226\136\151 named "Hcommit" (log_commit d\226\134\166 fst flag))%I.
Time
Definition CommitOff (pcurr psrc : nat * nat) : iProp \206\163 := \226\140\156pcurr = psrc\226\140\157%I.
Time
Definition CommitOn P plog flagsnd := (someone_writing P plog flagsnd)%I.
Time
Definition MainInv (pcurr : nat * nat) :=
  (named "Hmain_fst" (main_fst d\226\134\166 fst pcurr)
   \226\136\151 named "Hmain_snd" (main_snd d\226\134\166 snd pcurr))%I.
Time
Definition LogInv (plog : nat * nat) :=
  (named "Hlog_fst" (log_fst d\226\134\166 fst plog)
   \226\136\151 named "Hlog_snd" (log_snd d\226\134\166 snd plog))%I.
Time Set Default Proof Using "All".
Time Unset Implicit Arguments.
Time Import agree.
Time From Tactical Require Import UnfoldLemma.
Time
Definition SrcInv \206\147 (psrc : nat * nat) :=
  (named "Hsrc_auth" (own (\206\179src \206\147) (\226\151\143 Excl' psrc))
   \226\136\151 named "Hsrc" (source_state psrc))%I.
Time
Definition CommitInner' P (\206\147 : ghost_names) flag
  (plog pcurr psrc : nat * nat) :=
  (named "Hcommit_inv" (FlagInv \206\147 flag)
   \226\136\151 named "Hmain_inv" (MainInv pcurr)
     \226\136\151 named "Hlog_inv" (LogInv plog)
       \226\136\151 named "Hsrc_inv" (SrcInv \206\147 psrc)
         \226\136\151 named "Hsomewriter"
             match fst flag with
             | O => CommitOff pcurr psrc
             | S n' => CommitOn P plog (snd flag)
             end)%I.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementAdequacy
  CSL.RefinementIdempotenceModule.
Time Definition addrset := dom (gset nat) init_zero.
Time Opaque init_zero size.
Time Definition addrset_unfold := unfold_lemma addrset.
Time Lemma not_lt_size_not_in_addrset a : \194\172 a < size \226\134\146 a \226\136\137 addrset.
Time Proof.
Time (intros).
Time (apply not_elem_of_dom, init_zero_lookup_ge_None; lia).
Time
Definition CommitInner P (\206\147 : ghost_names) :=
  (\226\136\131 flag (plog : nat * nat) (pcurr : nat * nat) (psrc : nat * nat),
     CommitInner' P \206\147 flag plog pcurr psrc)%I.
Time Definition ExecInner \206\147 := CommitInner Registered \206\147.
Time
Definition MainLockInv \206\147 :=
  (\226\136\131 pcurr : nat * nat,
     lease main_fst (fst pcurr)
     \226\136\151 lease main_snd (snd pcurr) \226\136\151 own (\206\179src \206\147) (\226\151\175 Excl' pcurr))%I.
Time
Definition LogLockInv \206\147 :=
  (\226\136\131 plog : nat * nat,
     own (\206\179flag \206\147) (\226\151\175 Excl' (0, (0, existT _ (Ret tt) : procTC _)))
     \226\136\151 lease log_commit 0
       \226\136\151 lease log_fst (fst plog) \226\136\151 lease log_snd (snd plog))%I.
Time Definition mlN : namespace := nroot.@"lock_main".
Time Definition llN : namespace := nroot.@"lock_log".
Time Definition liN : namespace := nroot.@"inner_log".
Time
Definition ExecInv :=
  (\226\136\131 \206\147,
     source_ctx
     \226\136\151 (\226\136\131 \206\179lock_main, is_lock mlN \206\179lock_main main_lock (MainLockInv \206\147))
       \226\136\151 (\226\136\131 \206\179lock_log, is_lock llN \206\179lock_log log_lock (LogLockInv \206\147))
         \226\136\151 inv liN (CommitInner Registered \206\147))%I.
Time
Definition CrashStarter \206\147 :=
  (main_lock m\226\134\166 0
   \226\136\151 log_lock m\226\134\166 0
     \226\136\151 (\226\136\131 flag (plog pcurr psrc : nat * nat),
          own (\206\179flag \206\147) (\226\151\175 Excl' flag)
          \226\136\151 lease log_commit (fst flag)
            \226\136\151 lease log_fst (fst plog)
              \226\136\151 lease log_snd (snd plog)
                \226\136\151 lease main_fst (fst pcurr)
                  \226\136\151 lease main_snd (snd pcurr) \226\136\151 own (\206\179src \206\147) (\226\151\175 Excl' psrc)))%I.
Time Qed.
Time Lemma lt_size_in_addrset a : a < size \226\134\146 a \226\136\136 addrset.
Time Definition CrashInner \206\147 := (CommitInner True \206\147 \226\136\151 CrashStarter \206\147)%I.
Time Definition CrashInv \206\147 := (source_ctx \226\136\151 inv liN (CommitInner True \206\147))%I.
Time
Lemma someone_writing_weaken P Q p je :
  (P -\226\136\151 Q) -\226\136\151 someone_writing P p je -\226\136\151 someone_writing Q p je.
Time Proof.
Time (intros).
Time (apply elem_of_dom).
Time eexists.
Time (apply init_zero_lookup_lt_zero; lia).
Time Proof.
Time rewrite ?someone_writing_unfold.
Time iIntros "HPQ".
Time iIntros "H".
Time Import Data.
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time
Class fsPreG (m : GoModel) {wf : GoModelWf m} \206\163 :=
 FsPreG {go_fs_dlocks_preG :> Count_Heap.gen_heapPreG string unit \206\163;
         go_fs_dirs_preG :> gen_heapPreG string (gset string) \206\163;
         go_fs_paths_preG :> gen_dirPreG string string Inode \206\163;
         go_fs_inodes_preG :> gen_heapPreG Inode (List.list byte) \206\163;
         go_fs_fds_preG :> gen_heapPreG File (Inode * OpenMode) \206\163;
         go_fs_domalg_preG :> ghost_mapG (discreteO (gset string)) \206\163}.
Time iDestruct "H" as ( K ? ) "(HP&?&?)".
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
Time iExists _ , _.
Time
Definition fs\206\163 (m : GoModel) {wf : GoModelWf m} : gFunctors :=
  #[ gen_heap\206\163 string (gset string); Count_Heap.gen_heap\206\163 string unit;
  gen_dir\206\163 string string Inode; gen_heap\206\163 Inode (List.list byte);
  gen_heap\206\163 File (Inode * OpenMode); ghost_map\206\163 (discreteO (gset string))].
Time (assert (a \226\136\136 dom (gset nat) \207\131.(OneDisk.disk_state))).
Time {
Time (apply elem_of_dom; eauto).
Time iFrame.
Time }
Time set_solver.
Time #[global]
Instance subG_fsPreG  m {wf : GoModelWf m} {\206\163}:
 (subG (fs\206\163 m) \206\163 \226\134\146 (fsPreG m) \206\163).
Time Proof.
Time solve_inG.
Time by iApply "HPQ".
Time Qed.
Time Qed.
Time
Class goosePreG (goose_model : GoModel) {wf : GoModelWf goose_model} \206\163 :=
 GoosePreG {goose_preG_iris :> invPreG \206\163;
            goose_preG_heap :>
             Count_Heap.gen_heapPreG (sigT Ptr) (sigT ptrRawModel) \206\163;
            goose_preG_fs :> fsPreG goose_model \206\163;
            goose_preG_global :> ghost_mapG (discreteO sliceLockC) \206\163;
            goose_preG_treg_inG :>
             inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))}.
Time -
Time auto.
Time Qed.
Time
Definition goose\206\163 (m : GoModel) {wf : GoModelWf m} : gFunctors :=
  #[ inv\206\163; fs\206\163 m; gen_typed_heap\206\163 Ptr ptrRawModel;
  ghost_map\206\163 (discreteO sliceLockC);
  GFunctor (csumR countingR (authR (optionUR (exclR unitO))))].
Time #[global]
Instance subG_goosePreG  (m : GoModel) {wf : GoModelWf m} 
 {\206\163}: (subG (goose\206\163 m) \206\163 \226\134\146 goosePreG m \206\163).
Time Proof.
Time solve_inG.
Time Section gen_heap.
Time Context `{hG : gen_heapG L V \206\163}.
Time
Lemma gen_heap_init_to_bigOp \207\131 :
  own (gen_heap_name hG) (\226\151\175 to_gen_heap \207\131) -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i 1 v.
Time #[global]
Instance CommitInner'_timeless  P \206\147 flag plog pcurr 
 psrc: (Timeless P \226\134\146 Timeless (CommitInner' P \206\147 flag plog pcurr psrc)).
Time Proof.
Time (intros).
Time (destruct flag as (c, ?)).
Time (destruct c; apply _).
Time Proof.
Time (induction \207\131 using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros "Hown".
Time Qed.
Time rewrite big_opM_insert //.
Time Module Type goose_refinement_type.
Time Context (OpT : Type \226\134\146 Type).
Time Context (\206\155a : Layer OpT).
Time Context (gm : GoModel).
Time Context (gmWf : GoModelWf gm).
Time Context (impl : LayerImplRel GoLayer.Op OpT).
Time Context (\206\163 : gFunctors).
Time Notation compile_rel_base := (compile_rel_base impl).
Time Notation compile_rel_proc_seq := (compile_rel_proc_seq impl).
Time Notation compile_rel := (compile_rel impl).
Time Notation recover := (recover_rel impl).
Time Notation compile_proc_seq := (compile_proc_seq impl).
Time Context `{CFG : cfgPreG OpT \206\155a \206\163} `{HEX : @goosePreG gm gmWf \206\163}.
Time Context `{INV : Adequacy.invPreG \206\163}.
Time
Context `{REG : inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))}.
Time
Context
 (crash_inner : forall {_ : @cfgG OpT \206\155a \206\163} {_ : gooseG gm \206\163}, iProp \206\163).
Time
Context (exec_inner : forall {_ : @cfgG OpT \206\155a \206\163} {_ : gooseG gm \206\163}, iProp \206\163).
Time
Context (crash_param : forall (_ : @cfgG OpT \206\155a \206\163) (_ : gooseG gm \206\163), Type).
Time
Context
 (crash_inv : forall {H1 : @cfgG OpT \206\155a \206\163} {H2 : gooseG gm \206\163},
              @crash_param _ H2 \226\134\146 iProp \206\163).
Time
Context
 (crash_starter : forall {H1 : @cfgG OpT \206\155a \206\163} {H2 : gooseG gm \206\163},
                  @crash_param _ H2 \226\134\146 iProp \206\163).
Time
Context (exec_inv : forall {_ : @cfgG OpT \206\155a \206\163} {_ : gooseG gm \206\163}, iProp \206\163).
Time Context (E : coPset).
Time Context (recv : proc GoLayer.Op unit).
Time Context (init_absr : \206\155a.(OpState) \226\134\146 State \226\134\146 Prop).
Time End goose_refinement_type.
Time Module goose_refinement_definitions (eRT: goose_refinement_type).
Time Import eRT.
Time Existing Instances gm, gmWf.
Time
Definition recv_triple_type :=
  forall H1 H2 param,
  @crash_inv H1 H2 param \226\136\151 Registered \226\136\151 @crash_starter H1 H2 param
  \226\138\162 WP recv
    @ NotStuck; \226\138\164 {{ v, |={\226\138\164,E}=> \226\136\131 \207\1312a \207\1312a',
                                    source_state \207\1312a
                                    \226\136\151 \226\140\156Proc.crash_step \206\155a \207\1312a (Val \207\1312a' tt)\226\140\157
                                      \226\136\151 (\226\136\128 `{Hcfg' : cfgG OpT \206\155a \206\163} 
                                           (Hinv' : 
                                            invG \206\163) 
                                           tr',
                                           source_ctx \226\136\151 source_state \207\1312a'
                                           ={\226\138\164}=\226\136\151 
                                           exec_inner Hcfg'
                                             (GooseG _ _ \206\163 Hinv' go_heap_inG
                                                go_fs_inG go_global_inG tr')) }}.
Time
Definition refinement_base_triples_type :=
  forall H1 H2 T1 T2 j K `{LanguageCtx OpT T1 T2 \206\155a K} (p : proc OpT T1) p',
  compile_rel_base p p'
  \226\134\146 j \226\164\135 K p \226\136\151 Registered \226\136\151 @exec_inv H1 H2
    \226\138\162 WP p' {{ v, j \226\164\135 K (Ret v) \226\136\151 Registered }}.
Time
Definition init_wf_type :=
  \226\136\128 \207\1311a \207\1311c,
    init_absr \207\1311a \207\1311c
    \226\134\146 dom (gset string) \207\1311c.(fs).(dirents) =
      dom (gset string) \207\1311c.(fs).(dirlocks)
      \226\136\167 (\226\136\128 s l, \207\1311c.(fs).(dirlocks) !! s = Some l \226\134\146 fst l = Unlocked)
        \226\136\167 \207\1311c.(maillocks) = None.
Time
Definition crash_fsG {\206\163} (curr : @fsG _ _ \206\163) newDirLocks 
  newFds : @fsG _ _ \206\163 :=
  FsG _ _ _ newDirLocks go_fs_dirs_inG go_fs_paths_inG go_fs_inodes_inG
    newFds go_fs_domalg_inG go_fs_dom_name.
Time
Definition init_exec_inner_type :=
  \226\136\128 \207\1311a \207\1311c,
    init_absr \207\1311a \207\1311c
    \226\134\146 \226\136\128 (Hex : @gooseG gm gmWf \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
        ([\226\136\151 map] d\226\134\166ents \226\136\136 \207\1311c.(fs).(dirents), d \226\134\166 dom (gset string) ents)
        \226\136\151 rootdir \226\134\166{ - 1} dom (gset string) \207\1311c.(fs).(dirents)
          \226\136\151 ([\226\136\151 set] dir \226\136\136 dom (gset string) \207\1311c.(fs).(dirents), 
             dir \226\134\166 Unlocked) \226\136\151 source_ctx \226\136\151 source_state \207\1311a \226\136\151 global \226\134\166 None
        ={\226\138\164}=\226\136\151 exec_inner _ _.
Time
Definition exec_inv_preserve_crash_type :=
  \226\136\128 (Hex : @gooseG gm gmWf \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    exec_inv Hcfg Hex
    ={\226\138\164,E}=\226\136\151 \226\136\128 Hmem' Hdlocks' Hfds' Hreg' Hglobal',
               let Hex :=
                 GooseG _ _ \206\163 go_invG Hmem' (crash_fsG _ Hdlocks' Hfds')
                   Hreg' Hglobal' in
               (\226\136\131 S, rootdir \226\134\166{ - 1} S \226\136\151 ([\226\136\151 set] dir \226\136\136 S, dir \226\134\166 Unlocked))
               \226\136\151 global \226\134\166 None ={E}=\226\136\151 crash_inner Hcfg Hex.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap m) \226\136\151 mapsto i 1 x)%I with
 "[Hown]" as "[Hrest $]".
Time
Definition crash_inv_preserve_crash_type :=
  \226\136\128 (Hex : @gooseG gm gmWf \206\163) `(Hcfg : cfgG OpT \206\155a \206\163) param,
    crash_inv Hcfg Hex param
    ={\226\138\164,E}=\226\136\151 \226\136\128 Hmem' Hdlocks' Hfds' Hreg' Hglobal',
               let Hex :=
                 GooseG _ _ \206\163 go_invG Hmem' (crash_fsG _ Hdlocks' Hfds')
                   Hreg' Hglobal' in
               (\226\136\131 S, rootdir \226\134\166{ - 1} S \226\136\151 ([\226\136\151 set] dir \226\136\136 S, dir \226\134\166 Unlocked))
               \226\136\151 global \226\134\166 None ={E}=\226\136\151 crash_inner Hcfg Hex.
Time
Definition crash_inner_inv_type :=
  \226\136\128 (Hex : @gooseG gm gmWf \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    (\226\136\131 Hinv,
       crash_inner Hcfg
         (GooseG _ _ \206\163 Hinv go_heap_inG go_fs_inG go_global_inG go_treg_inG))
    \226\136\151 source_ctx
    ={\226\138\164}=\226\136\151 \226\136\131 param, crash_inv Hcfg Hex param \226\136\151 crash_starter Hcfg Hex param.
Time
Definition exec_inner_inv_type :=
  \226\136\128 (Hex : @gooseG gm gmWf \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    (\226\136\131 Hinv,
       exec_inner Hcfg
         (GooseG _ _ \206\163 Hinv go_heap_inG go_fs_inG go_global_inG go_treg_inG))
    \226\136\151 source_ctx ={\226\138\164}=\226\136\151 exec_inv Hcfg Hex.
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
Definition exec_inv_preserve_finish_type :=
  (\226\136\128 (Hex : @gooseG gm gmWf \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
     AllDone
     -\226\136\151 exec_inv Hcfg Hex
        ={\226\138\164,E}=\226\136\151 \226\136\131 \207\1312a \207\1312a' : \206\155a.(OpState),
                   source_state \207\1312a
                   \226\136\151 \226\140\156\206\155a.(finish_step) \207\1312a (Val \207\1312a' tt)\226\140\157
                     \226\136\151 (\226\136\128 `{Hcfg' : cfgG OpT \206\155a \206\163} 
                          (Hinv' : invG \206\163) Hmem' Hdlocks' 
                          Hfds' Hreg' Hglobal',
                          let Hex :=
                            GooseG _ _ \206\163 Hinv' Hmem'
                              (crash_fsG _ Hdlocks' Hfds') Hreg' Hglobal' in
                          source_ctx
                          \226\136\151 source_state \207\1312a'
                            \226\136\151 (\226\136\131 S,
                                 rootdir \226\134\166{ - 1} S
                                 \226\136\151 ([\226\136\151 set] dir \226\136\136 S, dir \226\134\166 Unlocked))
                              \226\136\151 global \226\134\166 None ={\226\138\164}=\226\136\151 
                          exec_inner Hcfg' Hex))%I.
Time rewrite to_gen_heap_insert.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (insert_singleton_op (to_gen_heap m) i (1%Qp, to_agree x)) ; last  by
 apply lookup_to_gen_heap_None).
Time End goose_refinement_definitions.
Time Module Type goose_refinement_obligations (eRT: goose_refinement_type).
Time Module eRD:=  goose_refinement_definitions eRT.
Time rewrite auth_frag_op.
Time Import eRT.
Time Import eRD.
Time Context (recsingle : recover = rec_singleton eRT.recv).
Time Context (nameIncl : nclose sourceN \226\138\134 eRT.E).
Time
Context
 (einv_persist : forall {H1 : @cfgG OpT \206\155a eRT.\206\163} {H2},
                 Persistent (exec_inv H1 H2)).
Time iDestruct "Hown" as "(?&?)".
Time
Context
 (cinv_persist : forall {H1 : @cfgG OpT \206\155a \206\163} {H2} {P : crash_param _ _},
                 Persistent (crash_inv H1 H2 P)).
Time
Context (exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx).
Time Context (recv_triple : recv_triple_type).
Time Context (init_wf : init_wf_type).
Time Context (refinement_base_triples : refinement_base_triples_type).
Time Context (init_exec_inner : init_exec_inner_type).
Time Context (exec_inv_preserve_crash : exec_inv_preserve_crash_type).
Time Context (crash_inv_preserve_crash : crash_inv_preserve_crash_type).
Time Context (exec_inner_inv : exec_inner_inv_type).
Time Context (crash_inner_inv : crash_inner_inv_type).
Time Context (exec_inv_preserve_finish : exec_inv_preserve_finish_type).
Time End goose_refinement_obligations.
Time
Module goose_refinement (eRT: goose_refinement_type)
  (eRO: goose_refinement_obligations eRT).
Time Module eRD:=  goose_refinement_definitions eRT.
Time Module RT<: refinement_type.
Time Import eRT.
Time Definition OpC := GoLayer.Op.
Time Definition \206\155c := GoLayer.Go.l.
Time Definition OpT := OpT.
Time Definition \206\155a := \206\155a.
Time Definition impl := impl.
Time Definition exmachG := @gooseG gm gmWf.
Time Definition \206\163 := \206\163.
Time Definition CFG := CFG.
Time Definition INV := INV.
Time Definition REG := REG.
Time Definition Hinstance := @gooseG_irisG _ _.
Time iFrame.
Time Definition Hinstance_reg := @go_treg_inG _ _.
Time
Definition set_inv_reg Hex Hinv Hreg :=
  GooseG _ _ \206\163 Hinv (@go_heap_inG _ _ _ Hex) (@go_fs_inG _ _ _ Hex)
    (@go_global_inG _ _ _ Hex) Hreg.
Time Definition crash_inner := crash_inner.
Time Definition exec_inner := exec_inner.
Time Definition crash_inv := crash_inv.
Time Definition crash_param := crash_param.
Time Definition crash_starter := crash_starter.
Time Definition exec_inv := exec_inv.
Time Definition E := E.
Time Definition recv := recv.
Time Definition init_absr := init_absr.
Time End RT.
Time Module RD:=  refinement_definitions RT.
Time Import RT RD.
Time Module RO: refinement_obligations RT.
Time Module RD:=  RD.
Time Import WeakestPre.
Time }
Time by iApply IH\207\131.
Time Import RT RD.
Time Definition nameIncl := eRO.nameIncl.
Time Definition einv_persist := eRO.einv_persist.
Time Definition cinv_persist := eRO.cinv_persist.
Time Existing Instances einv_persist, cinv_persist.
Time Definition recsingle := eRO.recsingle.
Time Definition refinement_base_triples := eRO.refinement_base_triples.
Time Definition exec_inv_source_ctx := eRO.exec_inv_source_ctx.
Time
Lemma set_inv_reg_spec0 :
  \226\136\128 Hex,
    set_inv_reg Hex (Hinstance \206\163 Hex).(@iris_invG OpC (Layer.State \206\155c) \206\163)
      (Hinstance_reg \206\163 Hex) = Hex.
Time Proof.
Time (destruct Hex; auto).
Time Qed.
Time
Lemma set_inv_reg_spec1 :
  \226\136\128 Hex Hinv Hreg,
    @iris_invG _ _ _ (Hinstance _ (set_inv_reg Hex Hinv Hreg)) = Hinv.
Time Proof.
Time trivial.
Time Qed.
Time
Lemma set_inv_reg_spec2 :
  \226\136\128 Hex Hinv Hreg, Hinstance_reg _ (set_inv_reg Hex Hinv Hreg) = Hreg.
Time Qed.
Time Proof.
Time trivial.
Time Qed.
Time
Lemma set_inv_reg_spec3 :
  \226\136\128 Hex Hinv Hinv' Hreg Hreg',
    set_inv_reg (set_inv_reg Hex Hinv' Hreg') Hinv Hreg =
    set_inv_reg Hex Hinv Hreg.
Time Proof.
Time trivial.
Time Qed.
Time Existing Instance Hinstance.
Time
Lemma register_spec `{@gooseG eRT.gm _ \206\163} :
  \226\136\131 Interp : OpState \206\155c \226\134\146 iProp \206\163,
    (\226\136\128 n \207\131,
       @state_interp _ _ _ (Hinstance _ _) (n, \207\131)
       -\226\136\151 thread_count_interp n \226\136\151 Interp \207\131)
    \226\136\167 (\226\136\128 n \207\131, thread_count_interp n \226\136\151 Interp \207\131 -\226\136\151 state_interp (n, \207\131)).
Time Proof.
Time eexists.
Time (split; [ eapply Interp.thread_reg1 | eapply Interp.thread_reg2 ]).
Time Qed.
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time rewrite /recv_triple_type.
Time iIntros ( ? ? ? ) "(#Hinv&Hreg&Hstart)".
Time #[global]
Instance CommitInner_timeless  P \206\147: (Timeless P \226\134\146 Timeless (CommitInner P \206\147)).
Time Proof.
Time (intros).
Time (apply _).
Time iPoseProof @eRO.recv_triple as "H".
Time
Lemma gen_heap_bigOpM_dom (\207\131 : gmap L V) (q : Qp) :
  ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i q v)
  -\226\136\151 [\226\136\151 set] i \226\136\136 dom (gset L) \207\131, \226\136\131 v, \226\140\156\207\131 !! i = Some v\226\140\157 \226\136\151 mapsto i q v.
Time Qed.
Time Proof.
Time iIntros "H".
Time #[global]
Instance sep_into_sep_single_named  {PROP : bi} (i : string) 
 (P : PROP): (IntoSepEnv (named i P) [(LNamed i, P)]).
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iApply big_sepM_dom.
Time iFrame.
Time eauto.
Time iApply (big_sepM_mono with "H").
Time Qed.
Time #[global]
Instance sep_into_sep_cons  {PROP : bi} (i : string) 
 (P Q : PROP) Ps:
 (IntoSepEnv Q Ps \226\134\146 IntoSepEnv (named i P \226\136\151 Q) ((LNamed i, P) :: Ps)) |10.
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iIntros ( k x Hlookup ) "H".
Time iExists _.
Time iFrame.
Time iSpecialize ("H" with "[$]").
Time iIntros ( ? ) "(?&?)".
Time eauto.
Time Qed.
Time iFrame.
Time by iApply H1.
Time Qed.
Time #[global]
Instance sep_into_sep_anon_cons  {PROP : bi} (P Q : PROP) 
 Ps: (IntoSepEnv Q Ps \226\134\146 IntoSepEnv (P \226\136\151 Q) ((LAnon, P) :: Ps)) |50.
Time
Lemma gen_heap_bigOp_split (\207\131 : gmap L V) (q : Qp) :
  ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i q v)
  -\226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i (q / 2) v)
     \226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, mapsto i (q / 2) v).
Time Proof.
Time rewrite /IntoSepEnv //=.
Time Proof.
Time rewrite -big_sepM_sep.
Time iIntros ( ? ) "(?&?)".
Time iFrame.
Time by iApply H1.
Time iApply (wp_wand with "H").
Time Qed.
Time #[global]
Instance sep_into_sep_single_anon  {PROP : bi} (P : PROP):
 (IntoSepEnv P [(LAnon, P)]) |100.
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iFrame.
Time eauto.
Time (apply big_sepM_mono).
Time iIntros ( ? ? ? ) "($&$)".
Time Qed.
Time
Ltac
 log_step Hinv :=
  iInv Hinv as "H"; destruct_commit_inner "H"; iLDestruct "Hlog_inv";
   iLDestruct "Hmain_inv"; iLDestruct "Hcommit_inv"; 
   repeat unify_ghost; repeat unify_lease; wp_step;
   (iModIntro; handle_pairs recommit; iNamed iFrame; iFrame); iNamed iFrame.
Time
Lemma write_log_fst (m : iProp \206\163) {_ : Timeless m} 
  \206\147 flagsnd (plog1 : nat) x j i :
  {{{ inv liN (CommitInner m \206\147)
      \226\136\151 named i (lease log_fst plog1)
        \226\136\151 named j (own \206\147.(\206\179flag) (\226\151\175 Excl' (0, flagsnd))) }}} 
  write_disk log_fst x {{{ RET tt; named i (lease log_fst x)
                                   \226\136\151 named j
                                       (own \206\147.(\206\179flag) (\226\151\175 Excl' (0, flagsnd)))}}}.
Time Qed.
Time End gen_heap.
Time Proof.
Time iIntros ( \206\166 ).
Time (iIntros "(Hinv&Hlog&Hflag) H\206\166"; iAssignNames).
Time iIntros ( _ ) "H".
Time iMod "H" as ( \207\1312a \207\1312a' ) "(?&%&H)".
Time
Definition gen_heap_ctx' {\206\163} {V} {hG : gen_heapG nat V \206\163} :=
  (\226\136\131 \207\131 : gmap nat V, \226\140\156dom (gset nat) \207\131 = addrset\226\140\157 \226\136\151 gen_heap_ctx \207\131)%I.
Time
Lemma gen_heap_update' {\206\163} {V} {hG : gen_heapG nat V \206\163} 
  (l : nat) v1 v2 :
  gen_heap_ctx' -\226\136\151 mapsto l 1 v1 ==\226\136\151 gen_heap_ctx' \226\136\151 mapsto l 1 v2.
Time (log_step "Hinv").
Time Proof.
Time iIntros "Hctx Hmapsto".
Time iDestruct "Hctx" as ( \207\131 Hdom ) "H".
Time iDestruct (@gen_heap_valid with "[$] [$]") as % Hlookup.
Time iModIntro.
Time iExists _ , _.
Time iFrame.
Time iMod (@gen_heap_update with "[$] [$]") as "(?&$)".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR ; first  by iPureIntro).
Time iIntros.
Time rewrite /post_recv.
Time iIntros ( ? ? ? ? ) "((_&Hstate)&Hthread)".
Time iModIntro.
Time iExists _.
Time (iExists _; iFrame).
Time iFrame.
Time iPureIntro.
Time rewrite dom_insert_L -Hdom.
Time (cut (l \226\136\136 dom (gset nat) \207\131)).
Time {
Time set_solver +.
Time iIntros.
Time }
Time (apply elem_of_dom).
Time eauto.
Time Qed.
Time iModIntro.
Time by iMod ("H" with "[$]").
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
Time Qed.
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
Time Existing Instance eRT.HEX.
Time Lemma init_exec_inner : init_exec_inner_type.
Time Proof.
Time rewrite /init_exec_inner_type.
Time iIntros ( \207\1311a \207\1311c Hinit ? ? ? ).
Time
iMod (gen_typed_heap_strong_init \207\1311c.(fs).(heap).(allocs)) as ( hM Hmpf_eq )
 "(Hmc&Hm)".
Time wp_bind.
Time iDestruct "Hlockinv" as ( v' ) "(Hl0&Hl1&Hstatus)".
Time iInv "Hinv" as "H".
Time
iMod (gen_heap_strong_init (fmap (dom (gset string)) \207\1311c.(fs).(dirents))) as
 ( hD Hdpf_eq ) "(Hdc&Hd)".
Time
iMod (gen_heap_strong_init \207\1311c.(fs).(fds)) as ( hFDs HFDpf_eq ) "(Hfdc&Hfd)".
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time
iMod (gen_heap_strong_init \207\1311c.(fs).(inodes)) as ( hIs HIpf_eq ) "(Hidc&Hi)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time
iMod (gen_dir_strong_init \207\1311c.(fs).(dirents)) as ( hP HPpf_eq ) "(Hpc&Hp)".
Time rewrite elem_of_dom in  {} Hdom2 *.
Time (intros [v1 Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time
iMod (Count_Heap.gen_heap_strong_init (\206\187 s, \207\1311c.(fs).(dirlocks) !! s)) as (
 hL HLpf_eq ) "(Hlc&Hl)".
Time iDestruct "Hcurr" as ( v0 stat ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time
iMod
 (ghost_var_alloc (A:=discreteO (gset string))
    (dom (gset string) \207\1311c.(fs).(dirents))) as ( hGD ) "(HgdA&Hgd)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time by iApply "H\206\166"; iFrame.
Time Qed.
Time replace 0%Z with O : Z by auto.
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time
iPoseProof
 (Count_Ghost.read_split (A:=discreteO (gset string)) hGD with "Hgd") as
 "(Hgd&Hgdr)".
Time (iDestruct "Hstat" as % Heq; subst).
Time iApply (wp_write_disk0 with "[$]").
Time
iMod (ghost_var_alloc (A:=discreteO sliceLockC) \207\1311c.(maillocks)) as ( hGL )
 "(HglA&Hgl)".
Time (set (hFG := FsG _ _ \206\163 hL hD hP hIs hFDs _ hGD)).
Time (set (hGl := GlobalG _ _ _ _ hGL)).
Time (set (hG := GooseG _ _ \206\163 _ hM hFG hGl _)).
Time iPoseProof (eRO.init_exec_inner \207\1311a \207\1311c Hinit hG _) as "H".
Time
Lemma write_log_snd (m : iProp \206\163) {H' : Timeless m} 
  \206\147 flagsnd (plog2 : nat) x j i :
  {{{ inv liN (CommitInner m \206\147)
      \226\136\151 named i (lease log_snd plog2)
        \226\136\151 named j (own \206\147.(\206\179flag) (\226\151\175 Excl' (0, flagsnd))) }}} 
  write_disk log_snd x {{{ RET tt; named i (lease log_snd x)
                                   \226\136\151 named j
                                       (own \206\147.(\206\179flag) (\226\151\175 Excl' (0, flagsnd)))}}}.
Time iExists hG.
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog&Hflag) H\206\166"; iAssignNames).
Time iModIntro.
Time iIntros "(Hsource1&Hsource2&Hthread)".
Time (log_step "Hinv").
Time iFrame.
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
Time iMod ("H" with "[-Hgd]") as "Hinner".
Time {
Time iFrame.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth Hj Hreg".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time (edestruct eRO.init_wf as (?, (?, ->)); eauto).
Time iFrame.
Time iSplitL "Hd".
Time *
Time iPoseProof (@gen_heap_init_to_bigOp _ _ _ _ _ hD with "[Hd]") as "?".
Time iFrame.
Time {
Time by rewrite Hdpf_eq.
Time clear.
Time iClear "Hlocks".
Time auto.
Time }
Time by rewrite big_opM_fmap.
Time }
Time iModIntro.
Time wp_bind.
Time iInv "Hinv" as "H".
Time *
Time
iPoseProof
 (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ hL _ _ \207\1311c.(fs).(dirlocks)
 with "[Hl]") as "Hl".
Time {
Time (intros s x).
Time (eapply eRO.init_wf; eauto).
Time }
Time {
Time by rewrite HLpf_eq.
Time clear \207\131 Hdom1 Hlookup Heq.
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time }
Time (edestruct eRO.init_wf as (->, (_, _)); eauto).
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time by iApply "H\206\166"; iFrame.
Time (intros [v1' Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_insert_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time Qed.
Time iDestruct "Hcurr" as ( ? ? ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time iApply big_sepM_dom.
Time iApply (big_sepM_mono with "Hl").
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (intros ? (?, []); eauto).
Time }
Time iFrame.
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time iModIntro.
Time iSplitL "Hgd".
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time -
Time iExists _.
Time iFrame.
Time -
Time (edestruct eRO.init_wf as (?, ?); eauto).
Time Qed.
Time iApply (wp_write_disk1 with "[$]").
Time
Lemma write_main_fst (m : iProp \206\163) {H' : Timeless m} 
  \206\147 base flagsnd (pcurr1 : nat) x i j :
  {{{ inv liN (CommitInner m \206\147)
      \226\136\151 named i (lease main_fst pcurr1)
        \226\136\151 named j (own \206\147.(\206\179flag) (\226\151\175 Excl' (S base, flagsnd))) }}} 
  write_disk main_fst x {{{ RET tt; named i (lease main_fst x)
                                    \226\136\151 named j
                                        (own \206\147.(\206\179flag)
                                           (\226\151\175 Excl' (S base, flagsnd)))}}}.
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog&Hflag) H\206\166"; iAssignNames).
Time (log_step "Hinv").
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
Time by iApply "H\206\166"; iFrame.
Time Qed.
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
Time
Lemma write_main_snd (m : iProp \206\163) {H' : Timeless m} 
  \206\147 base flagsnd (pcurr2 : nat) x i j :
  {{{ inv liN (CommitInner m \206\147)
      \226\136\151 named i (lease main_snd pcurr2)
        \226\136\151 named j (own \206\147.(\206\179flag) (\226\151\175 Excl' (S base, flagsnd))) }}} 
  write_disk main_snd x {{{ RET tt; named i (lease main_snd x)
                                    \226\136\151 named j
                                        (own \206\147.(\206\179flag)
                                           (\226\151\175 Excl' (S base, flagsnd)))}}}.
Time Proof.
Time iFrame.
Time (iIntros ( \206\166 ) "(Hinv&Hlog&Hflag) H\206\166"; iAssignNames).
Time (log_step "Hinv").
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
Time by iApply "H\206\166"; iFrame.
Time Qed.
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
Time
Lemma read_main_fst (m : iProp \206\163) {H' : Timeless m} 
  \206\147 pcurr i :
  {{{ inv liN (CommitInner m \206\147) \226\136\151 named i (lease main_fst pcurr) }}} 
  read_disk main_fst {{{ RET pcurr; named i (lease main_fst pcurr)}}}.
Time iIntros "!> (Hlocked&Hlockinv)".
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog) H\206\166"; iAssignNames).
Time (log_step "Hinv").
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
Time by iApply "H\206\166"; iFrame.
Time iIntros ( mv ) "!> (Hd0&Hret)".
Time Qed.
Time (destruct mv as [v| ]).
Time -
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time
Lemma read_main_snd (m : iProp \206\163) {H' : Timeless m} 
  \206\147 pcurr i :
  {{{ inv liN (CommitInner m \206\147) \226\136\151 named i (lease main_snd pcurr) }}} 
  read_disk main_snd {{{ RET pcurr; named i (lease main_snd pcurr)}}}.
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog) H\206\166"; iAssignNames).
Time (log_step "Hinv").
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
Time by iApply "H\206\166"; iFrame.
Time Qed.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time
Lemma set_commit {T} (m : iProp \206\163) {H' : Timeless m} 
  \206\147 flagsnd (pcurr' : nat * nat) icommit ifst isnd 
  i j x K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} 
  p :
  {{{ inv liN (CommitInner m \206\147)
      \226\136\151 m
        \226\136\151 j \226\164\135 K (Call (AtomicPair.Write p))
          \226\136\151 named icommit (lease log_commit x)
            \226\136\151 named ifst (lease log_fst (fst p))
              \226\136\151 named isnd (lease log_snd (snd p))
                \226\136\151 named i (own \206\147.(\206\179flag) (\226\151\175 Excl' (0, flagsnd))) }}} 
  write_disk log_commit 1 {{{ RET tt; named icommit (lease log_commit 1)
                                      \226\136\151 named ifst (lease log_fst (fst p))
                                        \226\136\151 named isnd (lease log_snd (snd p))
                                          \226\136\151 named i
                                              (own 
                                                 \206\147.(\206\179flag)
                                                 (\226\151\175 
                                                 Excl'
                                                 (1,
                                                 (j,
                                                 existT _
                                                 (K
                                                 (Call (AtomicPair.Write p))))
                                                  : 
                                                 prodO natO
                                                 (procTC AtomicPair.Op))))}}}.
Time Proof.
Time
(iIntros ( \206\166 ) "(Hinv&Hm&Hj&Hcommit_lease&Hlog1&Hlog2&Hflag) H\206\166";
  iAssignNames).
Time iInv "Hinv" as "H".
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time
(destruct_commit_inner "H"; iLDestruct "Hlog_inv"; iLDestruct "Hcommit_inv").
Time }
Time iModIntro.
Time wp_ret.
Time wp_bind.
Time iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
Time (repeat unify_ghost).
Time {
Time iFrame "Hlock".
Time (destruct p; simpl).
Time (repeat unify_lease).
Time iFrame.
Time
iMod
 (ghost_var_update (\206\179flag \206\147)
    (1,
    (j, existT _ (K (Call (AtomicPair.Write _))))
      : prodO natO (procTC AtomicPair.Op)) with "Hflag_auth [$]") as
 "(Hflag_auth&Hflag_ghost)".
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
Time wp_step.
Time recommit.
Time iModIntro.
Time iNamed iFrame.
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
Time iFrame.
Time }
Time iModIntro.
Time wp_bind.
Time iInv "Hinv" as "H".
Time clear \207\131 Hdom1 Hlookup Heq.
Time iDestruct "H" as ( \207\131 ) "(>Hdom1&>Hstate&Hctx_stat&>Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time (<ssreflect_plugin::ssrtclintros@0> generalize Hlt =>Hdom2).
Time iSplitL "Hm Hj".
Time rewrite -Hdom1 in  {} Hdom2.
Time rewrite elem_of_dom in  {} Hdom2 *.
Time {
Time iNext.
Time iIntros.
Time (simpl).
Time rewrite /CommitOn.
Time rewrite someone_writing_unfold.
Time iExists K , _.
Time iFrame.
Time (intros [v1 Hlookup]).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (big_sepM_lookup_acc with "Hdur")
 as "(Hcurr&Hdur)" ; first  eauto).
Time (simpl).
Time (destruct_pairs; auto).
Time }
Time iApply "H\206\166".
Time iFrame.
Time iDestruct "Hcurr" as ( ? ? ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time Qed.
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time (iDestruct "Hstat" as % Heq; subst).
Time iApply (wp_read_disk1_only1 with "[$]").
Time iIntros "!> Hd1".
Time iMod (ghost_step_call with "Hj Hsrc [$]") as "(Hj&Hstate&_)".
Time
Lemma unset_commit {T} (m : iProp \206\163) {H' : Timeless m} 
  \206\147 base (p p' : nat * nat) i1 icommit ifst isnd j 
  x isrc K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} :
  {{{ source_ctx
      \226\136\151 inv liN (CommitInner m \206\147)
        \226\136\151 named i1
            (own \206\147.(\206\179flag)
               (\226\151\175 (Excl'
                     (S base, (j, existT _ (K (Call (AtomicPair.Write p)))))
                     : optionUR
                         (exclR
                            (prodO natO (prodO natO (procTC AtomicPair.Op)))))))
          \226\136\151 named icommit (lease log_commit x)
            \226\136\151 named ifst (lease main_fst (fst p))
              \226\136\151 named isnd (lease main_snd (snd p))
                \226\136\151 named isrc (own \206\147.(\206\179src) (\226\151\175 Excl' p')) }}} 
  write_disk log_commit 0 {{{ RET tt; named i1
                                        (own \206\147.(\206\179flag)
                                           (\226\151\175 Excl'
                                                (0,
                                                (0, existT _ (Ret tt))
                                                  : 
                                                prodO natO
                                                 (procTC AtomicPair.Op))))
                                      \226\136\151 named icommit (lease log_commit 0)
                                        \226\136\151 named ifst (lease main_fst (fst p))
                                          \226\136\151 named isnd
                                              (lease main_snd (snd p))
                                            \226\136\151 named isrc
                                                (own \206\147.(\206\179src) (\226\151\175 Excl' p))
                                              \226\136\151 m \226\136\151 j \226\164\135 K (Ret tt)}}}.
Time Proof.
Time
(iIntros ( \206\166 )
  "(Hsource_inv&Hinv&Hflag&Hcommit_flag&Hmain1&Hmain2&Hsrc_ghost) H\206\166";
  iAssignNames).
Time iInv "Hinv" as "H".
Time
(destruct_commit_inner "H"; iLDestruct "Hmain_inv"; iLDestruct "Hcommit_inv";
  iLDestruct "Hsrc_inv").
Time {
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (split; auto).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time (destruct p as (p1, p2)).
Time (repeat unify_ghost).
Time }
Time iExists _.
Time iFrame.
Time destruct_pairs.
Time (repeat unify_lease).
Time (simpl).
Time rewrite /CommitOn.
Time rewrite someone_writing_unfold.
Time iDestruct "Hsomewriter" as ( ? K' ) "(Hreg&%&Hj)".
Time (simpl).
Time wp_step.
Time iSplitL "Hdur Hd0 Hd1 Hstatus_auth".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time iFrame.
Time iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
Time iFrame.
Time clear.
Time iClear "Hlocks".
Time auto.
Time {
Time (intros).
Time eexists.
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  by eauto).
Time }
Time iModIntro.
Time wp_ret.
Time wp_bind.
Time (econstructor; eauto).
Time iApply (wp_unlock with "[Hl0 Hl1 Hstatus Hlocked]").
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time {
Time iFrame "Hlock".
Time }
Time
iMod (ghost_var_update (\206\179src \206\147) (p1, p2) with "Hsrc_auth Hsrc_ghost") as
 "(Hsrc_auth&Hsrc_ghost)".
Time
iMod
 (ghost_var_update (\206\179flag \206\147) (0, (0, existT _ (Ret tt) : procTC _))
 with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
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
Time iModIntro.
Time handle_pairs recommit; iNamed iFrame.
Time iNamed iFrame.
Time #[global]
Instance DisksInv_Timeless  (P : iProp \206\163) {HT : Timeless P}:
 (Timeless (DisksInv P)).
Time iSplitL "".
Time {
Time iNext.
Time rewrite /CommitOff.
Time auto.
Time }
Time iApply "H\206\166".
Time Proof.
Time (apply _).
Time iFrame.
Time Qed.
Time End refinement_triples.
Time Qed.
Time
Lemma goose_interp_split_read_dir `{gooseG \206\163} \207\1312c :
  (goose_interp \207\1312c
   -\226\136\151 goose_interp \207\1312c
      \226\136\151 rootdir \226\134\166{ - 1} dom (gset string) \207\1312c.(fs).(dirents)
        \226\136\151 \226\140\156dom (gset string) \207\1312c.(fs).(dirents) =
           dom (gset string) \207\1312c.(fs).(dirlocks)\226\140\157)%I.
Time Proof.
Time clear.
Time iIntros "(?&(?&?&?&?&?&Hroot&%)&?)".
Time
Lemma unset_commit' {T} (m : iProp \206\163) {H' : Timeless m} 
  \206\147 base (p p' : nat * nat) i1 icommit ifst isnd ifst' 
  isnd' x isrc thd `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} :
  {{{ source_ctx
      \226\136\151 inv liN (CommitInner m \206\147)
        \226\136\151 named i1
            (own \206\147.(\206\179flag)
               (\226\151\175 (Excl' (S base, thd)
                     : optionUR
                         (exclR
                            (prodO natO (prodO natO (procTC AtomicPair.Op)))))))
          \226\136\151 named icommit (lease log_commit x)
            \226\136\151 named ifst (lease main_fst (fst p))
              \226\136\151 named isnd (lease main_snd (snd p))
                \226\136\151 named ifst' (lease log_fst (fst p))
                  \226\136\151 named isnd' (lease log_snd (snd p))
                    \226\136\151 named isrc (own \206\147.(\206\179src) (\226\151\175 Excl' p')) }}} 
  write_disk log_commit 0 {{{ RET tt; named i1
                                        (own \206\147.(\206\179flag)
                                           (\226\151\175 Excl'
                                                (0,
                                                (0, existT _ (Ret tt))
                                                  : 
                                                prodO natO
                                                 (procTC AtomicPair.Op))))
                                      \226\136\151 named icommit (lease log_commit 0)
                                        \226\136\151 named ifst (lease main_fst (fst p))
                                          \226\136\151 named isnd
                                              (lease main_snd (snd p))
                                            \226\136\151 named ifst'
                                                (lease log_fst (fst p))
                                              \226\136\151 named isnd'
                                                 (lease log_snd (snd p))
                                                \226\136\151 
                                                named isrc
                                                 (own \206\147.(\206\179src) (\226\151\175 Excl' p))
                                                \226\136\151 m}}}.
Time iDestruct "Hroot" as ( n ) "Hmapsto".
Time iFrame.
Time Proof.
Time
(iIntros ( \206\166 )
  "(Hsource_inv&Hinv&Hflag&Hcommit_flag&Hmain1&Hmain2&Hlog1&Hlog2&Hsrc_ghost) H\206\166";
  iAssignNames).
Time iInv "Hinv" as "H".
Time
(destruct_commit_inner "H"; iLDestruct "Hmain_inv"; iLDestruct "Hcommit_inv";
  iLDestruct "Hlog_inv"; iLDestruct "Hsrc_inv").
Time iFrame "%".
Time (destruct p as (p1, p2)).
Time (simpl).
Time destruct_pairs.
Time (repeat unify_ghost).
Time rewrite Count_Ghost.read_split.
Time iDestruct "Hmapsto" as "(?&?)".
Time Lemma init_zero_lookup_is_zero k x : init_zero !! k = Some x \226\134\146 x = 0.
Time Proof.
Time (destruct (lt_dec k size)).
Time -
Time (rewrite init_zero_lookup_lt_zero; congruence).
Time -
Time (rewrite init_zero_lookup_ge_None; congruence).
Time iFrame.
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
Time iExists (S n).
Time eauto.
Time Qed.
Time Instance CFG : (@cfgPreG OneDisk.Op OneDisk.l \206\163).
Time (apply _).
Time Qed.
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
Time (repeat unify_lease).
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time rewrite /exec_inv_preserve_crash_type.
Time iIntros ( ? ? ) "Hinv".
Time iPoseProof (eRO.exec_inv_preserve_crash with "Hinv") as "Hinv_post".
Time iMod "Hinv_post" as "Hinv_post".
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
Time iModIntro.
Time iIntros ( ? n \207\131 ) "((?&Hmach)&Hthread)".
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
Time iMod (gen_typed_heap_strong_init \226\136\133) as ( hM' Hmpf_eq' ) "(Hmc&Hm)".
Time
iMod (gen_heap_strong_init (\226\136\133 : gmap File (Inode * OpenMode))) as ( hFds'
 Hfds'_eq' ) "(Hfdsc&Hfd)".
Time eauto.
Time
iMod
 (Count_Heap.gen_heap_strong_init
    (\206\187 s,
       ((\206\187 _ : LockStatus * (), (Unlocked, ())) <$> \207\131.(fs).(dirlocks)) !! s))
 as ( hDlocks' Hdlocks'_eq' ) "(Hdlocksc&Hlocks)".
Time (simpl).
Time rewrite /CommitOn.
Time
iMod (ghost_var_alloc (A:=discreteO sliceLockC) None) as ( hGl_name )
 "(HglA&Hgl)".
Time rewrite someone_writing_unfold.
Time -
Time iApply (@write_refinement with "[$]").
Time iDestruct "Hsomewriter" as ( ? K' ) "(Hreg&%&Hj)".
Time (set (hGl := GlobalG _ _ _ _ hGl_name)).
Time (simpl).
Time wp_step.
Time eauto.
Time
iPoseProof (goose_interp_split_read_dir with "Hmach") as
 "(Hmach&Hroot&Hdom_eq)".
Time iMod ("Hinv_post" with "[Hm Hgl Hlocks Hroot Hdom_eq]") as "Hinv'".
Time {
Time iFrame.
Time Qed.
Time Lemma exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx.
Time iExists _.
Time iFrame.
Time
(iPoseProof
  (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ _ _ _ _ with "[Hlocks]") as
  "Hl"; swap 1 2).
Time Proof.
Time (red).
Time (intros).
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&?)".
Time {
Time rewrite Hdlocks'_eq'.
Time eauto.
Time }
Time {
Time (intros s x).
Time eauto.
Time rewrite lookup_fmap.
Time by intros (?, (?, ->))%fmap_Some_1.
Time }
Time iDestruct "Hdom_eq" as % ->.
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time (intros ? ? hS).
Time iIntros "(H&Hreg&Hstarter)".
Time iApply big_sepM_dom.
Time iDestruct "H" as "(#Hctx&#Hinv)".
Time rewrite big_sepM_fmap.
Time rewrite /recv.
Time
iAssert
 ([\226\136\151 set] a \226\136\136 addrset, if lt_dec a size then a m\226\134\166 0 \226\136\151 @UnlockedInv _ _ hS a
                       else a m\226\134\166 0 \226\136\151 @LockInv _ _ hS a)%I with "[Hstarter]"
 as "Hprogress".
Time (destruct thd).
Time (simpl).
Time (inversion H4).
Time {
Time iApply (big_sepS_mono with "Hstarter").
Time rewrite H6.
Time iIntros ( a Hin ) "Hunlocked".
Time (<ssreflect_plugin::ssrtclseq@0> destruct lt_dec ; first  iFrame).
Time exfalso.
Time (eapply not_lt_size_not_in_addrset; eauto).
Time }
Time rewrite /ReplicatedDiskImpl.recv.
Time iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
Time (assert (Hbound : size <= size) by lia).
Time (remember size as n eqn:Heqn ).
Time rewrite {+2}Heqn in  {} Hbound.
Time clear Heqn.
Time iInduction n as [| n] "IH".
Time -
Time wp_ret.
Time iInv "Hinv" as ">H" "_".
Time eauto.
Time {
Time (intros).
Time eexists.
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  by eauto).
Time (econstructor; eauto).
Time }
Time iModIntro.
Time iIntros ( \207\131' Hcrash ).
Time
iExists
 (GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
    (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl _).
Time (destruct Hcrash as ([], ((?, ?), (Hput, Hrest)))).
Time econstructor.
Time }
Time {
Time solve_ndisj.
Time }
Time
iMod (ghost_var_update (\206\179src \206\147) (p1, p2) with "Hsrc_auth Hsrc_ghost") as
 "(Hsrc_auth&Hsrc_ghost)".
Time iDestruct "H" as ( \207\131 ) "(Hdom1&Hstate&Hctx_stat&Hdur)".
Time iDestruct "Hdom1" as % Hdom1.
Time iApply fupd_mask_weaken.
Time {
Time solve_ndisj.
Time
iMod
 (ghost_var_update (\206\179flag \206\147) (0, (0, existT _ (Ret tt) : procTC _))
 with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
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
Time (inversion Hput).
Time }
Time iApply (big_sepM_mono with "H").
Time iIntros ( a v Hlookup ) "(Hd&(?&Hl))".
Time iDestruct "Hl" as ( v' ) "(Hl0&Hl1&Hstatus)".
Time iDestruct "Hd" as ( v0 stat ) "(Hd0&Hd1&Hstatus_auth&Hstat)".
Time subst.
Time inv_step.
Time (iDestruct (disk0_lease_agree with "Hd0 Hl0") as % Heq; subst).
Time (inversion Hrest; subst).
Time (iDestruct (disk1_lease_agree with "Hd1 Hl1") as % Heq; subst).
Time (iDestruct (mapsto_agree with "Hstatus Hstatus_auth") as % Heq; subst).
Time (simpl).
Time (repeat inv_step).
Time iFrame.
Time (inversion H).
Time deex.
Time inv_step.
Time iModIntro.
Time handle_pairs recommit; iNamed iFrame.
Time inv_step.
Time (inversion H).
Time deex.
Time inv_step.
Time iExists _.
Time iFrame.
Time }
Time iExists _ , _.
Time iFrame.
Time (unfold RecordSet.set in *).
Time (simpl).
Time (inversion H).
Time subst.
Time (simpl in *).
Time (repeat deex).
Time iSplitL "".
Time {
Time iPureIntro.
Time econstructor.
Time }
Time iClear "Hctx".
Time iIntros ( ? ? ? ) "(Hctx&Hstate)".
Time iDestruct (big_sepM_sep with "Hprogress") as "(Hdur&Hprogress)".
Time inv_step.
Time iDestruct (big_sepM_dom with "Hprogress") as "Hprogress".
Time rewrite Hdom1.
Time iModIntro.
Time iExists hS.
Time iFrame.
Time (eexists; shelve).
Time rewrite /CommitInner'.
Time iNamed iFrame.
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
Time subst.
Time iDestruct "Hmach" as "(?&(?&?&?&?&?&?)&?)".
Time (simpl).
Time (unfold RecordSet.set in *).
Time (simpl).
Time iFrame.
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
Time iNamed iFrame.
Time iApply (wp_read_disk0 with "[$]").
Time iIntros ( mv ) "!> (Hd0&Hret)".
Time (destruct mv as [v| ]).
Time *
Time iSplitL "Hstate Hctx_stat Hdur Hd0 Hd1 Hstatus_auth Hstat".
Time {
Time iExists _.
Time iFrame.
Time (simpl).
Time iFrame.
Time iSplitL "".
Time {
Time iNext.
Time rewrite /CommitOff.
Time auto.
Time }
Time iApply "H\206\166".
Time iFrame.
Time rewrite dom_fmap_L.
Time auto.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time iExists _ , _.
Time by iFrame.
Time iFrame.
Time eauto.
Time Qed.
Time Qed.
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
Time Ltac wp_step' := wp_step.
Time
Ltac
 wp_step :=
  try wp_bind;
   try
    match goal with
    | |- environments.envs_entails ?x ?igoal =>
          match igoal with
          | @wp _ _ _ _ _ _ _ (write_disk log_fst _) _ => iNamed
          iApply (write_log_fst with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (write_disk log_snd _) _ => iNamed
          iApply (write_log_snd with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (write_disk main_fst _) _ => iNamed
          iApply (write_main_fst with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (write_disk main_snd _) _ => iNamed
          iApply (write_main_snd with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (read_disk main_fst) _ => iNamed
          iApply (read_main_fst with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (read_disk main_snd) _ => iNamed
          iApply (read_main_snd with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ _ _ => wp_step'
          end
    end.
Time
Lemma write_refinement {T} j K
  `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} 
  p :
  {{{ j \226\164\135 K (Call (AtomicPair.Write p)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  write p {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 ) "(#Hsource_inv&#Hmain_lock&Hlog_lock&#Hinv)".
Time iDestruct "Hlog_lock" as ( \206\179lock_log ) "#Hlockinv".
Time iDestruct "Hmain_lock" as ( \206\179lock_main ) "#Hmlockinv".
Time (wp_lock "(Hlocked&HLL)").
Time
iDestruct "HLL" as ( plog ) "(Hflag_ghost&Hcommit_lease&Hlog_l1&Hlog_l2)".
Time (repeat wp_step).
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
Time
iNamed iApply (set_commit Registered _ _ p with "[$]"); iIntros "!>"; iLIntro.
Time *
Time iDestruct "Hstat" as "(Hj&Hreg')".
Time iMod (ghost_step_call with "Hj [$] [$]") as "(Hj&Hstate&_)".
Time (wp_lock "(Hlocked'&HML)").
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
Time iDestruct "HML" as ( pmain ) "(Hmain_lease1&Hmain_lease2&Hsrc_ghost)".
Time (repeat wp_step).
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
Time
iNamed
 iApply (unset_commit Registered _ _ p with "[$]"); iIntros "!>"; iLIntro.
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
Time (wp_unlock "[Hlog_l1 Hlog_l2 Hcommit_lease Hflag_ghost]").
Time {
Time (iExists _; iFrame).
Time }
Time (wp_unlock "[Hmain_lease1 Hmain_lease2 Hsrc_ghost]").
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iApply "Hdur".
Time {
Time (iExists _; iFrame).
Time iExists _ , _.
Time by iFrame.
Time }
Time iApply "H\206\166".
Time iFrame.
Time Qed.
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
Time
Lemma read_refinement {T} j K
  `{LanguageCtx AtomicPair.Op (nat * nat) T AtomicPair.l K} :
  {{{ j \226\164\135 K (Call AtomicPair.Read) \226\136\151 Registered \226\136\151 ExecInv }}} read {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time }
Time iDestruct "Hstatus" as "(Hstatus&Hstatus_auth)".
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 ) "(#Hsource_inv&#Hmain_lock&Hlog_lock&#Hinv)".
Time iModIntro.
Time iFrame.
Time iDestruct "Hlog_lock" as ( \206\179lock_log ) "#Hlockinv".
Time iDestruct "Hmain_lock" as ( \206\179lock_main ) "#Hmlockinv".
Time (wp_lock "(Hlocked'&HML)").
Time iDestruct "HML" as ( pmain ) "(Hmain1&Hmain2&Hsrc_ghost)".
Time wp_bind.
Time iInv "Hinv" as "H" "Hclose".
Time (destruct_commit_inner "H").
Time (iLDestruct "Hmain_inv"; iLDestruct "Hsrc_inv").
Time unify_ghost.
Time iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
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
Time
iMod ("Hclose" with "[-Hj H\206\166 Hlocked' Hreg Hmain1 Hmain2 Hsrc_ghost]") as "_".
Time {
Time recommit.
Time iNamed iFrame.
Time }
Time wp_step.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_intro_mask ; first  by
 set_solver +).
Time wp_step.
Time wp_bind.
Time (wp_unlock "[Hmain1 Hmain2 Hsrc_ghost]").
Time {
Time (iExists _; iFrame).
Time }
Time wp_ret.
Time (destruct pmain).
Time (simpl).
Time iApply "H\206\166".
Time iFrame.
Time Qed.
Time
Lemma init_mem_split :
  (([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i m\226\134\166 v) -\226\136\151 main_lock m\226\134\166 0 \226\136\151 log_lock m\226\134\166 0)%I.
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
Time iDestruct "Hmem" as "(?&?&_)".
Time iFrame.
Time Qed.
Time
Lemma init_disk_split :
  (([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i d\226\134\166 v \226\136\151 lease i v)
   -\226\136\151 (log_commit d\226\134\166 0
       \226\136\151 main_fst d\226\134\166 0 \226\136\151 main_snd d\226\134\166 0 \226\136\151 log_fst d\226\134\166 0 \226\136\151 log_snd d\226\134\166 0)
      \226\136\151 lease log_commit 0
        \226\136\151 lease main_fst 0
          \226\136\151 lease main_snd 0 \226\136\151 lease log_fst 0 \226\136\151 lease log_snd 0)%I.
Time Proof.
Time iIntros "Hdisk".
Time iPoseProof (disk_ptr_iter_split_aux O 4 with "Hdisk") as "H".
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
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time *
Time iExists _.
Time iFrame.
Time Proof.
Time rewrite /crash_inv_preserve_crash_type.
Time iIntros ( ? ? ? ) "Hinv".
Time iPoseProof (eRO.crash_inv_preserve_crash with "Hinv") as "Hinv_post".
Time iMod "Hinv_post" as "Hinv_post".
Time iModIntro.
Time iIntros ( ? n \207\131 ) "((?&Hmach)&Hthread)".
Time {
Time iMod (gen_typed_heap_strong_init \226\136\133) as ( hM' Hmpf_eq' ) "(Hmc&Hm)".
Time rewrite /size.
Time
iMod (gen_heap_strong_init (\226\136\133 : gmap File (Inode * OpenMode))) as ( hFds'
 Hfds'_eq' ) "(Hfdsc&Hfd)".
Time lia.
Time }
Time iDestruct "H" as "(H&_)".
Time
iMod
 (Count_Heap.gen_heap_strong_init
    (\206\187 s,
       ((\206\187 _ : LockStatus * (), (Unlocked, ())) <$> \207\131.(fs).(dirlocks)) !! s))
 as ( hDlocks' Hdlocks'_eq' ) "(Hdlocksc&Hlocks)".
Time (repeat iDestruct "H" as "((?&?)&H)").
Time
iMod (ghost_var_alloc (A:=discreteO sliceLockC) None) as ( hGl_name )
 "(HglA&Hgl)".
Time iFrame.
Time (set (hGl := GlobalG _ _ _ _ hGl_name)).
Time
iPoseProof (goose_interp_split_read_dir with "Hmach") as
 "(Hmach&Hroot&Hdom_eq)".
Time iMod ("Hinv_post" with "[Hm Hgl Hlocks Hroot Hdom_eq]") as "Hinv'".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by iPureIntro).
Time iSpecialize ("Hdur" $! v1).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_id ; last  auto).
Time iApply "Hdur".
Time {
Time iFrame.
Time iExists v1 , Sync.
Time iFrame.
Time iExists _.
Time iFrame.
Time
(iPoseProof
  (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ _ _ _ _ with "[Hlocks]") as
  "Hl"; swap 1 2).
Time {
Time rewrite Hdlocks'_eq'.
Time eauto.
Time }
Time {
Time (intros s x).
Time rewrite lookup_fmap.
Time by intros (?, (?, ->))%fmap_Some_1.
Time }
Time iDestruct "Hdom_eq" as % ->.
Time iApply big_sepM_dom.
Time rewrite big_sepM_fmap.
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
Time eauto.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_delete ; first  eauto).
Time iSplitR "Hrest".
Time {
Time (destruct lt_dec; try lia; [  ]).
Time }
Time iModIntro.
Time iIntros ( \207\131' Hcrash ).
Time
iExists
 (GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
    (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl _).
Time (destruct Hcrash as ([], ((?, ?), (Hput, Hrest)))).
Time (inversion Hput).
Time iFrame.
Time subst.
Time inv_step.
Time (inversion Hrest; subst).
Time (simpl).
Time (repeat inv_step).
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
Time (inversion H).
Time Qed.
Time deex.
Time inv_step.
Time {
Time lia.
Time inv_step.
Time (inversion H).
Time deex.
Time }
Time {
Time iDestruct "H" as "($&H)".
Time inv_step.
Time iDestruct "H" as ( ? ) "(?&?&?)".
Time iExists _ , _ , _.
Time iFrame.
Time }
Time }
Time Qed.
Time (unfold RecordSet.set in *).
Time End refinement_triples.
Time (simpl).
Time (inversion H).
Time subst.
Time (simpl in *).
Time (repeat deex).
Time inv_step.
Time subst.
Time iDestruct "Hmach" as "(?&(?&?&?&?&?&?)&?)".
Time (simpl).
Time (unfold RecordSet.set in *).
Time (simpl).
Time iFrame.
Time (simpl).
Time iFrame.
Time rewrite dom_fmap_L.
Time auto.
Time iFrame.
Time eauto.
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
Time Module lRT<: exmach_refinement_type.
Time Ltac wp_step' := wp_step.
Time
Ltac
 wp_step :=
  try wp_bind;
   try
    match goal with
    | |- environments.envs_entails ?x ?igoal =>
          match igoal with
          | @wp _ _ _ _ _ _ _ (write_disk log_fst _) _ => iNamed
          iApply (write_log_fst with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (write_disk log_snd _) _ => iNamed
          iApply (write_log_snd with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (write_disk main_fst _) _ => iNamed
          iApply (write_main_fst with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (write_disk main_snd _) _ => iNamed
          iApply (write_main_snd with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (read_disk main_fst) _ => iNamed
          iApply (read_main_fst with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ (read_disk main_snd) _ => iNamed
          iApply (read_main_snd with "[$]"); iIntros "!>"; iLIntro
          | @wp _ _ _ _ _ _ _ _ _ => wp_step'
          end
    end.
Time
Definition helper\206\163 : gFunctors :=
  #[ GFunctor
       (authR
          (optionUR (exclR (prodO natO (prodO natO (procTC AtomicPair.Op))))));
  GFunctor (authR (optionUR (exclR (prodO natO natO))))].
Time
Instance subG_helper\206\163 :
 (subG helper\206\163 \206\163
  \226\134\146 inG \206\163
      (authR
         (optionUR (exclR (prodO natO (prodO natO (procTC AtomicPair.Op))))))).
Time Proof.
Time solve_inG.
Time Qed.
Time
Instance subG_helper\206\163' :
 (subG helper\206\163 \206\163 \226\134\146 inG \206\163 (authR (optionUR (exclR (prodO natO natO))))).
Time Proof.
Time solve_inG.
Time Qed.
Time
Definition \206\163 : gFunctors :=
  #[ Adequacy.exmach\206\163; @cfg\206\163 AtomicPair.Op AtomicPair.l; lock\206\163; helper\206\163].
Time Existing Instance subG_cfgPreG.
Time
Definition init_absr \207\1311a \207\1311c :=
  ExMach.l.(initP) \207\1311c \226\136\167 AtomicPair.l.(initP) \207\1311a.
Time Definition OpT := AtomicPair.Op.
Time Definition \206\155a := AtomicPair.l.
Time Definition impl := ImplLog.impl.
Time Import ExMach.
Time
Instance from_exist_left_sep'  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist ((\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \206\166 a \226\136\151 Q)%I).
Time Proof.
Time rewrite /FromExist.
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&$)".
Time (iExists _; eauto).
Time Qed.
Time Instance CFG : (@cfgPreG AtomicPair.Op AtomicPair.l \206\163).
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
Time #[global]
Instance inG_inst1 : (inG \206\163 (authR (optionUR (exclR (prodO natO natO))))).
Time Proof.
Time (apply _).
Time iApply (big_sepM_mono with "H").
Time Qed.
Time #[global]
Instance inG_inst2 :
 (inG \206\163
    (authR
       (optionUR (exclR (prodO natO (prodO natO (procTC AtomicPair.Op))))))).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance inG_inst3 : (lockG \206\163).
Time Proof.
Time (apply _).
Time Qed.
Time Definition exec_inv := fun H1 H2 => @ExecInv \206\163 H2 _ H1 _ _.
Time
Definition exec_inner :=
  fun H1 H2 =>
  (\226\136\131 \206\147 v1 v2,
     main_lock m\226\134\166 v1
     \226\136\151 log_lock m\226\134\166 v2
       \226\136\151 (\226\140\156v1 = 0\226\140\157 -\226\136\151 @MainLockInv \206\163 _ _ \206\147)
         \226\136\151 (\226\140\156v2 = 0\226\140\157 -\226\136\151 @LogLockInv \206\163 _ _ \206\147) \226\136\151 @ExecInner \206\163 H2 H1 _ _ \206\147)%I.
Time
Definition crash_inner := fun H1 H2 => (\226\136\131 \206\147, @CrashInner \206\163 H2 H1 _ _ \206\147)%I.
Time
Definition crash_param :=
  fun (_ : @cfgG OpT \206\155a \206\163) (_ : exmachG \206\163) => ghost_names.
Time Definition crash_inv := fun H1 H2 \206\147 => @CrashInv \206\163 H2 H1 _ _ \206\147.
Time
Definition crash_starter :=
  fun (H1 : @cfgG OpT \206\155a \206\163) (H2 : exmachG \206\163) \206\147 => (@CrashStarter \206\163 _ _ _ \206\147)%I.
Time Definition E := nclose sourceN.
Time Definition recv := recv.
Time End lRT.
Time Module lRD:=  exmach_refinement_definitions lRT.
Time iIntros ( k x Hlookup ) "((((?&?)&?)&?)&?)".
Time Module lRO: exmach_refinement_obligations lRT.
Time Module eRD:=  lRD.
Time Import lRT lRD.
Time
Lemma einv_persist :
  forall {H1 : @cfgG OpT \206\155a \206\163} {H2}, Persistent (exec_inv H1 H2).
Time Proof.
Time (apply _).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
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
Time (red).
Time (intros).
Time iIntros "(?&?&HDB)".
Time (destruct op).
Time -
Time iApply (write_refinement with "[$]").
Time iNext.
Time iIntros ( ? ) "H".
Time iFrame.
Time -
Time iApply (read_refinement with "[$]").
Time iNext.
Time iIntros ( ? ) "H".
Time iFrame.
Time Qed.
Time iExists _ , _.
Time iFrame.
Time Lemma exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx.
Time Proof.
Time (red).
Time (intros).
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&?)".
Time auto.
Time Qed.
Time eauto.
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time (intros ? ? \206\147).
Time iIntros "(H&Hreg&Hstarter)".
Time iDestruct "H" as "(#Hctx&#Hinv)".
Time iDestruct "Hstarter" as "(Hmain_lock&Hlog_lock&Hrest)".
Time
iDestruct "Hrest" as ( flag plog pcurr psrc )
 "(Hflag_ghost&Hcommit_lease&Hlog1&Hlog2&Hmain1&Hmain2&Hsrc_ghost)".
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_commit_inner "H").
Time (iLDestruct "Hcommit_inv").
Time (repeat unify_ghost).
Time wp_step.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time iIntros ( ? ? ) "H".
Time iDestruct "H" as ( hS ) "(#Hsrc&#Hlocks&#Hinv)".
Time (destruct flag as (flag, thd)).
Time (simpl).
Time (destruct flag).
Time *
Time recommit.
Time iInv "Hinv" as ">H" "_".
Time iNamed iFrame.
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
Time iFrame.
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
Time iModIntro.
Time wp_ret.
Time iInv "Hinv" as "H" "_".
Time iMod (disk1_next with "[$]") as "(Hd1&Hl1)".
Time (destruct_commit_inner "H").
Time (iLDestruct "Hsrc_inv").
Time (iLDestruct "Hcommit_inv").
Time (iLDestruct "Hmain_inv").
Time (iLDestruct "Hlog_inv").
Time (simpl).
Time (repeat unify_ghost).
Time iModIntro.
Time iCombine "Hd0 Hd1 Hstat Hinterp" as "Hleft".
Time iCombine "Hl0 Hl1" as "Hright".
Time iSplitL "Hleft".
Time *
Time iExists v0 , stat.
Time (do 5 unify_lease).
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
Time (simpl).
Time rewrite /CommitOff.
Time iEval rewrite -big_opM_dom in "Hl".
Time (iDestruct "Hsomewriter" as % Hpeq; subst).
Time iApply fupd_mask_weaken.
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time {
Time solve_ndisj.
Time Lemma state_interp_no_inv : state_interp_no_inv_type.
Time }
Time iExists psrc , psrc.
Time Proof.
Time done.
Time Qed.
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time iFrame "Hsrc".
Time iIntros ( ? ? ) "Hinner".
Time iPoseProof (eRO.crash_inner_inv with "Hinner") as "Hinv".
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by
 iPureIntro; econstructor).
Time eauto.
Time iClear "Hctx Hinv".
Time iIntros ( ? ? ? ) "(#Hctx&Hsrc)".
Time Qed.
Time
iMod
 (@ghost_var_update _ _ _ (\206\179flag \206\147) (0, (0, existT _ (Ret tt) : procTC _))
 with "Hflag_auth Hflag_ghost") as "(Hflag_auth&Hflag_ghost)".
Time Lemma exec_inner_inv : exec_inner_inv_type.
Time Proof.
Time iIntros ( ? ? ) "Hinner".
Time iPoseProof (eRO.exec_inner_inv with "Hinner") as "Hinv".
Time eauto.
Time rewrite /UnlockedInv.
Time iApply (big_sepM_mono with "H").
Time Qed.
Time iIntros ( k x Hlookup ) "((Hs&Hl)&H2)".
Time iDestruct "Hs" as ( ? ) "(%&Hs)".
Time Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Time Proof.
Time iIntros ( ? ? ) "Hdone Hinv".
Time iClear "Hmain1 Hmain2 Hlog1 Hlog2 Hcommit_lease".
Time iDestruct "Hl" as ( v1 v2 ) "(Hl0&Hl1)".
Time iPoseProof eRO.exec_inv_preserve_finish as "H".
Time iMod ("H" $! _ _ with "[$] [$]") as ( ? ? ) "(?&?&Hinv_post)".
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite (init_zero_lookup_is_zero k x) ;
 last  auto).
Time iFrame.
Time iMod (disk_next with "Hmain_fst") as "(Hmain_fst&Hmain1)".
Time iMod (disk_next with "Hmain_snd") as "(Hmain_snd&Hmain2)".
Time iModIntro.
Time iExists _ , _.
Time iFrame.
Time iMod (disk_next with "Hlog_fst") as "(Hlog_fst&Hlog1)".
Time iExists _ , _ , _.
Time iFrame.
Time iMod (disk_next with "Hlog_snd") as "(Hlog_snd&Hlog2)".
Time }
Time iExists _.
Time iFrame "Hstate".
Time iDestruct (gen_heap_bigOpM_dom with "hSb") as "hSb".
Time iMod (disk_next with "Hcommit") as "(Hcommit&Hcommit_lease)".
Time rewrite ?HdomL0 ?HdomL1 ?HdomS.
Time rewrite -?Hdom1.
Time iDestruct (big_sepM_dom with "hSb") as "hSb".
Time iSplitL "".
Time {
Time iPureIntro.
Time auto.
Time iModIntro.
Time iExists \206\147 , 0 , 0.
Time iFrame.
Time }
Time iSplitL "hS".
Time {
Time iExists _.
Time iFrame.
Time by iPureIntro.
Time }
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time iIntros.
Time iIntros ( ? \207\1312c \207\1312c' Hfinish ? ? ) "((?&Hmach)&?)".
Time (inversion Hfinish).
Time iDestruct (big_sepM_mono_with_inv with "Hctx_stat H") as "(?&$)".
Time subst.
Time iMod (gen_typed_heap_strong_init \226\136\133) as ( hM' Hmpf_eq' ) "(Hmc&Hm)".
Time iIntros ( k x Hlookup ) "H".
Time iDestruct "H" as "(Hctx_stat&H&Hdur)".
Time iDestruct "H" as ( stat0 ) "(%&Hs)".
Time
iMod (gen_heap_strong_init (\226\136\133 : gmap File (Inode * OpenMode))) as ( hFds'
 Hfds'_eq' ) "(Hfdsc&Hfd)".
Time iDestruct "Hdur" as ( ? stat ) "(Hd0&Hd1&Hs'&Hstatus)".
Time iDestruct (@gen_heap_valid with "Hctx_stat Hs'") as % ?.
Time
iMod
 (Count_Heap.gen_heap_strong_init
    (\206\187 s,
       ((\206\187 _ : LockStatus * (), (Unlocked, ())) <$> \207\1312c.(fs).(dirlocks)) !! s))
 as ( hDlocks' Hdlocks'_eq' ) "(Hdlocksc&Hlocks)".
Time
(repeat
  match goal with
  | H1:?x = Some ?y, H2:?x = Some ?z
    |- _ => rewrite H1 in  {} H2; inversion H2; clear H1 H2; subst
  end).
Time iFrame.
Time
iMod (ghost_var_alloc (A:=discreteO sliceLockC) None) as ( hGl''_name )
 "(HglA&Hgl)".
Time (set (hGl'' := GlobalG _ _ _ _ hGl''_name)).
Time iModIntro.
Time
iExists
 (GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
    (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl'' _).
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time Qed.
Time (simpl).
Time
iPoseProof (goose_interp_split_read_dir with "Hmach") as
 "(Hmach&Hroot&Hdom_eq)".
Time iSplitL "Hmc Hmach Hfdsc Hdlocksc HglA".
Time {
Time iDestruct "Hmach" as "(?&(?&?&?&?&?&?)&?)".
Time (repeat deex).
Time inv_step.
Time (inversion _z).
Time inv_step.
Time (inversion _z0).
Time inv_step.
Time (inversion H1).
Time inv_step.
Time deex.
Time inv_step.
Time iSplitL "Hmain1 Hmain2 Hsrc_ghost".
Time (unfold RecordSet.set).
Time (simpl).
Time iFrame.
Time {
Time (iIntros; iExists _; iFrame).
Time }
Time iSplitL "Hlog1 Hlog2".
Time {
Time (iIntros; iExists _; iFrame).
Time }
Time recommit.
Time rewrite /CommitInner' /FlagInv.
Time iNamed iFrame.
Time (iNamed iFrame; auto).
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
Time *
Time (destruct plog as (plog1, plog2)).
Time recommit.
Time iInv "Hinv" as ">H" "_".
Time iNamed iFrame.
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
Time (simpl).
Time rewrite dom_fmap_L.
Time iFrame.
Time }
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
Time iIntros "(Hctx'&Hsrc')".
Time iModIntro.
Time iMod ("Hinv_post" $! _ _ hM' with "[-]").
Time {
Time iIntros ( ? ? Heq ) "(Hdone&Hinv)".
Time rewrite /DurInv.
Time iDestruct "Hinv" as ( v0 stat ) "(Hd0&Hd1&Hstat&Hinterp)".
Time (<ssreflect_plugin::ssrtclseq@0> destruct stat ; last  first).
Time iFrame.
Time {
Time iDestruct "Hinterp" as "(?&Hreg)".
Time (iExFalso; iApply (@AllDone_Register_excl with "Hdone Hreg")).
Time }
Time iFrame.
Time iExists _.
Time iFrame.
Time
(iPoseProof
  (@Count_Heap.gen_heap_init_to_bigOp _ _ _ _ _ _ _ _ with "[Hlocks]") as
  "Hl"; swap 1 2).
Time {
Time rewrite Hdlocks'_eq'.
Time eauto.
Time }
Time {
Time (intros s ?).
Time rewrite lookup_fmap.
Time by intros (?, (?, ->))%fmap_Some_1.
Time }
Time iDestruct "Hdom_eq" as % ->.
Time iApply big_sepM_dom.
Time rewrite big_sepM_fmap.
Time eauto.
Time eauto.
Time Qed.
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
Time iFrame.
Time rewrite -{+2}Hdom1.
Time iDestruct (big_sepM_dom with "hSb") as "hSb".
Time (repeat iDestruct (@big_sepM_sep with "[$]") as "H").
Time End RO.
Time Module R:=  refinement RT RO.
Time Export R.
Time End goose_refinement.
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
Time iModIntro.
Time wp_bind.
Time (iFastInv "Hinv" "H").
Time (destruct_commit_inner "H").
Time (iLDestruct "Hlog_inv").
Time destruct_pairs.
Time (repeat unify_ghost).
Time (repeat unify_lease).
Time wp_step.
Time iModIntro.
Time recommit.
Time iNamed iFrame.
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
Time iFrame.
Time wp_bind.
Time (iFastInv "Hinv" "H").
Time (destruct_commit_inner "H").
Time (iLDestruct "Hlog_inv").
Time destruct_pairs.
Time (repeat unify_ghost).
Time (repeat unify_lease).
Time wp_step.
Time iModIntro.
Time recommit.
Time iNamed iFrame.
Time iFrame.
Time (repeat wp_step).
Time
iNamedAux iApply
 (unset_commit' True%I _ _ (plog1, plog2) with "[-Hmain_lock Hlog_lock]").
Time {
Time iFrame.
Time iFrame "Hctx".
Time iFrame "Hinv".
Time }
Time (iIntros "!> "; iLIntro).
Time iInv "Hinv" as "H" "_".
Time (destruct_commit_inner "H").
Time (simpl).
Time (iLDestruct "Hmain_inv").
Time (iLDestruct "Hcommit_inv").
Time (iLDestruct "Hsrc_inv").
Time (iLDestruct "Hlog_inv").
Time destruct_pairs.
Time (repeat unify_ghost).
Time (do 4 unify_lease).
Time iDestruct "Hsomewriter" as % Hpeq.
Time iApply fupd_mask_weaken.
Time {
Time solve_ndisj.
Time }
Time iExists (plog1, plog2) , (plog1, plog2).
Time iFrame.
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by
 iPureIntro; econstructor).
Time iClear "Hctx Hinv".
Time iIntros ( ? ? ? ) "(#Hctx&Hsrc)".
Time
iMod
 (@ghost_var_update _ _ _ (\206\179flag \206\147) (0, (0, existT _ (Ret tt) : procTC _))
 with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
Time iClear "Hmain1 Hmain2 Hcommit_lease".
Time iMod (disk_next with "Hmain_fst") as "(Hmain_fst&Hmain1)".
Time iMod (disk_next with "Hmain_snd") as "(Hmain_snd&Hmain2)".
Time iMod (disk_next with "Hlog_fst") as "(Hlog_fst&Hlog1')".
Time iMod (disk_next with "Hlog_snd") as "(Hlog_snd&Hlog2')".
Time iMod (disk_next with "Hcommit") as "(Hcommit&Hcommit_lease)".
Time iModIntro.
Time iExists \206\147 , 0 , 0.
Time iFrame.
Time iSplitL "Hmain1 Hmain2 Hsrc_ghost".
Time {
Time (iIntros; iExists (_, _); iFrame).
Time }
Time iSplitL "Hlog1' Hlog2'".
Time {
Time (iIntros; iExists (_, _); iFrame).
Time }
Time iExists _ , (_, _) , (_, _) , (_, _).
Time recommit'.
Time rewrite /CommitInner' /FlagInv.
Time iNamed iFrame.
Time (iNamed iFrame; auto).
Time Time Qed.
Time Lemma init_wf : \226\136\128 \207\1311a \207\1311c, init_absr \207\1311a \207\1311c \226\134\146 ExMach.state_wf \207\1311c.
Time Proof.
Time (intros ? ? (H, ?)).
Time (inversion H).
Time subst.
Time (eapply ExMach.init_state_wf).
Time Qed.
Time Lemma init_exec_inner : init_exec_inner_type.
Time Proof.
Time (intros ? ? (H, Hinit) ? ?).
Time (inversion H).
Time (inversion Hinit).
Time subst.
Time iIntros "(Hmem&Hdisk&#?&Hstate)".
Time
iMod (@ghost_var_alloc _ _ _ _ (0, (0, existT _ (Ret tt) : procTC _))) as (
 \206\179flag ) "[Hflag_auth Hflag_ghost]".
Time iMod (ghost_var_alloc (0, 0)) as ( \206\179src ) "[Hsrc_auth Hsrc_ghost]".
Time iModIntro.
Time iExists {| \206\179flag := \206\179flag; \206\179src := \206\179src |}.
Time iExists 0 , 0.
Time iPoseProof (init_mem_split with "Hmem") as "(?&?)".
Time
iPoseProof (init_disk_split with "Hdisk") as
 "((?&?&?&?&?)&Hcommit&Hmain1&Hmain2&Hlog1&Hlog2)".
Time iFrame.
Time iSplitL "Hmain1 Hmain2 Hsrc_ghost".
Time {
Time (iIntros; iExists _; iFrame).
Time }
Time iSplitL "Hlog1 Hlog2".
Time {
Time (iIntros; iExists (_, _); iFrame).
Time }
Time iExists _ , (0, 0) , (0, 0) , (0, 0).
Time rewrite /CommitInner' /FlagInv.
Time unbundle_names.
Time iFrame.
Time rewrite /MainInv /LogInv /CommitOff.
Time iNamed iFrame.
Time (simpl).
Time iFrame.
Time auto.
Time Qed.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "H".
Time iDestruct "H" as ( \206\147 ) "Hrest".
Time iDestruct "Hrest" as "(#Hsource_inv&#Hmain_lock&#Hlog_lock&#Hinv)".
Time iDestruct "Hmain_lock" as ( \206\179lock_main ) "Hmlock".
Time iDestruct "Hlog_lock" as ( \206\179lock_log ) "Hlock".
Time iInv "Hinv" as "H" "_".
Time iDestruct "H" as ">H".
Time iDestruct "H" as ( flag plog pmain psrc ) "H".
Time (iLDestruct "H"; iAssignNames).
Time (iLDestruct "Hmain_inv").
Time (iLDestruct "Hcommit_inv").
Time (iLDestruct "Hsrc_inv").
Time (iLDestruct "Hlog_inv").
Time iClear "Hflag_auth Hsrc_auth".
Time iMod (ghost_var_alloc flag) as ( \206\179flag ) "[Hflag_auth Hflag_ghost]".
Time iMod (ghost_var_alloc psrc) as ( \206\179src ) "[Hsrc_auth Hsrc_ghost]".
Time iMod (disk_next with "Hmain_fst") as "(Hmain_fst&Hmain1)".
Time iMod (disk_next with "Hmain_snd") as "(Hmain_snd&Hmain2)".
Time iMod (disk_next with "Hlog_fst") as "(Hlog_fst&Hlog1')".
Time iMod (disk_next with "Hlog_snd") as "(Hlog_snd&Hlog2')".
Time iMod (disk_next with "Hcommit") as "(Hcommit&Hcommit_lease)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?)".
Time iModIntro.
Time iExists {| \206\179flag := \206\179flag; \206\179src := \206\179src |}.
Time rewrite /CrashInner /ExecInner /CommitInner.
Time recommit.
Time rewrite /CommitInner' /FlagInv.
Time unbundle_names.
Time iFrame.
Time iNamed iFrame.
Time (simpl).
Time iFrame.
Time iSplitL "Hsomewriter".
Time {
Time iIntros.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (fst flag) ; first  by iFrame).
Time rewrite /CommitOn.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply
 (someone_writing_weaken with "[] [Hsomewriter]") ; last  first).
Time {
Time iApply "Hsomewriter".
Time }
Time {
Time eauto.
Time }
Time }
Time (simpl).
Time iFrame.
Time iExists flag , plog , pmain , psrc.
Time (simpl).
Time iFrame.
Time Qed.
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time Proof.
Time (red).
Time (intros ? ? \206\147).
Time iIntros "(#Hctx&#Hinv)".
Time iInv "Hinv" as ">H" "_".
Time iDestruct "H" as ( flag plog pmain psrc ) "H".
Time (iLDestruct "H").
Time (iLDestruct "Hmain_inv").
Time (iLDestruct "Hcommit_inv").
Time (iLDestruct "Hsrc_inv").
Time (iLDestruct "Hlog_inv").
Time iClear "Hflag_auth Hsrc_auth".
Time iMod (ghost_var_alloc flag) as ( \206\179flag ) "[Hflag_auth Hflag_ghost]".
Time iMod (ghost_var_alloc psrc) as ( \206\179src ) "[Hsrc_auth Hsrc_ghost]".
Time iMod (disk_next with "Hmain_fst") as "(Hmain_fst&Hmain1)".
Time iMod (disk_next with "Hmain_snd") as "(Hmain_snd&Hmain2)".
Time iMod (disk_next with "Hlog_fst") as "(Hlog_fst&Hlog1')".
Time iMod (disk_next with "Hlog_snd") as "(Hlog_snd&Hlog2')".
Time iMod (disk_next with "Hcommit") as "(Hcommit&Hcommit_lease)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?)".
Time iModIntro.
Time iExists {| \206\179flag := \206\179flag; \206\179src := \206\179src |}.
Time rewrite /CrashInner /ExecInner /CommitInner.
Time iAssignNames.
Time iExists flag , plog , pmain , psrc.
Time (simpl).
Time rewrite /CommitInner'.
Time unbundle_names.
Time iNamed iFrame.
Time iFrame.
Time iExists flag , plog , pmain , psrc.
Time (simpl).
Time iFrame.
Time Qed.
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "(Hinv&#Hsrc)".
Time iDestruct "Hinv" as ( invG \206\147 ) "Hinv".
Time iDestruct "Hinv" as "(Hexec&Hinv)".
Time iMod (@inv_alloc \206\163 exm_invG liN _ (CommitInner True%I \206\147) with "Hexec").
Time iModIntro.
Time iExists \206\147.
Time iFrame.
Time iFrame "Hsrc".
Time Qed.
Time Lemma exec_inner_inv : exec_inner_inv_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "(Hinv&#Hsrc)".
Time iDestruct "Hinv" as ( invG \206\147 v1 v2 ) "(Hmlock&Hllock&Hml&Hll&Hexec)".
Time iMod (@inv_alloc \206\163 exm_invG liN _ (ExecInner \206\147) with "Hexec").
Time
iMod
 (@lock_init \206\163 (ExMachG _ exm_invG exm_mem_inG exm_disk_inG _) _ mlN
    main_lock _ (MainLockInv \206\147) with "[$] Hml") as ( \206\179lock ) "H".
Time
iMod
 (@lock_init \206\163 (ExMachG _ exm_invG exm_mem_inG exm_disk_inG _) _ llN log_lock
    _ (LogLockInv \206\147) with "[$] Hll") as ( \206\179lock' ) "H'".
Time iModIntro.
Time iFrame "Hsrc".
Time iExists \206\147.
Time iFrame.
Time (iExists _; iFrame).
Time (iExists _; iFrame).
Time Qed.
Time Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Time Proof.
Time iIntros ( ? ? ) "Had H".
Time iDestruct "H" as ( \206\147 ) "(Hsrc_ctx&Hmlock&Hlock&Hinv)".
Time iInv "Hinv" as ">H" "_".
Time iDestruct "H" as ( flag plog pmain psrc ) "H".
Time (iLDestruct "H").
Time (iLDestruct "Hmain_inv").
Time (iLDestruct "Hcommit_inv").
Time (iLDestruct "Hsrc_inv").
Time (iLDestruct "Hlog_inv").
Time iDestruct "Hmlock" as ( \206\179lock_main ) "Hmlock".
Time iDestruct "Hlock" as ( \206\179lock_log ) "Hlock".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (lock_crack with "Hmlock") as ( ? )
 ">(Hmlock&?)" ; first  by solve_ndisj).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (lock_crack with "Hlock") as ( ? )
 ">(Hlock&?)" ; first  by solve_ndisj).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time (iExists _ , _; iFrame).
Time iSplitL "".
Time {
Time iPureIntro.
Time econstructor.
Time }
Time iClear "Hsrc_ctx".
Time iIntros ( ? ? ? ? ) "(#Hctx&Hsrc&Hmem)".
Time
(<ssreflect_plugin::ssrtclseq@0>
 match goal with
 | |- context [ own (\206\179flag \206\147) (\226\151\143 Excl' ?x) ] => destruct (fst x)
 end ; last  first).
Time {
Time rewrite /CommitOn.
Time rewrite someone_writing_unfold.
Time iDestruct "Hsomewriter" as ( ? ? ) "(Hreg&?&?)".
Time iExFalso.
Time iApply (@AllDone_Register_excl with "Had Hreg").
Time }
Time iDestruct "Hsomewriter" as % hp.
Time subst.
Time
iMod (@ghost_var_alloc _ _ _ _ (0, (0, existT _ (Ret tt) : procTC _))) as (
 \206\179flag ) "[Hflag_auth' Hflag_ghost']".
Time iMod (ghost_var_alloc psrc) as ( \206\179src ) "[Hsrc_auth' Hsrc_ghost']".
Time iMod (disk_next with "Hmain_fst") as "(Hmain_fst&Hmain1)".
Time iMod (disk_next with "Hmain_snd") as "(Hmain_snd&Hmain2)".
Time iMod (disk_next with "Hlog_fst") as "(Hlog_fst&Hlog1')".
Time iMod (disk_next with "Hlog_snd") as "(Hlog_snd&Hlog2')".
Time iMod (disk_next with "Hcommit") as "(Hcommit&Hcommit_lease)".
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?)".
Time iExists {| \206\179flag := \206\179flag; \206\179src := \206\179src |}.
Time iExists _ , _.
Time iFrame.
Time rewrite /MainLockInv.
Time iSplitL "Hmain1 Hmain2 Hsrc_ghost'".
Time {
Time (iModIntro; iIntros).
Time iExists psrc.
Time iFrame.
Time }
Time iSplitL "Hlog1' Hlog2'".
Time {
Time (iModIntro; iIntros).
Time iExists plog.
Time iFrame.
Time }
Time iModIntro.
Time iExists _ , _ , _ , _.
Time rewrite /CommitInner' /FlagInv /MainInv /LogInv /SrcInv.
Time unbundle_names.
Time iFrame.
Time (simpl).
Time auto.
Time Qed.
Time End lRO.
Time Module lR:=  exmach_refinement lRT lRO.
Time Import lR.
Time
Lemma exmach_crash_refinement_seq {T} \207\1311c \207\1311a (es : proc_seq AtomicPair.Op T)
  :
  lRT.init_absr \207\1311a \207\1311c
  \226\134\146 wf_client_seq es
    \226\134\146 \194\172 proc_exec_seq AtomicPair.l es (rec_singleton (Ret ())) (1, \207\1311a) Err
      \226\134\146 \226\136\128 \207\1312c res,
          proc_exec_seq ExMach.l (compile_proc_seq ImplLog.impl es)
            (rec_singleton recv) (1, \207\1311c) (Val \207\1312c res)
          \226\134\146 \226\136\131 \207\1312a,
              proc_exec_seq AtomicPair.l es (rec_singleton (Ret tt)) 
                (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (apply lR.R.crash_refinement_seq).
Time Qed.
