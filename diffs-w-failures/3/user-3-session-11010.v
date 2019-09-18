Time From iris.algebra Require Import auth gmap frac agree.
Time Require Import Goose.Proof.Interp.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementAdequacy
  CSL.RefinementIdempotenceModule.
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
Time
Definition fs\206\163 (m : GoModel) {wf : GoModelWf m} : gFunctors :=
  #[ gen_heap\206\163 string (gset string); Count_Heap.gen_heap\206\163 string unit;
  gen_dir\206\163 string string Inode; gen_heap\206\163 Inode (List.list byte);
  gen_heap\206\163 File (Inode * OpenMode); ghost_map\206\163 (discreteO (gset string))].
Time #[global]
Instance subG_fsPreG  m {wf : GoModelWf m} {\206\163}:
 (subG (fs\206\163 m) \206\163 \226\134\146 (fsPreG m) \206\163).
Time Proof.
Time solve_inG.
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
Time Qed.
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
Time End goose_refinement_definitions.
Time Module Type goose_refinement_obligations (eRT: goose_refinement_type).
Time Module eRD:=  goose_refinement_definitions eRT.
Time Import eRT.
Time Import eRD.
Time Context (recsingle : recover = rec_singleton eRT.recv).
Time Context (nameIncl : nclose sourceN \226\138\134 eRT.E).
Time
Context
 (einv_persist : forall {H1 : @cfgG OpT \206\155a eRT.\206\163} {H2},
                 Persistent (exec_inv H1 H2)).
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
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time rewrite /recv_triple_type.
Time iIntros ( ? ? ? ) "(#Hinv&Hreg&Hstart)".
Time iPoseProof @eRO.recv_triple as "H".
Time iSpecialize ("H" with "[$]").
Time iApply (wp_wand with "H").
Time iIntros ( _ ) "H".
Time iMod "H" as ( \207\1312a \207\1312a' ) "(?&%&H)".
Time iModIntro.
Time iExists _ , _.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR ; first  by iPureIntro).
Time iIntros.
Time rewrite /post_recv.
Time iIntros ( ? ? ? ? ) "((_&Hstate)&Hthread)".
Time iModIntro.
Time iExists _.
Time iFrame.
Time iIntros.
Time iModIntro.
Time by iMod ("H" with "[$]").
Time Qed.
Time Existing Instance eRT.HEX.
Time Lemma init_exec_inner : init_exec_inner_type.
Time Proof.
Time rewrite /init_exec_inner_type.
Time iIntros ( \207\1311a \207\1311c Hinit ? ? ? ).
Time
iMod (gen_typed_heap_strong_init \207\1311c.(fs).(heap).(allocs)) as ( hM Hmpf_eq )
 "(Hmc&Hm)".
Time
iMod (gen_heap_strong_init (fmap (dom (gset string)) \207\1311c.(fs).(dirents))) as
 ( hD Hdpf_eq ) "(Hdc&Hd)".
Time
iMod (gen_heap_strong_init \207\1311c.(fs).(fds)) as ( hFDs HFDpf_eq ) "(Hfdc&Hfd)".
Time
iMod (gen_heap_strong_init \207\1311c.(fs).(inodes)) as ( hIs HIpf_eq ) "(Hidc&Hi)".
Time
iMod (gen_dir_strong_init \207\1311c.(fs).(dirents)) as ( hP HPpf_eq ) "(Hpc&Hp)".
Time
iMod (Count_Heap.gen_heap_strong_init (\206\187 s, \207\1311c.(fs).(dirlocks) !! s)) as (
 hL HLpf_eq ) "(Hlc&Hl)".
Time
iMod
 (ghost_var_alloc (A:=discreteO (gset string))
    (dom (gset string) \207\1311c.(fs).(dirents))) as ( hGD ) "(HgdA&Hgd)".
Time replace 0%Z with O : Z by auto.
Time
iPoseProof
 (Count_Ghost.read_split (A:=discreteO (gset string)) hGD with "Hgd") as
 "(Hgd&Hgdr)".
Time
iMod (ghost_var_alloc (A:=discreteO sliceLockC) \207\1311c.(maillocks)) as ( hGL )
 "(HglA&Hgl)".
Time (set (hFG := FsG _ _ \206\163 hL hD hP hIs hFDs _ hGD)).
Time (set (hGl := GlobalG _ _ _ _ hGL)).
Time (set (hG := GooseG _ _ \206\163 _ hM hFG hGl _)).
Time iPoseProof (eRO.init_exec_inner \207\1311a \207\1311c Hinit hG _) as "H".
Time iExists hG.
Time iModIntro.
Time iIntros "(Hsource1&Hsource2&Hthread)".
Time iFrame.
Time iMod ("H" with "[-Hgd]") as "Hinner".
Time {
Time iFrame.
Time (edestruct eRO.init_wf as (?, (?, ->)); eauto).
Time iFrame.
Time iSplitL "Hd".
Time *
Time iPoseProof (@gen_heap_init_to_bigOp _ _ _ _ _ hD with "[Hd]") as "?".
Time {
Time by rewrite Hdpf_eq.
Time }
Time by rewrite big_opM_fmap.
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
Time }
Time (edestruct eRO.init_wf as (->, (_, _)); eauto).
Time iApply big_sepM_dom.
Time iApply (big_sepM_mono with "Hl").
Time (intros ? (?, []); eauto).
Time }
Time iFrame.
Time iModIntro.
Time iSplitL "Hgd".
Time -
Time iExists _.
Time iFrame.
Time -
Time (edestruct eRO.init_wf as (?, ?); eauto).
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
Time iDestruct "Hroot" as ( n ) "Hmapsto".
Time iFrame.
Time iFrame "%".
Time rewrite Count_Ghost.read_split.
Time iDestruct "Hmapsto" as "(?&?)".
Time iFrame.
Time iExists (S n).
Time eauto.
Time Qed.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time rewrite /exec_inv_preserve_crash_type.
Time iIntros ( ? ? ) "Hinv".
Time iPoseProof (eRO.exec_inv_preserve_crash with "Hinv") as "Hinv_post".
Time iMod "Hinv_post" as "Hinv_post".
Time iModIntro.
Time iIntros ( ? n \207\131 ) "((?&Hmach)&Hthread)".
Time iMod (gen_typed_heap_strong_init \226\136\133) as ( hM' Hmpf_eq' ) "(Hmc&Hm)".
Time
iMod (gen_heap_strong_init (\226\136\133 : gmap File (Inode * OpenMode))) as ( hFds'
 Hfds'_eq' ) "(Hfdsc&Hfd)".
Time
iMod
 (Count_Heap.gen_heap_strong_init
    (\206\187 s,
       ((\206\187 _ : LockStatus * (), (Unlocked, ())) <$> \207\131.(fs).(dirlocks)) !! s))
 as ( hDlocks' Hdlocks'_eq' ) "(Hdlocksc&Hlocks)".
Time
iMod (ghost_var_alloc (A:=discreteO sliceLockC) None) as ( hGl_name )
 "(HglA&Hgl)".
Time (set (hGl := GlobalG _ _ _ _ hGl_name)).
Time
iPoseProof (goose_interp_split_read_dir with "Hmach") as
 "(Hmach&Hroot&Hdom_eq)".
Time iMod ("Hinv_post" with "[Hm Hgl Hlocks Hroot Hdom_eq]") as "Hinv'".
Time {
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
Time eauto.
Time }
Time iModIntro.
Time iIntros ( \207\131' Hcrash ).
Time
iExists
 (GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
    (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl _).
Time (destruct Hcrash as ([], ((?, ?), (Hput, Hrest)))).
Time (inversion Hput).
Time subst.
Time inv_step.
Time (inversion Hrest; subst).
Time (simpl).
Time (repeat inv_step).
Time (inversion H).
Time deex.
Time inv_step.
Time inv_step.
Time (inversion H).
Time deex.
Time inv_step.
Time (unfold RecordSet.set in *).
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
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time Proof.
Time rewrite /crash_inv_preserve_crash_type.
Time iIntros ( ? ? ? ) "Hinv".
Time iPoseProof (eRO.crash_inv_preserve_crash with "Hinv") as "Hinv_post".
Time iMod "Hinv_post" as "Hinv_post".
Time iModIntro.
Time iIntros ( ? n \207\131 ) "((?&Hmach)&Hthread)".
Time iMod (gen_typed_heap_strong_init \226\136\133) as ( hM' Hmpf_eq' ) "(Hmc&Hm)".
Time
iMod (gen_heap_strong_init (\226\136\133 : gmap File (Inode * OpenMode))) as ( hFds'
 Hfds'_eq' ) "(Hfdsc&Hfd)".
Time
iMod
 (Count_Heap.gen_heap_strong_init
    (\206\187 s,
       ((\206\187 _ : LockStatus * (), (Unlocked, ())) <$> \207\131.(fs).(dirlocks)) !! s))
 as ( hDlocks' Hdlocks'_eq' ) "(Hdlocksc&Hlocks)".
Time
iMod (ghost_var_alloc (A:=discreteO sliceLockC) None) as ( hGl_name )
 "(HglA&Hgl)".
Time (set (hGl := GlobalG _ _ _ _ hGl_name)).
Time
iPoseProof (goose_interp_split_read_dir with "Hmach") as
 "(Hmach&Hroot&Hdom_eq)".
Time iMod ("Hinv_post" with "[Hm Hgl Hlocks Hroot Hdom_eq]") as "Hinv'".
Time {
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
Time eauto.
Time }
Time iModIntro.
Time iIntros ( \207\131' Hcrash ).
Time
iExists
 (GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
    (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl _).
Time (destruct Hcrash as ([], ((?, ?), (Hput, Hrest)))).
Time (inversion Hput).
Time subst.
Time inv_step.
Time (inversion Hrest; subst).
Time (simpl).
Time (repeat inv_step).
Time (inversion H).
Time deex.
Time inv_step.
Time inv_step.
Time (inversion H).
Time deex.
Time inv_step.
Time (unfold RecordSet.set in *).
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
Time Lemma state_interp_no_inv : state_interp_no_inv_type.
Time Proof.
Time done.
Time Qed.
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time iIntros ( ? ? ) "Hinner".
Time iPoseProof (eRO.crash_inner_inv with "Hinner") as "Hinv".
Time eauto.
Time Qed.
Time Lemma exec_inner_inv : exec_inner_inv_type.
Time Proof.
Time iIntros ( ? ? ) "Hinner".
Time iPoseProof (eRO.exec_inner_inv with "Hinner") as "Hinv".
Time eauto.
Time Qed.
Time Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Time Proof.
Time iIntros ( ? ? ) "Hdone Hinv".
Time iPoseProof eRO.exec_inv_preserve_finish as "H".
Time iMod ("H" $! _ _ with "[$] [$]") as ( ? ? ) "(?&?&Hinv_post)".
Time iModIntro.
Time iExists _ , _.
Time iFrame.
Time iIntros.
Time iIntros ( ? \207\1312c \207\1312c' Hfinish ? ? ) "((?&Hmach)&?)".
Time (inversion Hfinish).
Time subst.
Time iMod (gen_typed_heap_strong_init \226\136\133) as ( hM' Hmpf_eq' ) "(Hmc&Hm)".
Time
iMod (gen_heap_strong_init (\226\136\133 : gmap File (Inode * OpenMode))) as ( hFds'
 Hfds'_eq' ) "(Hfdsc&Hfd)".
Time
iMod
 (Count_Heap.gen_heap_strong_init
    (\206\187 s,
       ((\206\187 _ : LockStatus * (), (Unlocked, ())) <$> \207\1312c.(fs).(dirlocks)) !! s))
 as ( hDlocks' Hdlocks'_eq' ) "(Hdlocksc&Hlocks)".
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
Time (unfold RecordSet.set).
Time (simpl).
Time iFrame.
Time (simpl).
Time rewrite dom_fmap_L.
Time iFrame.
Time }
Time iIntros "(Hctx'&Hsrc')".
Time iModIntro.
Time iMod ("Hinv_post" $! _ _ hM' with "[-]").
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
Time End RO.
Time Module R:=  refinement RT RO.
Time Export R.
Time End goose_refinement.
