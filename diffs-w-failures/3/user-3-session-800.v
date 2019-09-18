Time From iris.algebra Require Import auth gmap frac agree.
Time From iris.algebra Require Import auth gmap list.
Time Require Import Goose.Proof.Interp.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time From Armada.Examples.MailServer Require Import MailAPI.
Time From Armada.Goose.Examples Require Import MailServer.
Time From Armada.Goose.Proof Require Import Interp.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Adequacy CSL.RefinementAdequacy
  CSL.RefinementIdempotenceModule.
Time Require Import Goose.Proof.Interp.
Time From Armada Require AtomicPair.Helpers.
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
         go_fs_domalg_preG :> ghost_mapG (discreteC (gset string)) \206\163}.
Time From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Armada.Goose Require Import Machine.
Time From Armada.Goose Require Import GoZeroValues.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep.
Time Set Default Goal Selector "!".
Time Set Default Proof Using "Type".
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time Import Mail.
Time
Ltac
 non_err' :=
  match goal with
  | |- context [ ?x = Some _ ] =>
        match x with
        | None => fail 1
        | Some _ => fail 1
        | _ => let Heq := fresh "Heq" in
               destruct x as [?| ] eqn:Heq
        end
  | |- lookup _ _ _ _ => unfold lookup
  | |- unwrap _ _ _ => unfold unwrap
  | |- readSome _ _ _ => unfold readSome
  | |- context [ match ?x with
                 | _ => _
                 end ] => match goal with
                          | H:x = _ |- _ => rewrite H
                          end
  end.
Time Ltac non_err := repeat non_err'; trivial.
Time
Ltac
 ghost_err :=
  iMod (ghost_step_err with "[$] [$] [$]") ||
    match goal with
    | |- context [ (_ \226\164\135 ?K _)%I ] => iMod
      (@ghost_step_err _ _ _ _ _ _ _ _ _ _ (\206\187 x, K (Bind x _))
      with "[$] [$] [$]")
    end; eauto.
Time Ltac do_then := repeat (do 2 eexists; split; non_err).
Time
Ltac
 err_start := <ssreflect_plugin::ssrtclseq@0>
 left; right; do_then; destruct (open) ; last  by econstructor.
Time Ltac err_hd := left; non_err; try econstructor.
Time Ltac err_cons := right; do_then.
Time Ltac err0 := err_start; err_hd.
Time Ltac err1 := err_start; err_cons; err_hd.
Time Ltac err2 := err_start; err_cons; err_cons; err_hd.
Time Ltac err3 := err_start; err_cons; err_cons; err_cons; err_hd.
Time Ltac solve_err := ghost_err; (solve [ err0 | err1 | err2 | err3 ]).
Time Section api_lemmas.
Time Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Time #[global]Instance source_state_inhab : (Inhabited State).
Time Proof.
Time eexists.
Time exact {| heap := \226\136\133; messages := \226\136\133; open := false |}.
Time Qed.
Time #[global]Instance LockRef_inhab : (Inhabited LockRef).
Time Proof.
Time eexists.
Time (apply nullptr).
Time Qed.
Time
Lemma open_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call Open)
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\140\156\207\131.(open) = false\226\140\157 \226\136\151 j \226\164\135 K (Call Open) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time
Definition fs\206\163 (m : GoModel) {wf : GoModelWf m} : gFunctors :=
  #[ gen_heap\206\163 string (gset string); Count_Heap.gen_heap\206\163 string unit;
  gen_dir\206\163 string string Inode; gen_heap\206\163 Inode (List.list byte);
  gen_heap\206\163 File (Inode * OpenMode); ghost_map\206\163 (discreteC (gset string))].
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
            goose_preG_global :> ghost_mapG (discreteC sliceLockC) \206\163;
            goose_preG_treg_inG :>
             inG \206\163 (csumR countingR (authR (optionUR (exclR unitC))))}.
Time
Definition goose\206\163 (m : GoModel) {wf : GoModelWf m} : gFunctors :=
  #[ inv\206\163; fs\206\163 m; gen_typed_heap\206\163 Ptr ptrRawModel;
  ghost_map\206\163 (discreteC sliceLockC);
  GFunctor (csumR countingR (authR (optionUR (exclR unitC))))].
Time #[global]
Instance subG_goosePreG  (m : GoModel) {wf : GoModelWf m} 
 {\206\163}: (subG (goose\206\163 m) \206\163 \226\134\146 goosePreG m \206\163).
Time (destruct \207\131.(open) as [| ] eqn:Heq).
Time Proof.
Time solve_inG.
Time -
Time ghost_err.
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
Context `{REG : inG \206\163 (csumR countingR (authR (optionUR (exclR unitC))))}.
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
Time (intros n).
Time left.
Time right.
Time (do 2 eexists).
Time split.
Time {
Time rewrite /reads.
Time rewrite Heq.
Time econstructor.
Time }
Time (simpl).
Time econstructor.
Time -
Time by iFrame.
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time rewrite /recv_triple_type.
Time iIntros ( ? ? ? ) "(#Hinv&Hreg&Hstart)".
Time iPoseProof @eRO.recv_triple as "H".
Time iSpecialize ("H" with "[$]").
Time Qed.
Time iApply (wp_wand with "H").
Time
Lemma open_open_step_inv {T} {T'} j j' K K' `{LanguageCtx _ _ T Mail.l K}
  `{LanguageCtx _ _ T' Mail.l K'} (\207\131 : l.(OpState)) 
  E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call Open)
    -\226\136\151 j' \226\164\135 K' (Call Open) -\226\136\151 source_ctx -\226\136\151 source_state \207\131 ={E}=\226\136\151 False.
Time Proof.
Time iIntros ( ? ) "Hj Hj' #Hsrc Hstate".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (open_step_inv with "[$] [$] [$]") as (
 Hopen ) "(?&?)" ; first  auto).
Time iIntros ( _ ) "H".
Time iMod "H" as ( \207\1312a \207\1312a' ) "(?&%&H)".
Time iModIntro.
Time iExists _ , _.
Time iFrame.
Time iMod (ghost_step_call with "[$] [$] [$]") as "(?&?&?)".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR ; first  by iPureIntro).
Time iIntros.
Time rewrite /post_recv.
Time iIntros ( ? ? ? ? ) "((_&Hstate)&Hthread)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  by econstructor).
Time (econstructor; auto).
Time (do 2 eexists; split).
Time {
Time rewrite /reads Hopen //=.
Time iModIntro.
Time }
Time (simpl).
Time (do 2 eexists).
Time split.
Time *
Time econstructor.
Time *
Time econstructor.
Time }
Time {
Time auto.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (open_step_inv with "[$] [$] [$]") as (
 Hopen' ) "(?&?)" ; first  auto).
Time iExists _.
Time iFrame.
Time iIntros.
Time iModIntro.
Time by iMod ("H" with "[$]").
Time Qed.
Time (simpl in Hopen').
Time congruence.
Time Qed.
Time
Lemma pickup_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (pickup uid)
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\140\156\226\136\131 v, \207\131.(messages) !! uid = Some v\226\140\157
                 \226\136\151 j \226\164\135 K (pickup uid) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
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
Time (iIntros; iFrame; eauto).
Time
iMod (gen_heap_strong_init \207\1311c.(fs).(fds)) as ( hFDs HFDpf_eq ) "(Hfdc&Hfd)".
Time Qed.
Time
iMod (gen_heap_strong_init \207\1311c.(fs).(inodes)) as ( hIs HIpf_eq ) "(Hidc&Hi)".
Time
Lemma pickup_end_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) msgs E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Pickup_End uid msgs))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v,
                   \226\140\156\207\131.(messages) !! uid = Some (MPickingUp, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Pickup_End uid msgs)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time
iMod (gen_dir_strong_init \207\1311c.(fs).(dirents)) as ( hP HPpf_eq ) "(Hpc&Hp)".
Time non_err.
Time
iMod (Count_Heap.gen_heap_strong_init (\206\187 s, \207\1311c.(fs).(dirlocks) !! s)) as (
 hL HLpf_eq ) "(Hlc&Hl)".
Time
iMod
 (ghost_var_alloc (A:=discreteC (gset string))
    (dom (gset string) \207\1311c.(fs).(dirents))) as ( hGD ) "(HgdA&Hgd)".
Time -
Time (destruct p as ([], ?); try by iFrame; auto; solve_err).
Time replace 0%Z with O : Z by auto.
Time
iPoseProof
 (Count_Ghost.read_split (A:=discreteC (gset string)) hGD with "Hgd") as
 "(Hgd&Hgdr)".
Time
iMod (ghost_var_alloc (A:=discreteC sliceLockC) \207\1311c.(maillocks)) as ( hGL )
 "(HglA&Hgl)".
Time (set (hFG := FsG _ _ \206\163 hL hD hP hIs hFDs _ hGD)).
Time (set (hGl := GlobalG _ _ _ _ hGL)).
Time (set (hG := GooseG _ _ \206\163 _ hM hFG hGl _)).
Time iPoseProof (eRO.init_exec_inner \207\1311a \207\1311c Hinit hG _) as "H".
Time iExists hG.
Time iModIntro.
Time iIntros "(Hsource1&Hsource2&Hthread)".
Time iFrame.
Time -
Time solve_err.
Time Qed.
Time
Lemma unlock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Unlock uid))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v,
                   \226\140\156\207\131.(messages) !! uid = Some (MLocked, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Unlock uid)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time non_err.
Time -
Time (destruct p as ([], ?); try by iFrame; eauto; solve_err).
Time iMod ("H" with "[-Hgd]") as "Hinner".
Time {
Time iFrame.
Time -
Time solve_err.
Time (edestruct eRO.init_wf as (?, (?, ->)); eauto).
Time Qed.
Time iFrame.
Time iSplitL "Hd".
Time *
Time iPoseProof (@gen_heap_init_to_bigOp _ _ _ _ _ hD with "[Hd]") as "?".
Time
Lemma delete_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid msg (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Delete uid msg))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v body,
                   \226\140\156\207\131.(messages) !! uid = Some (MLocked, v)
                    \226\136\167 v !! msg = Some body\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Delete uid msg)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time {
Time by rewrite Hdpf_eq.
Time }
Time by rewrite big_opM_fmap.
Time non_err.
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
Time -
Time (destruct p as ([], msgs); try by iFrame; eauto; try solve_err).
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
Time iExists _.
Time non_err.
Time *
Time iFrame.
Time eauto.
Time *
Time solve_err.
Time -
Time solve_err.
Time Qed.
Time
Lemma is_opened_step_inv {T} {T2} j K `{LanguageCtx _ T T2 Mail.l K} 
  op (\207\131 : l.(OpState)) E :
  match op with
  | Open => False
  | _ => True
  end
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 K (Call op)
      -\226\136\151 source_ctx
         -\226\136\151 source_state \207\131
            ={E}=\226\136\151 \226\140\156\207\131.(open) = true\226\140\157 \226\136\151 j \226\164\135 K (Call op) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct \207\131.(open) as [| ] eqn:Heq ; last 
 first).
Time -
Time ghost_err.
Time (intros n).
Time left.
Time right.
Time (do 2 eexists).
Time split.
Time {
Time rewrite /reads.
Time rewrite Heq.
Time econstructor.
Time }
Time (simpl).
Time (destruct op; try econstructor).
Time (exfalso; eauto).
Time -
Time by iFrame.
Time Qed.
Time
Lemma is_opened_step_inv' {T} {T1} {T2} j K f `{LanguageCtx _ T1 T2 Mail.l K}
  (op : Op T) (\207\131 : l.(OpState)) E :
  match op with
  | Open => False
  | _ => True
  end
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 K (Bind (Call op) f)
      -\226\136\151 source_ctx
         -\226\136\151 source_state \207\131
            ={E}=\226\136\151 \226\140\156\207\131.(open) = true\226\140\157
                   \226\136\151 j \226\164\135 K (Bind (Call op) f) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct \207\131.(open) as [| ] eqn:Heq ; last 
 first).
Time -
Time ghost_err.
Time (intros n).
Time left.
Time right.
Time (do 2 eexists).
Time split.
Time {
Time rewrite /reads.
Time rewrite Heq.
Time econstructor.
Time }
Time (simpl).
Time (destruct op; try econstructor).
Time (exfalso; eauto).
Time -
Time by iFrame.
Time Qed.
Time
Lemma if_relation_left {A} {B} {T} b (P Q : relation A B T) 
  a o : b = true \226\134\146 P a o \226\134\146 (if b then P else Q) a o.
Time Proof.
Time (intros ->).
Time trivial.
Time Qed.
Time
Lemma opened_step {T} (op : Op T) \207\131 ret :
  \207\131.(open) = true \226\134\146 step_open op \207\131 ret \226\134\146 l.(Proc.step) op \207\131 ret.
Time Proof.
Time (intros Heq Hstep).
Time (destruct ret).
Time -
Time (do 2 eexists).
Time split.
Time {
Time (rewrite /reads; eauto).
Time }
Time rewrite Heq.
Time eauto.
Time -
Time right.
Time (do 2 eexists).
Time split.
Time {
Time (rewrite /reads; eauto).
Time }
Time (rewrite Heq; eauto).
Time Qed.
Time
Lemma deref_step_inv_do {T} {T2} j K `{LanguageCtx _ T T2 Mail.l K} 
  p off (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.PtrDeref p off)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc v,
                   \226\140\156Data.getAlloc p \207\131.(heap) = Some (s, alloc)
                    \226\136\167 lock_available Reader s = Some tt
                      \226\136\167 List.nth_error alloc off = Some v\226\140\157
                   \226\136\151 j \226\164\135 K (Ret v) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time iMod (ghost_step_call _ _ _ _ with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (eapply opened_step; auto).
Time eexists.
Time *
Time (repeat (do 2 eexists; split; non_err)).
Time *
Time (unfold RecordSet.set).
Time (destruct \207\131; eauto).
Time }
Time {
Time eauto.
Time }
Time iExists _.
Time iFrame.
Time (inv_step; eauto).
Time Qed.
Time
Lemma store_start_step_inv_do {T} {T2} j K `{LanguageCtx _ unit T2 Mail.l K}
  p off (x : T) (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.PtrStore p off x Begin)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc,
                   \226\140\156Data.getAlloc p \207\131.(heap) = Some (s, alloc)
                    \226\136\167 lock_acquire Writer s = Some Locked\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs
                               (updDyn p (Locked, alloc))) \207\131).
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
iMod
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; split; non_err)).
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time eauto.
Time (destruct s; simpl in *; try congruence; inv_step; subst; eauto).
Time Qed.
Time
Lemma store_finish_step_inv_do {T} {T2} j K `{LanguageCtx _ unit T2 Mail.l K}
  p off (x : T) xh (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.PtrStore p off x (FinishArgs xh))))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc alloc',
                   \226\140\156Data.getAlloc p \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.list_nth_upd alloc off x = Some alloc'
                      \226\136\167 lock_release Writer s = Some Unlocked\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs
                               (updDyn p (Unlocked, alloc'))) \207\131).
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (non_err; try solve_err).
Time
iMod
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; try split; non_err)).
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time eauto.
Time (destruct s; simpl in *; try congruence).
Time inv_step.
Time eauto.
Time Qed.
Time
Lemma slice_append_step_inv {T} {T2} j K `{LanguageCtx _ _ T2 Mail.l K} 
  p (x : T) (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.SliceAppend p x)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc val,
                   \226\140\156Data.getAlloc p.(slice.ptr) \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.getSliceModel p alloc = Some val
                      \226\136\167 lock_available Writer s = Some tt\226\140\157
                   \226\136\151 j \226\164\135 K (Call (DataOp (Data.SliceAppend p x)))
                     \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time iExists _.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time inv_step.
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma bytes_to_string_step_inv_do {T2} j K `{LanguageCtx _ _ T2 Mail.l K} 
  p (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.BytesToString p)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc val,
                   \226\140\156Data.getAlloc p.(slice.ptr) \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.getSliceModel p alloc = Some val
                      \226\136\167 lock_available Reader s = Some tt\226\140\157
                   \226\136\151 j \226\164\135 K (Ret (bytes_to_string val)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time iExists _.
Time inv_step.
Time iMod (ghost_step_call _ _ _ _ with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (eapply opened_step; auto).
Time eexists.
Time *
Time (repeat (do 2 eexists; split; non_err)).
Time {
Time (unfold Data.getAlloc).
Time rewrite Heq //=.
Time }
Time (repeat (do 2 eexists; try split; non_err)).
Time *
Time (unfold RecordSet.set).
Time (destruct \207\131; eauto).
Time }
Time {
Time solve_ndisj.
Time }
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma lock_release_step_inv_do {T} j K `{LanguageCtx _ _ T Mail.l K} 
  lk m (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.LockRelease lk m)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s s',
                   \226\140\156Data.getAlloc lk \207\131.(heap) = Some (s, tt)
                    \226\136\167 lock_release m s = Some s'\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs (updDyn lk (s', ())))
                            \207\131).
Time Proof.
Time iIntros.
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
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
Time {
Time (simpl; auto).
Time }
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  first).
Time iDestruct "Hroot" as ( n ) "Hmapsto".
Time iFrame.
Time {
Time ghost_err.
Time (intros n).
Time err_start.
Time err_hd.
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time }
Time (destruct p as (?, [])).
Time iExists _.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  first).
Time iFrame "%".
Time {
Time rewrite Count_Ghost.read_split.
Time ghost_err.
Time iDestruct "Hmapsto" as "(?&?)".
Time iFrame.
Time iExists (S n).
Time eauto.
Time Qed.
Time (intros n).
Time err_start.
Time err_cons.
Time {
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time }
Time (simpl).
Time rewrite Heq0.
Time econstructor.
Time }
Time iExists _.
Time eauto.
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
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time
iMod
 (Count_Heap.gen_heap_strong_init
    (\206\187 s,
       ((\206\187 _ : LockStatus * (), (Unlocked, ())) <$> \207\131.(fs).(dirlocks)) !! s))
 as ( hDlocks' Hdlocks'_eq' ) "(Hdlocksc&Hlocks)".
Time
iMod (ghost_var_alloc (A:=discreteC sliceLockC) None) as ( hGl_name )
 "(HglA&Hgl)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; try split; non_err)).
Time {
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time (set (hGl := GlobalG _ _ _ _ hGl_name)).
Time }
Time (simpl).
Time rewrite Heq0.
Time econstructor.
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time
iPoseProof (goose_interp_split_read_dir with "Hmach") as
 "(Hmach&Hroot&Hdom_eq)".
Time eauto.
Time iMod ("Hinv_post" with "[Hm Hgl Hlocks Hroot Hdom_eq]") as "Hinv'".
Time Qed.
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
Time
Lemma lock_acquire_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  lk m (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.LockAcquire lk m)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s,
                   \226\140\156Data.getAlloc lk \207\131.(heap) = Some (s, tt)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (DataOp (Data.LockAcquire lk m)))
                     \226\136\151 source_state \207\131.
Time }
Time iModIntro.
Time iIntros ( \207\131' Hcrash ).
Time Proof.
Time iIntros.
Time
iExists
 (GooseG _ _ _ (@go_invG _ _ _ Hex) hM'
    (eRO.eRD.crash_fsG (@go_fs_inG _ _ _ _) hDlocks' hFds') hGl _).
Time (destruct Hcrash as ([], ((?, ?), (Hput, Hrest)))).
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  first).
Time {
Time ghost_err.
Time (inversion Hput).
Time subst.
Time inv_step.
Time (inversion Hrest; subst).
Time (intros n).
Time err_start.
Time err_hd.
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time }
Time (destruct p as (?, [])).
Time iExists _.
Time iFrame.
Time (simpl).
Time (repeat inv_step).
Time eauto.
Time Qed.
Time
Lemma deliver_start_step_inv_do {T2} j K `{LanguageCtx _ unit T2 Mail.l K}
  uid msg (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Deliver_Start uid msg))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc vs s',
                   \226\140\156Data.getAlloc msg.(slice.ptr) \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.getSliceModel msg alloc = Some vs
                      \226\136\167 lock_acquire Reader s = Some s'\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs
                               (updDyn msg.(slice.ptr) (s', alloc))) \207\131).
Time (inversion H).
Time Proof.
Time iIntros.
Time deex.
Time inv_step.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time inv_step.
Time (inversion H).
Time deex.
Time inv_step.
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (unfold RecordSet.set in *).
Time (simpl).
Time (inversion H).
Time subst.
Time (simpl in *).
Time (repeat deex).
Time (simpl; auto).
Time }
Time (destruct p as (s, alloc)).
Time iExists s , alloc.
Time (non_err; try solve_err).
Time inv_step.
Time subst.
Time iDestruct "Hmach" as "(?&(?&?&?&?&?&?)&?)".
Time (simpl).
Time (unfold RecordSet.set in *).
Time (simpl).
Time
iMod
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time iFrame.
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; try split; non_err)).
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma deliver_end_step_inv {T2} j K `{LanguageCtx _ unit T2 Mail.l K} 
  uid msg (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Deliver_End uid msg))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v s alloc vs s',
                   \226\140\156\207\131.(messages) !! uid = Some v
                    \226\136\167 Data.getAlloc msg.(slice.ptr) \207\131.(heap) =
                      Some (s, alloc)
                      \226\136\167 Data.getSliceModel msg alloc = Some vs
                        \226\136\167 lock_release Reader s = Some s'\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Deliver_End uid msg)) \226\136\151 source_state \207\131.
Time (simpl).
Time Proof.
Time iIntros.
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (\207\131.(messages) !! uid) as [(ms, mbox)| ] eqn:Heq_uid ; last  first).
Time {
Time solve_err.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (Data.getAlloc msg.(slice.ptr) \207\131.(heap))
  as [(s, alloc)| ] eqn:Heq_lookup ; last  first).
Time {
Time ghost_err.
Time (intros n).
Time left.
Time (eapply opened_step; auto).
Time right.
Time (do 2 eexists; split; non_err).
Time right.
Time exists (fresh (dom (gset string) mbox)).
Time (eexists; split).
Time {
Time econstructor.
Time (eapply (not_elem_of_dom (D:=gset string)), is_fresh).
Time }
Time left.
Time rewrite /readUnlockSlice.
Time err_hd.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (lock_release Reader s) as [?| ] eqn:Heq_avail ; last  first).
Time {
Time ghost_err.
Time iFrame.
Time (intros n).
Time left.
Time (eapply opened_step; auto).
Time right.
Time (do 2 eexists; split; non_err).
Time right.
Time exists (fresh (dom (gset string) mbox)).
Time (eexists; split).
Time {
Time econstructor.
Time (eapply (not_elem_of_dom (D:=gset string)), is_fresh).
Time }
Time left.
Time (err_cons; err_hd).
Time rewrite dom_fmap_L.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (Data.getSliceModel msg alloc) as [alloc'| ] eqn:Heq_upd ; last 
 first).
Time {
Time ghost_err.
Time auto.
Time iFrame.
Time (intros n).
Time left.
Time (eapply opened_step; auto).
Time right.
Time (do 2 eexists; split; non_err).
Time right.
Time exists (fresh (dom (gset string) mbox)).
Time (eexists; split).
Time {
Time econstructor.
Time (eapply (not_elem_of_dom (D:=gset string)), is_fresh).
Time }
Time err3.
Time eauto.
Time }
Time iFrame.
Time Qed.
Time iExists _ , _ , _ , _ , _.
Time (iPureIntro; eauto).
Time Qed.
Time End api_lemmas.
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
iMod (ghost_var_alloc (A:=discreteC sliceLockC) None) as ( hGl_name )
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
iMod (ghost_var_alloc (A:=discreteC sliceLockC) None) as ( hGl''_name )
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
