Time From iris.algebra Require Import auth gmap frac agree.
Time Require Import ExMach.Adequacy.
Time Import ExMach.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time Import WeakestPre.
Time Module Type exmach_refinement_type.
Time Context (OpT : Type \226\134\146 Type).
Time Context (\206\155a : Layer OpT).
Time Context (impl : LayerImpl ExMach.Op OpT).
Time Context (\206\163 : gFunctors).
Time Notation compile_op := (compile_op impl).
Time Notation compile_rec := (compile_rec impl).
Time Notation compile_seq := (compile_seq impl).
Time Notation compile := (compile impl).
Time Notation recover := (recover impl).
Time Notation compile_proc_seq := (compile_proc_seq impl).
Time Context `{CFG : cfgPreG OpT \206\155a \206\163} `{HEX : exmachPreG \206\163}.
Time Context `{INV : Adequacy.invPreG \206\163}.
Time
Context `{REG : inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))}.
Time
Context (crash_inner : forall {_ : @cfgG OpT \206\155a \206\163} {_ : exmachG \206\163}, iProp \206\163).
Time
Context (exec_inner : forall {_ : @cfgG OpT \206\155a \206\163} {_ : exmachG \206\163}, iProp \206\163).
Time
Context (crash_param : forall (_ : @cfgG OpT \206\155a \206\163) (_ : exmachG \206\163), Type).
Time
Context
 (crash_inv : forall {H1 : @cfgG OpT \206\155a \206\163} {H2 : exmachG \206\163},
              @crash_param _ H2 \226\134\146 iProp \206\163).
Time
Context
 (crash_starter : forall {H1 : @cfgG OpT \206\155a \206\163} {H2 : exmachG \206\163},
                  @crash_param _ H2 \226\134\146 iProp \206\163).
Time
Context (exec_inv : forall {_ : @cfgG OpT \206\155a \206\163} {_ : exmachG \206\163}, iProp \206\163).
Time Context (E : coPset).
Time Context (recv : proc ExMach.Op unit).
Time Context (init_absr : \206\155a.(OpState) \226\134\146 ExMach.State \226\134\146 Prop).
Time End exmach_refinement_type.
Time Module exmach_refinement_definitions (eRT: exmach_refinement_type).
Time Import eRT.
Time
Definition recv_triple_type :=
  forall H1 H2 param,
  @crash_inv H1 H2 param \226\136\151 Registered \226\136\151 @crash_starter H1 H2 param
  \226\138\162 WP recv
    @ NotStuck; \226\138\164 {{ v, |={\226\138\164,E}=> \226\136\131 \207\1312a \207\1312a',
                                    source_state \207\1312a
                                    \226\136\151 \226\140\156\206\155a.(crash_step) \207\1312a (Val \207\1312a' tt)\226\140\157
                                      \226\136\151 (\226\136\128 `{Hcfg' : cfgG OpT \206\155a \206\163} 
                                           (Hinv' : 
                                            invG \206\163) 
                                           tr',
                                           source_ctx \226\136\151 source_state \207\1312a'
                                           ={\226\138\164}=\226\136\151 
                                           exec_inner Hcfg'
                                             (ExMachG \206\163 Hinv' exm_mem_inG
                                                (next_leased_heapG
                                                 (hG:=exm_disk_inG)) tr')) }}.
Time
Definition refinement_op_triples_type :=
  forall H1 H2 T1 T2 j K `{LanguageCtx OpT T1 T2 \206\155a K} (op : OpT T1),
  j \226\164\135 K (Call op) \226\136\151 Registered \226\136\151 @exec_inv H1 H2
  \226\138\162 WP compile (Call op) {{ v, j \226\164\135 K (Ret v) \226\136\151 Registered }}.
Time
Definition init_exec_inner_type :=
  \226\136\128 \207\1311a \207\1311c,
    init_absr \207\1311a \207\1311c
    \226\134\146 \226\136\128 `{Hex : exmachG \206\163} `{Hcfg : cfgG OpT \206\155a \206\163},
        ([\226\136\151 map] i\226\134\166v \226\136\136 mem_state \207\1311c, i m\226\134\166 v)
        \226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 disk_state \207\1311c, i d\226\134\166 v \226\136\151 lease i v)
          \226\136\151 source_ctx \226\136\151 source_state \207\1311a ={\226\138\164}=\226\136\151 exec_inner _ _.
Time
Definition exec_inv_preserve_crash_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    exec_inv Hcfg Hex
    ={\226\138\164,E}=\226\136\151 \226\136\128 Hmem' Hreg',
               let Hex :=
                 ExMachG \206\163 exm_invG Hmem'
                   (next_leased_heapG (hG:=exm_disk_inG)) Hreg' in
               ([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i m\226\134\166 v) ={E}=\226\136\151 crash_inner Hcfg Hex.
Time
Definition crash_inv_preserve_crash_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163) param,
    crash_inv Hcfg Hex param
    ={\226\138\164,E}=\226\136\151 \226\136\128 Hmem' Hreg',
               let Hex :=
                 ExMachG \206\163 exm_invG Hmem'
                   (next_leased_heapG (hG:=exm_disk_inG)) Hreg' in
               ([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i m\226\134\166 v) ={E}=\226\136\151 crash_inner Hcfg Hex.
Time
Definition crash_inner_inv_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    (\226\136\131 Hinv,
       crash_inner Hcfg
         (ExMachG \206\163 Hinv exm_mem_inG exm_disk_inG exm_treg_inG)) \226\136\151 source_ctx
    ={\226\138\164}=\226\136\151 \226\136\131 param, crash_inv Hcfg Hex param \226\136\151 crash_starter Hcfg Hex param.
Time
Definition exec_inner_inv_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    (\226\136\131 Hinv,
       exec_inner Hcfg (ExMachG \206\163 Hinv exm_mem_inG exm_disk_inG exm_treg_inG))
    \226\136\151 source_ctx ={\226\138\164}=\226\136\151 exec_inv Hcfg Hex.
Time
Definition exec_inv_preserve_finish_type :=
  (\226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
     AllDone
     -\226\136\151 exec_inv Hcfg Hex
        ={\226\138\164,E}=\226\136\151 \226\136\131 \207\1312a \207\1312a' : \206\155a.(OpState),
                   source_state \207\1312a
                   \226\136\151 \226\140\156\206\155a.(finish_step) \207\1312a (Val \207\1312a' tt)\226\140\157
                     \226\136\151 (\226\136\128 `{Hcfg' : cfgG OpT \206\155a \206\163} 
                          (Hinv' : invG \206\163) Hmem' Hreg',
                          let Hex :=
                            ExMachG \206\163 Hinv' Hmem'
                              (next_leased_heapG (hG:=exm_disk_inG)) Hreg' in
                          source_ctx
                          \226\136\151 source_state \207\1312a'
                            \226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i m\226\134\166 v)
                          ={\226\138\164}=\226\136\151 exec_inner Hcfg' Hex))%I.
Time End exmach_refinement_definitions.
Time Module Type exmach_refinement_obligations (eRT: exmach_refinement_type).
Time Module eRD:=  exmach_refinement_definitions eRT.
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
Time Context (init_wf : \226\136\128 \207\1311a \207\1311c, init_absr \207\1311a \207\1311c \226\134\146 state_wf \207\1311c).
Time Context (refinement_op_triples : refinement_op_triples_type).
Time Context (init_exec_inner : init_exec_inner_type).
Time Context (exec_inv_preserve_crash : exec_inv_preserve_crash_type).
Time Context (crash_inv_preserve_crash : crash_inv_preserve_crash_type).
Time Context (exec_inner_inv : exec_inner_inv_type).
Time Context (crash_inner_inv : crash_inner_inv_type).
Time Context (exec_inv_preserve_finish : exec_inv_preserve_finish_type).
Time End exmach_refinement_obligations.
Time
Module exmach_refinement (eRT: exmach_refinement_type)
  (eRO: exmach_refinement_obligations eRT).
Time Module RT<: refinement_type.
Time Import eRT.
Time Definition OpC := ExMach.Op.
Time Definition \206\155c := ExMach.l.
Time Definition OpT := OpT.
Time Definition \206\155a := \206\155a.
Time Definition impl := impl.
Time Definition exmachG := exmachG.
Time Definition \206\163 := \206\163.
Time Definition CFG := CFG.
Time Definition INV := INV.
Time Definition REG := REG.
Time Definition Hinstance := @exmachG_irisG.
Time Definition Hinstance_reg := @exm_treg_inG.
Time
Definition set_inv_reg Hex Hinv Hreg :=
  ExMachG \206\163 Hinv (@exm_mem_inG _ Hex) (@exm_disk_inG _ Hex) Hreg.
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
Time Definition refinement_op_triples := eRO.refinement_op_triples.
Time Definition exec_inv_source_ctx := eRO.exec_inv_source_ctx.
Time
Lemma set_inv_reg_spec0 :
  \226\136\128 Hex,
    set_inv_reg Hex (Hinstance \206\163 Hex).(@iris_invG OpC (State \206\155c) \206\163)
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
Time
Lemma register_spec `{WeakestPre.exmachG \206\163} :
  \226\136\131 Interp : OpState \206\155c \226\134\146 iProp \206\163,
    (\226\136\128 n \207\131,
       @state_interp _ _ _ (Hinstance _ _) (n, \207\131)
       -\226\136\151 thread_count_interp n \226\136\151 Interp \207\131)
    \226\136\167 (\226\136\128 n \207\131, thread_count_interp n \226\136\151 Interp \207\131 -\226\136\151 state_interp (n, \207\131)).
Time Proof.
Time eexists.
Time (split; eauto using thread_reg1, thread_reg2).
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
Time iExists (ExMachG \206\163 _ _ next_leased_heapG _).
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
iMod (gen_heap_strong_init (mem_state \207\1311c)) as ( hM Hmpf_eq ) "(Hmc&Hm)".
Time
iMod (leased_heap_strong_init (disk_state \207\1311c)) as ( hD Hdpf_eq ) "(Hdc&Hd)".
Time
iPoseProof (eRO.init_exec_inner \207\1311a \207\1311c Hinit (ExMachG \206\163 _ hM hD _) _) as "H".
Time iModIntro.
Time iExists (ExMachG \206\163 _ hM hD _).
Time iIntros "(Hsource1&Hsource2&Hthread)".
Time iMod ("H" with "[Hm Hd Hsource1 Hsource2]") as "Hinner".
Time {
Time iFrame.
Time iSplitL "Hm".
Time {
Time rewrite -Hmpf_eq.
Time (iApply mem_init_to_bigOp; auto).
Time }
Time {
Time iApply (big_sepM_mono with "Hd").
Time iIntros ( ? ? ? ) "(?&?&?)".
Time iFrame.
Time }
Time }
Time iModIntro.
Time iFrame.
Time iExists _ , _.
Time iFrame.
Time (iPureIntro; edestruct eRO.init_wf as (Hwf1, Hwf2); eauto).
Time (split_and !; eauto; intros i).
Time *
Time (destruct (Hwf1 i); intuition).
Time *
Time (destruct (Hwf2 i); intuition).
Time Qed.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time rewrite /exec_inv_preserve_crash_type.
Time iIntros ( ? ? ) "Hinv".
Time iPoseProof (eRO.exec_inv_preserve_crash with "Hinv") as "Hinv_post".
Time iMod (gen_heap_strong_init init_zero) as ( hM Hmpf_eq ) "(Hmc&Hm)".
Time iMod "Hinv_post" as "Hinv_post".
Time iModIntro.
Time iIntros ( ? n \207\131 ).
Time iMod ("Hinv_post" with "[Hm]") as "Hinv_post".
Time {
Time rewrite -Hmpf_eq.
Time (iApply @mem_init_to_bigOp; auto).
Time }
Time iIntros "(Hmach&Hthread)".
Time iModIntro.
Time iIntros ( \207\131' Hcrash ).
Time
iExists
 (ExMachG \206\163 (@exm_invG _ Hex) hM
    (next_leased_heapG (hG:=@exm_disk_inG _ Hex)) 
    (@exm_treg_inG _ Hex)).
Time iFrame.
Time iDestruct "Hmach" as "(?&Hdisk)".
Time (inversion Hcrash).
Time subst.
Time iDestruct "Hdisk" as ( ? ? ) "(?&?&%&%&%&%)".
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  done).
Time iExists _ , _.
Time iFrame.
Time (iPureIntro; split_and !; [ auto | auto |  | assumption ]).
Time (intros ? Hsome).
Time (apply not_le; intros Hge).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite init_zero_lookup_ge_None in 
 {} Hsome ; last  by lia).
Time (apply is_Some_None in Hsome; auto).
Time Qed.
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time Proof.
Time rewrite /crash_inv_preserve_crash_type.
Time iIntros ( ? ? ? ) "Hinv".
Time iPoseProof (eRO.crash_inv_preserve_crash with "Hinv") as "Hinv_post".
Time iMod (gen_heap_strong_init init_zero) as ( hM Hmpf_eq ) "(Hmc&Hm)".
Time iMod "Hinv_post" as "Hinv_post".
Time iModIntro.
Time iIntros ( ? n \207\131 ).
Time iMod ("Hinv_post" with "[Hm]") as "Hinv_post".
Time {
Time rewrite -Hmpf_eq.
Time (iApply @mem_init_to_bigOp; auto).
Time }
Time iIntros "(Hmach&Hthread)".
Time iModIntro.
Time iIntros ( \207\131' Hcrash ).
Time
iExists
 (ExMachG \206\163 (@exm_invG _ Hex) hM
    (next_leased_heapG (hG:=@exm_disk_inG _ Hex)) 
    (@exm_treg_inG _ Hex)).
Time iFrame.
Time iDestruct "Hmach" as "(?&Hdisk)".
Time (inversion Hcrash).
Time subst.
Time iDestruct "Hdisk" as ( ? ? ) "(?&?&%&%&%&%)".
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  done).
Time iExists _ , _.
Time iFrame.
Time (iPureIntro; split_and !; [ auto | auto |  | assumption ]).
Time (intros ? Hsome).
Time (apply not_le; intros Hge).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite init_zero_lookup_ge_None in 
 {} Hsome ; last  by lia).
Time (apply is_Some_None in Hsome; auto).
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
Time iIntros ( ? ? ? Hfinish ? ? ) "((?&Hdisk)&?)".
Time (inversion Hfinish).
Time subst.
Time iMod (gen_heap_strong_init init_zero) as ( hM Hmpf_eq ) "(Hmc&Hm)".
Time iDestruct "Hdisk" as ( ? ? ) "(_&?&%&%&%&%)".
Time iFrame.
Time iModIntro.
Time
iExists
 (ExMachG \206\163 (@exm_invG _ Hex) hM
    (next_leased_heapG (hG:=@exm_disk_inG _ Hex)) 
    (@exm_treg_inG _ Hex)).
Time iSplitR "Hinv_post Hm".
Time {
Time iFrame.
Time iExists init_zero , _.
Time iFrame.
Time (iPureIntro; split_and !; [ auto | auto |  | assumption ]).
Time (intros ? Hsome).
Time (apply not_le; intros Hge).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite init_zero_lookup_ge_None in 
 {} Hsome ; last  by lia).
Time (apply is_Some_None in Hsome; auto).
Time }
Time iIntros "Hstate".
Time iSpecialize ("Hinv_post" with "[Hstate Hm]").
Time {
Time iFrame.
Time iDestruct "Hstate" as "(?&?)".
Time iFrame.
Time rewrite -Hmpf_eq.
Time (iApply @mem_init_to_bigOp; auto).
Time }
Time eauto.
Time Qed.
Time End RO.
Time Module R:=  refinement RT RO.
Time Export R.
Time End exmach_refinement.
