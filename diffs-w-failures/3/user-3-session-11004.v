Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement.
Time Require Import StatDb.Impl ExMach.WeakestPre ExMach.RefinementAdequacy.
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
Time {
Time (apply auth_both_valid; done).
Time }
Time Qed.
Time
Lemma add_refinement {T} j K `{LanguageCtx DB.Op unit T DB.l K} 
  n :
  {{{ j \226\164\135 K (Call (DB.Add n)) \226\136\151 Registered \226\136\151 DBInv }}} 
  add n {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&#Hsource_inv&Hinv) H\206\166".
Time iDestruct "Hinv" as ( \206\1791 \206\1792 ) "(#Hlockinv&#Hinv)".
Time (wp_lock "(Hlocked&HDB)").
Time iDestruct "HDB" as ( l ) "(Hsource_tok&Hsum&Hcount)".
Time (do 3 wp_step).
Time wp_bind.
Time iInv "Hinv" as ( l' ) ">(Htok&Hsource)".
Time
iDestruct (own_valid_2 with "Htok Hsource_tok") as %
 [<-%leibniz_equiv%Excl_included _]%auth_both_valid.
Time
iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
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
iMod
 (own_update_2 _ _ _ (\226\151\143 Excl' (n :: l) \226\139\133 \226\151\175 Excl' (n :: l))
 with "Htok Hsource_tok") as "[Hfull ?]".
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
Time wp_ret.
Time by iApply "H\206\166".
Time Qed.
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
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time rewrite /recv_triple_type.
Time (intros).
Time iIntros "((#Hctx&#Hinv)&_&_)".
Time wp_ret.
Time iInv "Hinv" as ( l ) ">(?&?&?&?)" "_".
Time rewrite /source_inv.
Time iMod init_ghost_list as ( \206\1792 ) "[Hauth Hfrag]".
Time iApply (fupd_mask_weaken _ _).
Time {
Time solve_ndisj.
Time }
Time iExists l , nil.
Time iFrame.
Time iSplitL "".
Time {
Time (iPureIntro; econstructor).
Time }
Time iClear "Hctx Hinv".
Time iIntros ( ? ? ? ) "(#Hctx&Hstate)".
Time rewrite /DBLockInv.
Time iModIntro.
Time iExists _.
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
Time iDestruct "Hopen" as ( l ) "(?&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iModIntro.
Time iExists l.
Time iFrame.
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
Time iFrame.
Time Qed.
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time rewrite /crash_inner_inv_type.
Time (intros).
Time iIntros "H".
Time iDestruct "H" as "(Hinv&#Hsrc)".
Time iDestruct "Hinv" as ( invG ) "Hinv".
Time rewrite /DBCrashInner /CrashInv.
Time iDestruct "Hinv" as ( l ) "(?&?)".
Time iMod (@inv_alloc \206\163 exm_invG iN _ DBCrashInner with "[-]").
Time {
Time iNext.
Time (iExists l; iFrame).
Time }
Time iModIntro.
Time iFrame.
Time iExists tt.
Time iFrame "Hsrc".
Time Qed.
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
Time iDestruct "H" as ( v ) "(?&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time (iExists _ , nil; eauto).
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by eauto).
Time iIntros ( ? ? ? ? ) "(?&Hstate&Hmem)".
Time iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
Time iMod init_ghost_list as ( \206\1792' ) "[Hauth Hfrag]".
Time iModIntro.
Time iExists O.
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
