Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement.
Time
Require Import AtomicPairAPI AtomicPair.ImplShadow ExMach.WeakestPre
  ExMach.RefinementAdequacy.
Time Require Import AtomicPair.Helpers.
Time Unset Implicit Arguments.
Time Existing Instance from_exist_left_sep_later.
Time #[local]
Ltac
 destruct_einner H :=
  iDestruct H as ( ? (?, ?) (?, ?) ) ">(Hsource&Hmap)"; iDestruct "Hmap" as
   "(Hptr&Hcase)"; repeat unify_lease; repeat unify_ghost.
Time Set Default Proof Using "Type".
Time Section refinement_triples.
Time
Context `{!exmachG \206\163} `{lockG \206\163} `{!@cfgG AtomicPair.Op AtomicPair.l \206\163}
 `{!inG \206\163 (authR (optionUR (exclR (prodO natO natO))))}
 `{!inG \206\163 (authR (optionUR (exclR natO)))}.
Time Import ExMach.
Time
Definition ptr_map (ptr_val : nat) (pcurr : nat * nat)
  (pother : nat * nat) :=
  (ptr_addr d\226\134\166 ptr_val
   \226\136\151 (read_addrs ptr_val).1 d\226\134\166 pcurr.1
     \226\136\151 (read_addrs ptr_val).2 d\226\134\166 pcurr.2
       \226\136\151 (write_addrs ptr_val).1 d\226\134\166 pother.1
         \226\136\151 (write_addrs ptr_val).2 d\226\134\166 pother.2)%I.
Time
Definition ExecInner :=
  (\226\136\131 (ptr_val : nat) (pcurr : nat * nat) (pother : nat * nat),
     source_state pcurr \226\136\151 ptr_map ptr_val pcurr pother)%I.
Time
Definition lease_map (ptr_val : nat) (pcurr : nat * nat)
  (pother : nat * nat) :=
  (lease ptr_addr ptr_val
   \226\136\151 lease (read_addrs ptr_val).1 pcurr.1
     \226\136\151 lease (read_addrs ptr_val).2 pcurr.2
       \226\136\151 lease (write_addrs ptr_val).1 pother.1
         \226\136\151 lease (write_addrs ptr_val).2 pother.2)%I.
Time
Definition ExecLockInv :=
  (\226\136\131 (ptr_val : nat) (pcurr : nat * nat) pother,
     lease_map ptr_val pcurr pother)%I.
Time
Definition CrashInner :=
  (\226\136\131 (ptr_val : nat) (pcurr : nat * nat) pother,
     source_state pcurr
     \226\136\151 ptr_map ptr_val pcurr pother
       \226\136\151 lease_map ptr_val pcurr pother \226\136\151 lock_addr m\226\134\166 0)%I.
Time Definition lN : namespace := nroot.@"lock".
Time Definition iN : namespace := nroot.@"inner".
Time
Definition ExecInv :=
  (source_ctx
   \226\136\151 (\226\136\131 \206\179lock, is_lock lN \206\179lock lock_addr ExecLockInv \226\136\151 inv iN ExecInner))%I.
Time Definition CrashInv := (source_ctx \226\136\151 inv iN CrashInner)%I.
Time
Lemma read_of_swap ptr_val :
  read_addrs (swap_ptr ptr_val) = write_addrs ptr_val.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct ptr_val =>//=).
Time Qed.
Time
Lemma write_of_swap ptr_val :
  write_addrs (swap_ptr ptr_val) = read_addrs ptr_val.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct ptr_val =>//=).
Time Qed.
Time
Lemma write_refinement {T} j K
  `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} 
  p :
  {{{ j \226\164\135 K (Call (AtomicPair.Write p)) \226\136\151 Registered \226\136\151 ExecInv }}} 
  write p {{{ v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&#Hsource_inv&Hinv) H\206\166".
Time iDestruct "Hinv" as ( \206\179lock ) "(#Hlockinv&#Hinv)".
Time (wp_lock "(Hlocked&HEL)").
Time
iDestruct "HEL" as ( ptr_val pcurr pother )
 "(Hptr_ghost&Hpair1_ghost&Hpair2_ghost&Hother1_ghost&Hother2_ghost)".
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_einner "H").
Time wp_step.
Time (iModIntro; iExists _ , _ , _; iFrame).
Time (destruct p as (new_fst, new_snd)).
Time wp_bind.
Time (iFastInv "Hinv" "H").
Time (destruct_einner "H").
Time iDestruct "Hcase" as "(?&?&Hfst&Hsnd)".
Time wp_step.
Time iExists ptr_val.
Time (simpl).
Time (iExists _ , (new_fst, _); iFrame).
Time (simpl).
Time iFrame.
Time iModIntro.
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_einner "H").
Time iDestruct "Hcase" as "(Ho1&Ho2&Hfst&Hsnd)".
Time wp_step.
Time (iModIntro; iExists _ , _; iFrame).
Time (simpl).
Time iExists (_, _).
Time iFrame.
Time wp_bind.
Time (iFastInv "Hinv" "H").
Time (destruct_einner "H").
Time iDestruct "Hcase" as "(Ho1&Ho2&Hfst'&Hsnd')".
Time (repeat unify_lease).
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
Time iExists (swap_ptr ptr_val).
Time (iExists _ , _; iFrame).
Time (rewrite ?read_of_swap ?write_of_swap; iFrame).
Time iModIntro.
Time (wp_unlock "[-H\206\166 Hreg Hj]"; iFrame).
Time {
Time iExists _ , (_, _) , (_, _).
Time iFrame.
Time (rewrite ?read_of_swap ?write_of_swap; iFrame).
Time }
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma read_refinement {T} j K
  `{LanguageCtx AtomicPair.Op (nat * nat) T AtomicPair.l K} :
  {{{ j \226\164\135 K (Call AtomicPair.Read) \226\136\151 Registered \226\136\151 ExecInv }}} read {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&#Hsource_inv&Hinv) H\206\166".
Time iDestruct "Hinv" as ( \206\179lock ) "(#Hlockinv&#Hinv)".
Time (wp_lock "(Hlocked&HEL)").
Time
iDestruct "HEL" as ( ptr_val pcurr pother )
 "(Hptr_ghost&Hpair1_ghost&Hpair2_ghost&Hother1_ghost&Hother2_ghost)".
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_einner "H").
Time wp_step.
Time (iModIntro; iExists _ , _ , _; iFrame).
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_einner "H").
Time iDestruct "Hcase" as "(Hfst&Hsnd&?&?)".
Time (simpl).
Time (repeat unify_lease).
Time wp_step.
Time (iModIntro; iExists _ , (_, _) , (_, _); iFrame).
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_einner "H").
Time iDestruct "Hcase" as "(Hfst&Hsnd&?&?)".
Time (simpl).
Time (repeat unify_lease).
Time (repeat unify_lease).
Time wp_step.
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
Time (iModIntro; iExists _ , (_, _) , (_, _); iFrame).
Time wp_bind.
Time (wp_unlock "[-H\206\166 Hreg Hj]").
Time {
Time iExists _ , _ , _.
Time iFrame.
Time }
Time wp_ret.
Time (iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma init_mem_split :
  (([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i m\226\134\166 v) -\226\136\151 lock_addr m\226\134\166 0)%I.
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
Time iDestruct "Hmem" as "(?&_)".
Time iFrame.
Time Qed.
Time
Lemma init_disk_split :
  (([\226\136\151 map] i\226\134\166v \226\136\136 init_zero, i d\226\134\166 v \226\136\151 lease i v)
   -\226\136\151 (ptr_addr d\226\134\166 0
       \226\136\151 copy0_fst d\226\134\166 0 \226\136\151 copy0_snd d\226\134\166 0 \226\136\151 copy1_fst d\226\134\166 0 \226\136\151 copy1_snd d\226\134\166 0)
      \226\136\151 lease ptr_addr 0
        \226\136\151 lease copy0_fst 0
          \226\136\151 lease copy0_snd 0 \226\136\151 lease copy1_fst 0 \226\136\151 lease copy1_snd 0)%I.
Time Proof.
Time iIntros "Hdisk".
Time iPoseProof (disk_ptr_iter_split_aux O 4 with "Hdisk") as "H".
Time {
Time rewrite /size.
Time lia.
Time }
Time iDestruct "H" as "(H&_)".
Time (repeat iDestruct "H" as "((?&?)&H)").
Time iFrame.
Time Qed.
Time End refinement_triples.
Time Module sRT<: exmach_refinement_type.
Time
Definition helper\206\163 : gFunctors :=
  #[ GFunctor (authR (optionUR (exclR natO)));
  GFunctor (authR (optionUR (exclR (prodO natO natO))))].
Time
Instance subG_helper\206\163 :
 (subG helper\206\163 \206\163 \226\134\146 inG \206\163 (authR (optionUR (exclR natO)))).
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
Time
Definition init_absr \207\1311a \207\1311c :=
  ExMach.l.(initP) \207\1311c \226\136\167 AtomicPair.l.(initP) \207\1311a.
Time Definition OpT := AtomicPair.Op.
Time Definition \206\155a := AtomicPair.l.
Time Definition impl := ImplShadow.impl.
Time Existing Instance subG_cfgPreG.
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
Time Qed.
Time #[global]Instance inG_inst2 : (inG \206\163 (authR (optionUR (exclR natO)))).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance inG_inst3 : (lockG \206\163).
Time Proof.
Time (apply _).
Time Qed.
Time Definition exec_inv := fun H1 H2 => (@ExecInv \206\163 H2 _ H1)%I.
Time
Definition exec_inner :=
  fun H1 H2 =>
  (\226\136\131 v, lock_addr m\226\134\166 v \226\136\151 (\226\140\156v = 0\226\140\157 -\226\136\151 @ExecLockInv \206\163 H2) \226\136\151 @ExecInner \206\163 H2 H1)%I.
Time
Definition crash_param := fun (_ : @cfgG OpT \206\155a \206\163) (_ : exmachG \206\163) => unit.
Time
Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv \206\163 H2 H1.
Time
Definition crash_starter :=
  fun H1 H2 (_ : crash_param H1 H2) => True%I : iProp \206\163.
Time Definition crash_inner := fun H1 H2 => (@CrashInner \206\163 H2 H1)%I.
Time Definition E := nclose sourceN.
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
Time Lemma exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx.
Time Proof.
Time (iIntros ( ? ? ) "(?&?)"; eauto).
Time Qed.
Time
Lemma ptr_map_next {H : exmachG \206\163} Hinv Hmem Hreg 
  ptr_val curr other :
  ptr_map ptr_val curr other
  ==\226\136\151 let Hex :=
        ExMachG \206\163 Hinv Hmem (next_leased_heapG (hG:=exm_disk_inG)) Hreg in
      ptr_map ptr_val curr other \226\136\151 lease_map ptr_val curr other.
Time Proof.
Time iIntros "(Hptr&Ho1&Ho2&Hc1&Hc2)".
Time by repeat iMod (disk_next with "[$]") as "($&$)".
Time Qed.
Time Lemma recv_triple : recv_triple_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "((#Hctx&#Hinv)&_)".
Time wp_ret.
Time iInv "Hinv" as ( ptr_val pcurr pother ) ">(?&Hcase&Hlease&?)" "_".
Time iApply (fupd_mask_weaken _ _).
Time {
Time solve_ndisj.
Time }
Time iExists pcurr , pcurr.
Time iFrame.
Time iSplitL "".
Time {
Time (iPureIntro; econstructor).
Time }
Time iClear "Hctx Hinv".
Time iIntros ( ? ? ? ) "(#Hctx&Hstate)".
Time iMod (ptr_map_next with "Hcase") as "(Hp&Hl)".
Time iExists 0.
Time iFrame.
Time (iSplitL "Hl"; iModIntro; iIntros; iExists _ , _ , _; iFrame).
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
Time (red).
Time (intros ? ? (H, Hinit) ? ?).
Time (inversion H).
Time (inversion Hinit).
Time subst.
Time iIntros "(Hmem&Hdisk&#?&Hstate)".
Time iPoseProof (init_mem_split with "Hmem") as "?".
Time iPoseProof (init_disk_split with "Hdisk") as "(Hd&Hl)".
Time iModIntro.
Time iExists _.
Time iFrame.
Time iSplitL "Hl".
Time -
Time iDestruct "Hl" as "(?&?&?&?&?)".
Time iIntros "_".
Time iExists 0 , (_, _) , (_, _).
Time iFrame.
Time -
Time iDestruct "Hd" as "(?&?&?&?&?)".
Time iExists 0 , (_, _) , (_, _).
Time iFrame.
Time Qed.
Time Lemma exec_inv_preserve_crash : exec_inv_preserve_crash_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "(#Hctx&#Hinv)".
Time iDestruct "Hinv" as ( \206\179lock ) "(#Hlock&#Hinv)".
Time iInv "Hinv" as "Hopen" "_".
Time (destruct_einner "Hopen").
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iPoseProof (@init_mem_split with "Hmem") as "?".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (ptr_map_next with "[Hptr Hcase]") as
 "(?&?)" ; first  by iFrame).
Time iModIntro.
Time iExists _ , (_, _) , (_, _).
Time iFrame.
Time Qed.
Time Lemma crash_inv_preserve_crash : crash_inv_preserve_crash_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "(#Hctx&#Hinv)".
Time iInv "Hinv" as ">Hopen" "_".
Time iDestruct "Hopen" as ( ? (?, ?) (?, ?) ) "(?&Hcase&_)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time iIntros ( ? ? ) "Hmem".
Time iMod (ptr_map_next with "Hcase") as "(?&?)".
Time iModIntro.
Time iExists _ , (_, _) , (_, _).
Time iFrame.
Time iPoseProof (@init_mem_split with "Hmem") as "?".
Time iFrame.
Time Qed.
Time Lemma crash_inner_inv : crash_inner_inv_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "(Hinv&#Hsrc)".
Time iDestruct "Hinv" as ( invG ) "Hinv".
Time iDestruct "Hinv" as ( ? ? ? ) "(?&?&?)".
Time iMod (@inv_alloc \206\163 exm_invG iN _ CrashInner with "[-]").
Time {
Time iNext.
Time (iExists _ , _ , _; iFrame).
Time }
Time iModIntro.
Time iFrame.
Time iExists tt.
Time iFrame "Hsrc".
Time Qed.
Time Lemma exec_inner_inv : exec_inner_inv_type.
Time Proof.
Time (red).
Time (intros).
Time iIntros "(Hinv&#Hsrc)".
Time iDestruct "Hinv" as ( invG v ) "Hinv".
Time iDestruct "Hinv" as "(?&Hinv)".
Time iDestruct "Hinv" as "(Hlock&Hinner)".
Time
iMod
 (@lock_init \206\163 (ExMachG _ exm_invG exm_mem_inG exm_disk_inG _) _ lN lock_addr
    _ ExecLockInv with "[$] [-Hinner]") as ( \206\179lock ) "H".
Time {
Time iFrame.
Time }
Time iMod (@inv_alloc \206\163 exm_invG iN _ ExecInner with "[Hinner]").
Time {
Time iFrame.
Time }
Time iModIntro.
Time iFrame "Hsrc".
Time iExists _.
Time iFrame.
Time Qed.
Time Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
Time Proof.
Time iIntros ( ? ? ) "? (?&H)".
Time iDestruct "H" as ( ? ) "(Hlock&Hinv)".
Time iInv "Hinv" as "H" "_".
Time iDestruct "H" as ( ptr (n1, n2) (n1', n2') ) ">(Hsource&Hmap)".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (lock_crack with "Hlock") as ">H" ;
 first  by solve_ndisj).
Time iDestruct "H" as ( v ) "(?&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 solve_ndisj).
Time (iExists _ , _; iFrame).
Time iSplitL "".
Time {
Time iPureIntro.
Time econstructor.
Time }
Time iIntros ( ? ? ? ? ) "(?&?&Hmem)".
Time iMod (ptr_map_next with "Hmap") as "(Hp&Hl)".
Time iPoseProof (@init_mem_split with "Hmem") as "?".
Time iExists _.
Time iFrame.
Time rewrite /ExecLockInv.
Time (iSplitL "Hl"; iModIntro; iIntros; iExists _ , (_, _) , (_, _); iFrame).
Time Qed.
Time End sRO.
Time Module sR:=  exmach_refinement sRT sRO.
Time Import sR.
Time
Lemma exmach_crash_refinement_seq {T} \207\1311c \207\1311a (es : proc_seq AtomicPair.Op T)
  :
  sRT.init_absr \207\1311a \207\1311c
  \226\134\146 wf_client_seq es
    \226\134\146 \194\172 proc_exec_seq AtomicPair.l es (rec_singleton (Ret ())) (1, \207\1311a) Err
      \226\134\146 \226\136\128 \207\1312c res,
          proc_exec_seq ExMach.l (compile_proc_seq ImplShadow.impl es)
            (rec_singleton recv) (1, \207\1311c) (Val \207\1312c res)
          \226\134\146 \226\136\131 \207\1312a,
              proc_exec_seq AtomicPair.l es (rec_singleton (Ret tt)) 
                (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (apply sR.R.crash_refinement_seq).
Time Qed.
