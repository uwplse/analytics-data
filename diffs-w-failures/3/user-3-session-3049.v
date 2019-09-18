Time From Transitions Require Import Relations Rewriting.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time Require Export CSL.WeakestPre CSL.Refinement CSL.Adequacy.
Time From iris.algebra Require Import auth frac agree gmap list.
Time From iris.base_logic.lib Require Import invariants.
Time From iris.proofmode Require Import tactics.
Time Unset Implicit Arguments.
Time Import RelationNotations.
Time From Transitions Require Import Relations.
Time
Definition wp_recovery_refinement {Ta} {Tc} {R} {OpTa} 
  {OpTc} \206\163 (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) `{invPreG \206\163}
  `{cfgPreG OpTa \206\155a \206\163} (ea : proc OpTa Ta) (ec : proc OpTc Tc)
  (rec : proc OpTc R) (\207\1311a : State \206\155a) \207\1311c \207\134 \207\134rec 
  E k :=
  Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
    (\226\140\156nclose sourceN \226\138\134 E\226\140\157
     \226\136\167 (\226\136\131 \207\134inv : forall {_ : @cfgG OpTa \206\155a \206\163}, State \206\155c \226\134\146 iProp \206\163,
          \226\136\128 `{Hinv : invG \206\163} `{Hcfg : cfgG OpTa \206\155a \206\163},
            |={\226\138\164}=> \226\136\131 stateI : State \206\155c \226\134\146 iProp \206\163,
                      let _ : irisG OpTc \206\155c \206\163 := IrisG _ _ _ Hinv stateI in
                      source_ctx' ([existT _ ea], snd \207\1311a)
                      \226\136\151 O \226\164\135 ea \226\136\151 source_state (snd \207\1311a)
                      ={\226\138\164}=\226\136\151 stateI \207\1311c
                             \226\136\151 WP ec
                               @ NotStuck; \226\138\164 {{ vc, 
                               \226\136\131 va : Ta,
                                 O \226\164\135 of_val va
                                 \226\136\151 (\226\136\128 \207\1312c,
                                      stateI \207\1312c
                                      ={\226\138\164,E}=\226\136\151 \226\136\131 \207\1312a,
                                                 source_state \207\1312a
                                                 \226\136\151 
                                                 \207\134 va vc \207\1312a (snd \207\1312c)) }}
                               \226\136\151 (\226\136\128 \207\1312c, stateI \207\1312c ={\226\138\164,E}=\226\136\151 \207\134inv \207\1312c)
                                 \226\136\151 \226\150\161 (\226\136\128 `{Hinv : invG \206\163} 
                                        `{Hcfg : cfgG OpTa \206\155a \206\163} 
                                        \207\1311c \207\1311c' (Hcrash : 
                                                 lifted_crash_step \206\155c \207\1311c
                                                 (Val \207\1311c' tt)),
                                        \207\134inv \207\1311c
                                        \226\136\151 source_ctx'
                                            ([existT _ ea], snd \207\1311a)
                                        ={\226\138\164}=\226\136\151 \226\136\131 stateI : State \206\155c \226\134\146 iProp \206\163,
                                                 let _ : 
                                                 irisG OpTc \206\155c \206\163 :=
                                                 IrisG _ _ _ Hinv stateI in
                                                 stateI \207\1311c'
                                                 \226\136\151 
                                                 WP rec
                                                 @ NotStuck; \226\138\164 {{ v, 
                                                 \226\136\128 \207\1312c,
                                                 stateI \207\1312c
                                                 ={\226\138\164,E}=\226\136\151 
                                                 \226\136\131 \207\1312a \207\1312a',
                                                 source_state (snd \207\1312a)
                                                 \226\136\151 
                                                 \226\140\156
                                                 lifted_crash_step \206\155a \207\1312a
                                                 (Val \207\1312a' tt)\226\140\157
                                                 \226\136\151 
                                                 \207\134rec (snd \207\1312a') (snd \207\1312c) }}
                                                 \226\136\151 
                                                 (\226\136\128 \207\1312c,
                                                 stateI \207\1312c ={\226\138\164,E}=\226\136\151 \207\134inv \207\1312c))))%I.
Time
Fixpoint wp_proc_seq_refinement {Ta Tc R OpTa OpTc} 
{\206\163} (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) `{invPreG \206\163} 
`{cfgPreG OpTa \206\155a \206\163} (esa : proc_seq OpTa Ta) (esc : proc_seq OpTc Tc)
(rec : proc OpTc R) (\207\1311a : State \206\155a) \207\1311c \207\134 E {struct esa} : 
iProp \206\163 :=
  match esa, esc with
  | Proc_Seq_Nil va, Proc_Seq_Nil vc => (\207\134 va vc \207\1311a \207\1311c)%I
  | @Proc_Seq_Bind _ _ T0a ea esa, @Proc_Seq_Bind _ _ T0c ec esc =>
      wp_recovery_refinement \206\163 \206\155a \206\155c ea ec rec \207\1311a \207\1311c
        (\206\187 (va : T0a) (vc : T0c) \207\1312a \207\1312c,
           \226\136\128 \207\1312c' (Hfinish : \206\155c.(finish_step) \207\1312c (Val \207\1312c' tt)),
             \226\136\131 \207\1312a' (Hfinisha : \206\155a.(finish_step) \207\1312a (Val \207\1312a' tt)),
               wp_proc_seq_refinement \206\155a \206\155c (esa (Normal (existT T0a va)))
                 (esc (Normal (existT T0c vc))) rec 
                 (1, \207\1312a') (1, \207\1312c') \207\134 E)%I
        (\206\187 \207\1312a \207\1312c,
           wp_proc_seq_refinement \206\155a \206\155c (esa (Recovered (existT _ tt)))
             (esc (Recovered (existT _ tt))) rec (1, \207\1312a) 
             (1, \207\1312c) \207\134 E) E O
  | _, _ => False%I
  end.
Time
Lemma crash_step_snd {OpT} (\206\155a : Layer OpT) \207\1311a \207\1312a 
  t n :
  lifted_crash_step \206\155a \207\1311a (Val \207\1312a t)
  \226\134\146 lifted_crash_step \206\155a (n, snd \207\1311a) (Val (1, snd \207\1312a) tt).
Time Proof.
Time rewrite /lifted_crash_step.
Time (destruct \207\1311a as (n1, \207\1311a)).
Time (destruct \207\1312a as (n2, \207\1312a)).
Time (intros ([], ((?, \207\1311a'), (Hput, Hcrash)))).
Time (inversion Hput; subst).
Time (inversion H).
Time subst.
Time (inversion Hcrash; subst).
Time exists tt,(1, \207\1311a').
Time (split; eauto).
Time (econstructor; destruct t; eauto).
Time Qed.
Time
Lemma finish_step_snd {OpT} (\206\155a : Layer OpT) \207\1311a \207\1312a 
  t n :
  lifted_finish_step \206\155a \207\1311a (Val \207\1312a t)
  \226\134\146 lifted_finish_step \206\155a (n, snd \207\1311a) (Val (1, snd \207\1312a) tt).
Time Proof.
Time rewrite /lifted_finish_step.
Time (destruct \207\1311a as (n1, \207\1311a)).
Time (destruct \207\1312a as (n2, \207\1312a)).
Time (intros ([], ((?, \207\1311a'), (Hput, Hcrash)))).
Time (inversion Hput; subst).
Time (inversion H).
Time subst.
Time (inversion Hcrash; subst).
Time exists tt,(1, \207\1311a').
Time (split; eauto).
Time (econstructor; destruct t; eauto).
Time Qed.
Time
Lemma lifted_finish_step_intro {OpT} (\206\155a : Layer OpT) 
  n \207\131 \207\131' t1 t2 :
  finish_step \206\155a \207\131 (Val \207\131' t1)
  \226\134\146 lifted_finish_step \206\155a (n, \207\131) (Val (1, \207\131') t2).
Time Proof.
Time (intros).
Time (destruct t1, t2).
Time (exists tt,(1, \207\131); split; rewrite //=).
Time Qed.
Time
Lemma lifted_finish_step_intro' {OpT} (\206\155a : Layer OpT) 
  \207\131 \207\131' t1 t2 :
  finish_step \206\155a (snd \207\131) (Val \207\131' t1)
  \226\134\146 lifted_finish_step \206\155a \207\131 (Val (1, \207\131') t2).
Time Proof.
Time (intros).
Time (destruct t1, t2, \207\131).
Time (eapply lifted_finish_step_intro; eauto).
Time Qed.
Time
Lemma wp_recovery_refinement_impl_wp_recovery {Ta} 
  {Tc} {R} OpTa OpTc \206\163 (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) 
  `{invPreG \206\163} `{cfgPreG OpTa \206\155a \206\163} (ea : proc OpTa Ta) 
  (ec : proc OpTc Tc) (rec : proc OpTc R) \207\1311a \207\1311c 
  \207\134 \207\134rec E k (Hno_fault : \194\172 exec \206\155a ea (1, \207\1311a) Err) :
  wp_recovery_refinement \206\163 \206\155a \206\155c ea ec rec (1, \207\1311a) \207\1311c \207\134 \207\134rec E k
  \226\138\162 wp_recovery NotStuck ec rec \207\1311c
      (\206\187 (vc : Tc) (\207\1312c : State \206\155c),
         \226\136\131 va \207\1312a,
           \226\140\156exec \206\155a ea (1, \207\1311a) (Val \207\1312a (existT Ta va))\226\140\157
           \226\136\151 \207\134 va vc \207\1312a.2 \207\1312c.2)
      (\206\187 \207\1312c : State \206\155c,
         \226\136\131 tp2 (\207\1312a \207\1312a' : Proc.State),
           \226\140\156exec_partial \206\155a ea (1, \207\1311a) (Val \207\1312a tp2)
            \226\136\167 lifted_crash_step \206\155a \207\1312a (Val \207\1312a' tt)\226\140\157 \226\136\151 
           \207\134rec \207\1312a'.2 \207\1312c.2) k.
Time Proof.
Time iIntros "Hwp".
Time iApply (bupd_iter_mono with "[] Hwp").
Time iIntros "Hwp".
Time iDestruct "Hwp" as ( Hclosure \207\134inv ) "Hwp".
Time
iExists (fun \207\131 => (\226\136\131 _ : cfgG \206\163, \207\134inv _ \207\131 \226\136\151 source_inv [existT Ta ea] \207\1311a)%I).
Time iIntros ( Hinv ).
Time (assert (Inhabited \206\155a.(OpState))).
Time {
Time (eexists; eauto).
Time }
Time
(iMod (source_cfg_init [existT _ ea] \207\1311a) as ( cfgG )
  "(#Hsrc&Hpool&HstateA)"; auto).
Time {
Time (intros Herr; apply Hno_fault).
Time (apply exec_partial_err_exec_err; eauto).
Time }
Time iMod ("Hwp" $! _ _) as ( stateI ) "Hwand".
Time
(iMod ("Hwand" with "[Hpool HstateA]") as "[Hstate [H [Hinv #H\207\134]]]"; eauto).
Time {
Time iFrame.
Time iFrame "#".
Time
rewrite /source_pool_map /tpool_to_map fmap_insert fmap_empty insert_empty
 //=.
Time }
Time iExists stateI.
Time iIntros "{$Hstate} !>".
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "H" ; last  iSplitL "Hinv").
Time *
Time (iApply wp_wand_l; iFrame "H").
Time iIntros ( vc ) "H".
Time iDestruct "H" as ( va ) "(Hmapsto&Hopen)".
Time iIntros ( \207\1312c' ) "Hstate".
Time iMod ("Hopen" with "Hstate") as ( \207\1312a ) "(Hstate&Habsr)".
Time iInv "Hsrc" as ( tp' n' \207\131' ) ">[Hauth Hp]" "_".
Time iDestruct "Hp" as % Hp.
Time (destruct Hp as (Hp, Hno_fault')).
Time rewrite //= in  {} Hp.
Time
(iDestruct (source_state_reconcile with "Hstate Hauth") as % Hstate; subst).
Time
(iDestruct (source_thread_reconcile with "Hmapsto Hauth") as % Hlookup; subst).
Time (apply take_drop_middle in Hlookup).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply fupd_mask_weaken ; first  by
 set_solver +).
Time iExists va , (n', \207\131').
Time (iSplit; auto).
Time iPureIntro.
Time rewrite -Hlookup //= /of_val in  {} Hp.
Time (eapply exec_partial_finish; eauto).
Time *
Time iIntros.
Time iMod ("Hinv" with "[$]").
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (inv_open_timeless with "Hsrc") as
 "(?&_)" ; first  by eassumption).
Time (iApply fupd_mask_weaken; auto).
Time {
Time set_solver +.
Time }
Time iFrame.
Time (iExists _; iFrame).
Time *
Time iModIntro.
Time iIntros ( ? ? ? ? ) "Hinv".
Time iDestruct "Hinv" as ( cfgG' ) "(?&HcfgInv)".
Time iClear "Hsrc".
Time iMod (inv_alloc sourceN \226\138\164 (source_inv _ _) with "HcfgInv") as "#cfgInv".
Time iMod ("H\207\134" with "[//] [$]") as ( stateI' ) "(Hstate&Hwp&Hinv)".
Time iModIntro.
Time iExists stateI'.
Time iFrame.
Time iSplitL "Hwp".
Time **
Time (iApply wp_wand_l; iFrame).
Time iIntros ( _ ) "H1".
Time iIntros ( \207\131 ) "Hstate".
Time iMod ("H1" with "[$]") as ( \207\1312a \207\1313a ) "(Hstate&Hp&Habsr)".
Time iDestruct "Hp" as % Hcrash.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (inv_open_timeless with "cfgInv") as
 "(Hinv&_)" ; first  by eassumption).
Time (iApply fupd_mask_weaken; auto).
Time {
Time set_solver +.
Time }
Time iDestruct "Hinv" as ( tp' n' \207\1313a' ) "(Hauth&%&%)".
Time
(iDestruct (source_state_reconcile with "Hstate Hauth") as % Hstate; subst).
Time iExists _ , _ , (1, snd \207\1313a).
Time iFrame.
Time (iPureIntro; intuition eauto).
Time (eapply crash_step_snd; eauto).
Time **
Time iIntros.
Time iMod ("Hinv" with "[$]").
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (inv_open_timeless with "cfgInv") as
 "(?&_)" ; first  by eassumption).
Time (iApply fupd_mask_weaken; auto).
Time {
Time set_solver +.
Time }
Time iFrame.
Time (iExists _; iFrame).
Time Qed.
Time
Theorem wp_recovery_refinement_adequacy_internal {Ta} 
  {Tc} {R} OpTa OpTc \206\163 (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) 
  `{invPreG \206\163} `{cfgPreG OpTa \206\155a \206\163} (ea : proc OpTa Ta) 
  (ec : proc OpTc Tc) (rec : proc OpTc R) \207\1311a \207\1311c 
  \207\134 \207\134rec E k (Hno_fault : \194\172 exec \206\155a ea (1, \207\1311a) Err) :
  wp_recovery_refinement \206\163 \206\155a \206\155c ea ec rec (1, \207\1311a) \207\1311c \207\134 \207\134rec E k
  \226\138\162 recv_adequate_internal NotStuck ec rec \207\1311c
      (\206\187 v \207\1312c,
         \226\136\131 va \207\1312a,
           \226\140\156exec \206\155a ea (1, \207\1311a) (Val \207\1312a (existT _ va))\226\140\157
           \226\136\151 \207\134 va v (snd \207\1312a) (snd \207\1312c))%I
      (\206\187 \207\1312c,
         \226\136\131 tp2 \207\1312a \207\1312a',
           \226\140\156exec_partial \206\155a ea (1, \207\1311a) (Val \207\1312a tp2)
            \226\136\167 lifted_crash_step \206\155a \207\1312a (Val \207\1312a' tt)\226\140\157
           \226\136\151 \207\134rec (snd \207\1312a') (snd \207\1312c))%I k.
Time Proof.
Time iIntros "Hwp".
Time (unshelve iApply wp_recovery_adequacy_internal; eauto).
Time (iApply wp_recovery_refinement_impl_wp_recovery; eauto).
Time Qed.
Time
Theorem wp_proc_seq_refinement_adequacy_internal {Ta} 
  {Tc} {R} OpTa OpTc \206\163 (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) 
  `{invPreG \206\163} `{cfgPreG OpTa \206\155a \206\163} (esa : proc_seq OpTa Ta)
  (esc : proc_seq OpTc Tc) (rec : proc OpTc R) \207\1311c 
  \207\1311a \207\134 P E k
  (Hno_fault : \194\172 proc_exec_seq \206\155a esa (rec_singleton (Ret tt)) (1, \207\1311a) Err)
  (H\207\134 : \226\136\128 va vc \207\1312a \207\1312c, \207\134 va vc \207\1312c \207\1312a -\226\136\151 \226\140\156P va vc\226\140\157) :
  Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
    (wp_proc_seq_refinement \206\155a \206\155c esa esc rec (1, \207\1311a) \207\1311c \207\134 E)
  \226\138\162 \226\136\128 n \207\1312c vc,
      \226\140\156proc_exec_seq_n \206\155c esc rec n \207\1311c (Val \207\1312c vc)\226\140\157
      \226\134\146 (Nat.iter (S k + n) (\206\187 P, |==> \226\150\183 P)%I
           (\226\140\156\226\136\131 va \207\1312a,
               proc_exec_seq \206\155a esa (rec_singleton (Ret tt)) 
                 (1, \207\1311a) (Val \207\1312a va) \226\136\167 P va vc\226\140\157
              : iProp \206\163))%I.
Time Proof.
Time iIntros "Hwp".
Time iIntros ( n \207\1312c res Hexec ).
Time iRevert "Hwp".
Time
(iInduction esa as [] "IH" forall ( k n esc \207\1311c \207\1311a Hno_fault Hexec );
  iIntros "Hwp").
Time -
Time (destruct esc).
Time *
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@bupd_iter_le _ k) =>//=; try lia).
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  eauto).
Time iIntros "H".
Time iDestruct (H\207\134 with "H") as % ?.
Time iPureIntro.
Time (destruct Hexec as (?, Hpure)).
Time (inversion Hpure; subst).
Time eexists _,(1, \207\1311a).
Time (split; eauto).
Time econstructor.
Time *
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@bupd_iter_le _ k) =>//=; try lia).
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  eauto).
Time auto.
Time -
Time (destruct esc).
Time {
Time (simpl).
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@bupd_iter_le _ k) =>//=; try lia).
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  eauto).
Time auto.
Time }
Time (destruct Hexec as (n1, (n2, (Heq, (res0, (\207\1311', (Hhd, Hrest))))))).
Time (destruct Hhd as [Hnorm| Hrecv]).
Time **
Time (destruct Hnorm as (v, ((?, ?), (Hexec, Hfinish)))).
Time (destruct Hfinish as ([], ((?, ?), (Hfinish, Hpure)))).
Time (destruct Hfinish as ([], ((?, ?), (Hputs, Hfinish)))).
Time (inversion Hputs; subst).
Time (inversion Hpure; subst).
Time (destruct Hfinish; subst).
Time
replace (S k + (5 + n1 + S n2))%nat with (S k + 5 + n1 + S n2)%nat by lia.
Time rewrite /wp_proc_seq_refinement -/wp_proc_seq_refinement.
Time rewrite Nat_iter_add.
Time
(unshelve iPoseProof (wp_recovery_refinement_adequacy_internal with "Hwp") as
  "Hwp"; eauto).
Time {
Time (intros Herr).
Time (apply Hno_fault).
Time (do 3 left).
Time eauto.
Time }
Time iDestruct "Hwp" as "(Hwp&_)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply
 (@bupd_iter_le _ (S k + S (S n1))%nat) ; first  by lia).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  by iApply
 "Hwp").
Time iIntros "H".
Time iDestruct "H" as ( v' Hp ) "H".
Time subst.
Time iDestruct "H" as ( va \207\1312a Hexeca ) "H".
Time
(unshelve iDestruct ("H" $! _ _) as ( \207\1312a' Hfinisha ) "H"; [  | eauto |  ];
  [  ]).
Time (inversion H1; subst).
Time iMod ("IH" $! _ O n2 with "[] [] H") as "H".
Time {
Time iPureIntro.
Time (intros Herr).
Time (eapply Hno_fault).
Time right.
Time (do 2 eexists; split; eauto).
Time left.
Time (do 2 eexists; split; eauto).
Time exists tt.
Time eexists.
Time (split; eauto).
Time (eapply lifted_finish_step_intro'; eauto).
Time econstructor.
Time }
Time {
Time eauto.
Time }
Time iModIntro.
Time iNext.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  by iApply "H").
Time iIntros "H".
Time iDestruct "H" as ( va'' \207\1312a'' ) "(%&%)".
Time iPureIntro.
Time (exists va'',\207\1312a''; split; auto).
Time (do 2 eexists; split; eauto).
Time left.
Time (do 2 eexists; split; eauto).
Time eexists tt,_.
Time (split; eauto).
Time (eapply lifted_finish_step_intro'; eauto).
Time econstructor.
Time **
Time (destruct Hrecv as ([], ((?, ?), (Hrexec, Hfinish)))).
Time (destruct Hfinish as ([], ((?, ?), (Hputs, Hpure)))).
Time (inversion Hpure).
Time subst.
Time (destruct Hputs as (Hput, Hpure')).
Time (inversion Hpure').
Time subst.
Time (inversion Hput; subst).
Time
replace (S k + (5 + n1 + S n2))%nat with (S k + (5 + n1) + S n2)%nat by lia.
Time rewrite /wp_proc_seq_refinement -/wp_proc_seq_refinement.
Time rewrite Nat_iter_add.
Time
(unshelve iPoseProof (wp_recovery_refinement_adequacy_internal with "Hwp") as
  "Hwp"; eauto).
Time {
Time (intros Herr).
Time (apply Hno_fault).
Time (do 3 left).
Time eauto.
Time }
Time iDestruct "Hwp" as "(_&Hwp&_)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  by iApply
 "Hwp").
Time iIntros "H".
Time iDestruct "H" as ( v' Hp ) "H".
Time subst.
Time iDestruct "H" as ( \207\1312a Hexeca ) "H".
Time replace (S n2) with (1 + n2)%nat by auto.
Time iMod ("IH" $! _ O n2 with "[] [] H") as "H".
Time {
Time iPureIntro.
Time (intros Herr).
Time (eapply Hno_fault).
Time right.
Time (do 2 eexists; split; eauto).
Time right.
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split; eauto ; last 
 econstructor).
Time (eapply rexec_singleton_ret_intro; intuition eauto).
Time
(<ssreflect_plugin::ssrtclseq@0> eexists (_, _); split; eauto ; last 
 econstructor).
Time (destruct \207\1312a; econstructor; eauto).
Time }
Time {
Time eauto.
Time }
Time iModIntro.
Time iNext.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  by iApply "H").
Time iIntros "H".
Time iDestruct "H" as ( va' \207\1312a' ) "(%&%)".
Time iPureIntro.
Time (exists va',\207\1312a'; split; auto).
Time (do 2 eexists; split; eauto).
Time right.
Time (<ssreflect_plugin::ssrtclseq@0> econstructor ; last  econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> econstructor ; last  econstructor).
Time (eapply rexec_singleton_ret_intro; intuition eauto).
Time
(<ssreflect_plugin::ssrtclseq@0> eexists (_, _); split; eauto ; last 
 econstructor).
Time (destruct \207\1312a; econstructor; eauto).
Time Qed.
Time
Theorem wp_proc_seq_refinement_impl_wp_proc_seq {Ta} 
  {Tc} {R} OpTa OpTc \206\163 (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) 
  `{invPreG \206\163} `{cfgPreG OpTa \206\155a \206\163} (esa : proc_seq OpTa Ta)
  (esc : proc_seq OpTc Tc) (rec : proc OpTc R) \207\1311c 
  \207\1311a \207\134 E
  (Hno_fault : \194\172 proc_exec_seq \206\155a esa (rec_singleton (Ret tt)) (1, \207\1311a) Err)
  :
  wp_proc_seq_refinement \206\155a \206\155c esa esc rec (1, \207\1311a) (1, \207\1311c) \207\134 E
  \226\138\162 wp_proc_seq NotStuck esc rec (1, \207\1311c)
      (\206\187 (vc : Tc) (\207\1312c : State \206\155c), \226\136\131 va \207\1312a, \207\134 va vc \207\1312a (1, \207\1312c.2)).
Time Proof.
Time revert esc \207\1311c \207\1311a Hno_fault.
Time
(<ssreflect_plugin::ssrtclintros@0> induction esa as [| ? ? ? IH] =>esc \207\1311c
 \207\1311a Hno_fault).
Time -
Time (destruct esc; simpl; eauto).
Time iIntros "[]".
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> destruct esc ; first  by
 simpl; eauto; iIntros "[]").
Time rewrite /wp_proc_seq_refinement -/wp_proc_seq_refinement.
Time iIntros "Hwp".
Time
iPoseProof (wp_recovery_refinement_impl_wp_recovery with "Hwp") as "Hwp".
Time {
Time (intros Hexec).
Time (apply Hno_fault).
Time (do 2 left).
Time (do 2 left).
Time by apply exec_partial_err_exec_err.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iApply wp_recovery_mono ; last  iApply
  "Hwp"; rewrite -/wp_proc_seq).
Time *
Time iIntros ( ? ? ) "H".
Time iDestruct "H" as ( va \207\1312a Hexeca ) "H".
Time iIntros.
Time iDestruct ("H" $! _ Hfinish) as ( \207\1312a' Hexeca' ) "H".
Time (simpl).
Time iApply IH.
Time {
Time (intros Herr).
Time (eapply Hno_fault).
Time right.
Time (do 2 eexists; split; eauto).
Time left.
Time (do 2 eexists; split; eauto).
Time (do 2 eexists).
Time (<ssreflect_plugin::ssrtclseq@0> split; eauto ; last  econstructor).
Time rewrite /lifted_finish_step.
Time (eexists tt,(1, snd \207\1312a); split).
Time *
Time (destruct \207\1312a).
Time (split; eauto).
Time econstructor.
Time *
Time (econstructor; eauto).
Time }
Time eauto.
Time *
Time iAlways.
Time iIntros ( ? ) "H".
Time iDestruct "H" as ( tp2 \207\1312a \207\1312a' (Hexeca, Hcrash) ) "H".
Time (destruct \207\1312a).
Time (destruct \207\1312a').
Time iIntros.
Time (simpl).
Time iApply IH.
Time {
Time (intros Herr).
Time (eapply Hno_fault).
Time right.
Time (do 2 eexists; split; eauto).
Time right.
Time (do 2 eexists).
Time split.
Time (eapply rexec_singleton_ret_intro; eauto).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split; eauto ; last 
 econstructor).
Time econstructor.
Time econstructor.
Time eauto.
Time }
Time eauto.
Time Qed.
Time
Theorem wp_proc_seq_refinement_impl_wp_proc_seq' {Ta} 
  {Tc} {R} OpTa OpTc \206\163 (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) 
  `{invPreG \206\163} `{cfgPreG OpTa \206\155a \206\163} (esa : proc_seq OpTa Ta)
  (esc : proc_seq OpTc Tc) (rec : proc OpTc R) \207\1311c 
  \207\1311a \207\134 E
  (Hno_fault : \194\172 proc_exec_seq \206\155a esa (rec_singleton (Ret tt)) (1, \207\1311a) Err)
  :
  wp_proc_seq_refinement \206\155a \206\155c esa esc rec (1, \207\1311a) (1, \207\1311c) \207\134 E
  \226\138\162 wp_proc_seq NotStuck esc rec (1, \207\1311c) (\206\187 _ _, True).
Time Proof.
Time iIntros "H".
Time
(iPoseProof (wp_proc_seq_refinement_impl_wp_proc_seq with "H") as "H"; auto).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply wp_proc_seq_mono ; last  by iApply
 "H").
Time iAlways.
Time auto.
Time Qed.
Time Import uPred.
Time
Theorem wp_proc_seq_refinement_adequacy {T} {R} OpTa 
  OpTc \206\163 (\206\155a : Layer OpTa) (\206\155c : Layer OpTc) `{invPreG \206\163}
  `{cfgPreG OpTa \206\155a \206\163} (esa : proc_seq OpTa T) (esc : proc_seq OpTc T)
  (rec : proc OpTc R) \207\1311c \207\1311a \207\134 E
  (Hno_fault : \194\172 proc_exec_seq \206\155a esa (rec_singleton (Ret tt)) (1, \207\1311a) Err)
  (H\207\134 : \226\136\128 va vc \207\1312a \207\1312c, \207\134 va vc \207\1312c \207\1312a -\226\136\151 \226\140\156va = vc\226\140\157) :
  wp_proc_seq_refinement \206\155a \206\155c esa esc rec (1, \207\1311a) (1, \207\1311c) \207\134 E
  \226\134\146 \226\136\128 \207\1312c res,
      proc_exec_seq \206\155c esc (rec_singleton rec) (1, \207\1311c) (Val \207\1312c res)
      \226\134\146 \226\136\131 \207\1312a,
          proc_exec_seq \206\155a esa (rec_singleton (Ret tt)) 
            (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (intros Hwp ? ? Hexec).
Time
(<ssreflect_plugin::ssrtclseq@0>
 eapply proc_exec_seq_equiv_proc_exec_seq_n in Hexec as (n, ?) ; last  first).
Time {
Time (eapply proc_seq_adequate_not_stuck; eauto).
Time (eapply wp_proc_seq_adequacy with (k := 0) (\207\1340 := \206\187 _ _, True); eauto).
Time (simpl).
Time (iApply (wp_proc_seq_refinement_impl_wp_proc_seq' with "[]"); eauto).
Time iApply Hwp.
Time }
Time {
Time eauto using lifted_crash_non_err.
Time }
Time (eapply (soundness (M:=iResUR \206\163) _ (S O + n))).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_laterN_mono ; first  by
 reflexivity; eauto).
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  first).
Time {
Time (iApply wp_proc_seq_refinement_adequacy_internal; eauto).
Time (iApply Hwp; eauto).
Time }
Time iIntros "H".
Time iDestruct "H" as % (va, (\207\1312a, (Hexec, Heq))).
Time subst.
Time eauto.
Time Qed.
