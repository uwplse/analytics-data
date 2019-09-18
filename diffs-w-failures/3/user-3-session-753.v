Time From Transitions Require Import Relations Rewriting.
Time Require Export Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Export Spec.Layer.
Time Require Export CSL.WeakestPre.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time #[global]Unset Implicit Arguments.
Time Section lifting.
Time Context {OpT : Type \226\134\146 Type}.
Time Context `{\206\155 : Layer OpT}.
Time Context `{irisG OpT \206\155 \206\163}.
Time Implicit Type s : stuckness.
Time Implicit Type \207\131 : State \206\155.
Time Implicit Types P Q : iProp \206\163.
Time
Lemma wp_lift_pre_step {T} s E \206\166 (e1 : proc OpT T) :
  to_val e1 = None
  \226\134\146 (\226\136\128 \207\1311, state_interp \207\1311 ={E,E}=\226\136\151 state_interp \207\1311 \226\136\151 WP e1 @ s; E {{ \206\166 }})
    \226\138\162 WP e1 @ s; E {{ \206\166 }}.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite {+2}wp_unfold /wp_pre =>Heq).
Time rewrite Heq.
Time iIntros "Hwand".
Time iIntros ( \207\131 ) "H".
Time iMod ("Hwand" with "H") as "(Hinterp&Hwp)".
Time rewrite wp_unfold /wp_pre.
Time rewrite Heq.
Time by iApply "Hwp".
Time Qed.
Time
Lemma wp_lift_step_fupd {T} s E \206\166 (e1 : proc OpT T) :
  to_val e1 = None
  \226\134\146 (\226\136\128 \207\1311,
       state_interp \207\1311
       ={E,\226\136\133}=\226\136\151 \226\140\156match s with
                 | NotStuck => non_errorable e1 \207\1311
                 | _ => True
                 end\226\140\157
                \226\136\151 (\226\136\128 e2 \207\1312 (efs : thread_pool OpT),
                     \226\140\156exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2, efs))\226\140\157
                     ={\226\136\133,\226\136\133,E}\226\150\183=\226\136\151 state_interp \207\1312
                                 \226\136\151 WP e2 @ s; E {{ \206\166 }}
                                   \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, 
                                      WP projT2 ef @ s; \226\138\164 {{ _, True }})))
    \226\138\162 WP e1 @ s; E {{ \206\166 }}.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite wp_unfold /wp_pre =>{+}->).
Time iIntros "H" ( \207\1311 ) "H\207\131".
Time iMod ("H" with "H\207\131") as "(%&H)".
Time iModIntro.
Time iSplit.
Time by destruct s.
Time done.
Time Qed.
Time
Lemma wp_lift_step {T} s E \206\166 (e1 : proc OpT T) :
  to_val e1 = None
  \226\134\146 (\226\136\128 \207\1311,
       state_interp \207\1311
       ={E,\226\136\133}=\226\136\151 \226\140\156match s with
                 | NotStuck => non_errorable e1 \207\1311
                 | _ => True
                 end\226\140\157
                \226\136\151 \226\150\183 (\226\136\128 e2 \207\1312 efs,
                       \226\140\156exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2, efs))\226\140\157
                       ={\226\136\133,E}=\226\136\151 state_interp \207\1312
                                \226\136\151 WP e2 @ s; E {{ \206\166 }}
                                  \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, 
                                     WP projT2 ef @ s; \226\138\164 {{ _, True }})))
    \226\138\162 WP e1 @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros ( ? ) "H".
Time (iApply wp_lift_step_fupd; [ done |  ]).
Time iIntros ( ? ) "H\207\131".
Time iMod ("H" with "H\207\131") as "[$ H]".
Time iIntros "!> * % !>".
Time by iApply "H".
Time Qed.
Time
Lemma wp_lift_pure_step {T} s E E' \206\166 (e1 : proc OpT T) :
  match s with
  | NotStuck => (\226\136\128 \207\1311, non_errorable e1 \207\1311) \226\136\167 to_val e1 = None
  | _ => to_val e1 = None
  end
  \226\134\146 (\226\136\128 \207\1311 e2 \207\1312 efs, exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2, efs)) \226\134\146 \207\1311 = \207\1312)
    \226\134\146 (|={E,E'}\226\150\183=> \226\136\128 e2 efs \207\131,
                     \226\140\156exec_step \206\155.(sem) e1 \207\131 (Val \207\131 (e2, efs))\226\140\157
                     \226\134\146 WP e2 @ s; E {{ \206\166 }}
                       \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, WP projT2 ef
                                             @ s; \226\138\164 {{ _, True }}))
      \226\138\162 WP e1 @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros ( Hsafe Hstep ) "H".
Time iApply wp_lift_step.
Time {
Time (destruct s; intuition).
Time }
Time iIntros ( \207\1311 ) "H\207\131".
Time iMod "H".
Time
(<ssreflect_plugin::ssrtclseq@0> <ssreflect_plugin::ssrtclseq@0> iMod
 fupd_intro_mask' as "Hclose" ; last  iModIntro ; first  by set_solver).
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s; intuition; eapply Hsafe).
Time }
Time iNext.
Time iIntros ( e2 \207\1312 efs ? ).
Time (destruct (Hstep \207\1311 e2 \207\1312 efs); auto; subst).
Time iMod "Hclose" as "_".
Time iFrame "H\207\131".
Time iMod "H".
Time (iApply "H"; auto).
Time Qed.
Time
Lemma wp_lift_atomic_step_fupd {T} {s} {E1} {E2} {\206\166} 
  (e1 : proc OpT T) :
  to_val e1 = None
  \226\134\146 (\226\136\128 \207\1311,
       state_interp \207\1311
       ={E1}=\226\136\151 \226\140\156match s with
                | NotStuck => non_errorable e1 \207\1311
                | _ => True
                end\226\140\157
               \226\136\151 (\226\136\128 e2 \207\1312 efs,
                    \226\140\156exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2, efs))\226\140\157
                    ={E1,E2}\226\150\183=\226\136\151 state_interp \207\1312
                                \226\136\151 from_option \206\166 False (to_val e2)
                                  \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, 
                                     WP projT2 ef @ s; \226\138\164 {{ _, True }})))
    \226\138\162 WP e1 @ s; E1 {{ \206\166 }}.
Time Proof.
Time iIntros ( ? ) "H".
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (wp_lift_step_fupd s E1 _ e1)
  =>//; iIntros ( \207\1311 ) "H\207\1311").
Time iMod ("H" $! \207\1311 with "H\207\1311") as "[$ H]".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (fupd_intro_mask' E1 \226\136\133) as "Hclose" ;
 first  set_solver).
Time iIntros "!>" ( e2 \207\1312 efs ? ).
Time iMod "Hclose" as "_".
Time (iMod ("H" $! e2 \207\1312 efs with "[#]") as "H"; [ done |  ]).
Time (iMod (fupd_intro_mask' E2 \226\136\133) as "Hclose"; [ set_solver |  ]).
Time iIntros "!> !>".
Time iMod "Hclose" as "_".
Time iMod "H" as "($ & H\206\166 & $)".
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (to_val e2) eqn:? ; last  by
 iExFalso).
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_value ; last  done).
Time by apply of_to_val.
Time Qed.
Time
Lemma wp_lift_atomic_step {T} {s} {E} {\206\166} (e1 : proc OpT T) :
  to_val e1 = None
  \226\134\146 (\226\136\128 \207\1311,
       state_interp \207\1311
       ={E}=\226\136\151 \226\140\156match s with
               | NotStuck => non_errorable e1 \207\1311
               | _ => True
               end\226\140\157
              \226\136\151 \226\150\183 (\226\136\128 e2 \207\1312 efs,
                     \226\140\156exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2, efs))\226\140\157
                     ={E}=\226\136\151 state_interp \207\1312
                            \226\136\151 from_option \206\166 False (to_val e2)
                              \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, 
                                 WP projT2 ef @ s; \226\138\164 {{ _, True }})))
    \226\138\162 WP e1 @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros ( ? ) "H".
Time (iApply wp_lift_atomic_step_fupd; [ done |  ]).
Time iIntros ( ? ) "?".
Time iMod ("H" with "[$]") as "[$ H]".
Time iIntros "!> * % !> !>".
Time by iApply "H".
Time Qed.
Time
Lemma wp_lift_call_step {T} {s} {E} {\206\166} (op : OpT T) :
  (\226\136\128 \207\1311,
     state_interp \207\1311
     ={E}=\226\136\151 \226\140\156match s with
             | NotStuck => \194\172 snd_lift (\206\155.(sem).(step) op) \207\1311 Err
             | _ => True
             end\226\140\157
            \226\136\151 \226\150\183 (\226\136\128 e2 \207\1312,
                   \226\140\156snd_lift (\206\155.(sem).(step) op) \207\1311 (Val \207\1312 e2)\226\140\157
                   ={E}=\226\136\151 state_interp \207\1312 \226\136\151 \206\166 e2))
  \226\138\162 WP Call op @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time (iApply wp_lift_atomic_step; [ done |  ]).
Time iIntros ( \207\131 ) "?".
Time iMod ("H" with "[$]") as "[% H]".
Time iSplitL "".
Time {
Time
(iModIntro; iPureIntro; <ssreflect_plugin::ssrtclintros@0> 
  destruct s =>//= Herr).
Time by apply bind_pure_no_err in Herr.
Time }
Time iIntros "!> * % !>".
Time iIntros ( \207\1312 efs Hstep ).
Time (destruct Hstep as (?, (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time rewrite //= right_id.
Time (iApply "H"; eauto).
Time Qed.
Time
Lemma wp_lift_pure_det_step {T} {s} {E} {\206\166} E' (e1 : proc OpT T) 
  e2 efs :
  match s with
  | NotStuck => (\226\136\128 \207\1311, non_errorable e1 \207\1311) \226\136\167 to_val e1 = None
  | _ => to_val e1 = None
  end
  \226\134\146 (\226\136\128 \207\1311 e2' \207\1312 efs',
       exec_step \206\155.(sem) e1 \207\1311 (Val \207\1312 (e2', efs'))
       \226\134\146 \207\1311 = \207\1312 \226\136\167 e2 = e2' \226\136\167 efs = efs')
    \226\134\146 (|={E,E'}\226\150\183=> WP e2 @ s; E {{ \206\166 }}
                   \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, WP projT2 ef @ s; \226\138\164 {{ _, True }}))
      \226\138\162 WP e1 @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros ( ? Hpuredet ) "H".
Time (iApply (wp_lift_pure_step s E E'); try done).
Time {
Time by intros; eapply Hpuredet.
Time }
Time (iApply (step_fupd_wand with "H"); iIntros "H").
Time by iIntros ( e' efs' \207\131 (_, (->, ->))%Hpuredet ).
Time Qed.
Time
Lemma loop_non_errorable {T} {R} \207\131 (b : T \226\134\146 proc OpT (LoopOutcome T R))
  (init : T) : non_errorable (Loop b init) \207\131.
Time Proof.
Time (inversion 1).
Time Qed.
Time
Lemma spawn_non_errorable {T} \207\131 (e : proc OpT T) : non_errorable (Spawn e) \207\131.
Time Proof.
Time (destruct \207\131).
Time (intros Herr).
Time (apply bind_pure_no_err in Herr).
Time rewrite /fst_lift in  {} Herr.
Time (inversion Herr).
Time Qed.
Time Lemma wait_non_errorable \207\131 : non_errorable Wait \207\131.
Time Proof.
Time (destruct \207\131).
Time (intros Herr).
Time (apply bind_pure_no_err in Herr).
Time rewrite /fst_lift in  {} Herr.
Time (inversion Herr).
Time Qed.
Time Lemma unregister_non_errorable \207\131 : non_errorable Unregister \207\131.
Time Proof.
Time (destruct \207\131).
Time (intros Herr).
Time (apply bind_pure_no_err in Herr).
Time rewrite /fst_lift in  {} Herr.
Time (inversion Herr).
Time Qed.
Time #[global]
Instance bind_proc_ctx  {T} {R} (f : T \226\134\146 proc OpT R):
 (LanguageCtx \206\155 (\206\187 x, Bind x f)).
Time Proof.
Time (split; auto).
Time -
Time (intros e1 \207\131 ? ? ? H).
Time (<ssreflect_plugin::ssrtclintros@0> induction e1 =>//=).
Time *
Time (inversion H as (?, (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (repeat eexists; eauto).
Time *
Time (do 2 eexists).
Time (destruct e1; split; eauto; try econstructor).
Time *
Time (inversion H; subst; do 2 eexists; split; econstructor).
Time *
Time (destruct \207\131 as (n, s)).
Time (destruct \207\1312 as (n2, s2)).
Time (destruct H as ([], (?, (?, ?)))).
Time (inversion H0; subst).
Time rewrite /fst_lift in  {} H.
Time (destruct H; subst).
Time (inversion H).
Time subst.
Time eexists (Ret tt, []),(pred n, s2).
Time (split; try econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists ; last  econstructor).
Time (rewrite /fst_lift; split; eauto).
Time *
Time (destruct \207\131 as (n, s)).
Time (destruct \207\1312 as (n2, s2)).
Time (destruct H as ([], (?, (?, ?)))).
Time (inversion H0; subst).
Time rewrite /fst_lift in  {} H.
Time (destruct H; subst).
Time (inversion H).
Time subst.
Time eexists (Ret tt, []),(1, s2).
Time (split; try econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists ; last  econstructor).
Time (rewrite /fst_lift; split; eauto).
Time *
Time (destruct \207\131 as (n, s)).
Time (destruct \207\1312 as (n2, s2)).
Time (destruct H as ([], (?, (?, ?)))).
Time (inversion H0; subst).
Time rewrite /fst_lift in  {} H.
Time (destruct H; subst).
Time (inversion H).
Time subst.
Time eexists (Ret tt, [existT _ (Bind e1 (\206\187 _, Unregister))]),(S n, s2).
Time (split; try econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists ; last  econstructor).
Time (rewrite /fst_lift; split; eauto).
Time -
Time (intros e1 \207\1311 Herr).
Time (<ssreflect_plugin::ssrtclintros@0> induction e1 =>//=).
Time *
Time (apply bind_pure_no_err in Herr; intuition).
Time *
Time left.
Time (destruct e1; eauto; try econstructor).
Time *
Time (apply bind_pure_no_err in Herr; intuition).
Time *
Time (apply bind_pure_no_err in Herr; intuition).
Time *
Time (apply bind_pure_no_err in Herr; intuition).
Time -
Time (intros e1 \207\131 ? ? ? ? H).
Time (<ssreflect_plugin::ssrtclintros@0> induction e1 =>//=).
Time *
Time (inversion H as (?, (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (inversion Hstep as (?, (?, (?, Hpure'))); inversion Hpure'; subst).
Time (repeat eexists; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (eexists; split; eauto).
Time -
Time (intros e1 \207\131 ? Herr).
Time (<ssreflect_plugin::ssrtclintros@0> induction e1 =>//=).
Time *
Time (do 2 apply bind_pure_no_err in Herr).
Time eauto.
Time *
Time (inversion Herr; eauto).
Time (destruct H1 as (?, (?, (?, Hp)))).
Time (inversion Hp).
Time *
Time (inversion Herr).
Time **
Time exfalso.
Time (eapply loop_non_errorable; eauto).
Time **
Time (destruct H1 as (?, (?, (?, Hp)))).
Time (inversion Hp).
Time *
Time (inversion Herr).
Time **
Time exfalso.
Time (eapply unregister_non_errorable; eauto).
Time **
Time (destruct H0 as (?, (?, (?, Hp)))).
Time (inversion Hp).
Time *
Time (inversion Herr).
Time **
Time exfalso.
Time (eapply wait_non_errorable; eauto).
Time **
Time (destruct H0 as (?, (?, (?, Hp)))).
Time (inversion Hp).
Time *
Time (inversion Herr).
Time **
Time exfalso.
Time (eapply spawn_non_errorable; eauto).
Time **
Time (destruct H0 as (?, (?, (?, Hp)))).
Time (inversion Hp).
Time Qed.
Time #[global]
Instance id_ctx  {T}: (LanguageCtx \206\155 (fun x : proc OpT T => x)).
Time Proof.
Time (split; intuition eauto).
Time Qed.
Time #[global]
Instance comp_ctx  {T1} {T2} {T3} (K : proc OpT T1 \226\134\146 proc OpT T2)
 (K' : proc OpT T2 \226\134\146 proc OpT T3):
 (LanguageCtx \206\155 K \226\134\146 LanguageCtx \206\155 K' \226\134\146 LanguageCtx \206\155 (\206\187 x, K' (K x))).
Time Proof.
Time (intros Hctx Hctx').
Time (split; intros).
Time -
Time by do 2 apply fill_not_val.
Time -
Time by do 2 apply fill_step_valid.
Time -
Time by do 2 apply fill_step_err.
Time -
Time (edestruct (@fill_step_inv_valid _ _ _ _ _ Hctx'); eauto; intuition).
Time {
Time (apply fill_not_val; auto).
Time }
Time subst.
Time (edestruct (@fill_step_inv_valid _ _ _ _ _ Hctx); eauto; intuition).
Time subst.
Time eauto.
Time -
Time (do 2 (apply fill_step_inv_err; auto)).
Time {
Time (apply fill_not_val; auto).
Time }
Time Qed.
Time
Lemma wp_bind_proc {T1} {T2} (f : T1 \226\134\146 proc OpT T2) 
  s E (e : proc OpT T1) \206\166 :
  WP e @ s; E {{ v, WP Bind (of_val v) f @ s; E {{ \206\166 }} }}
  \226\138\162 WP Bind e f @ s; E {{ \206\166 }}.
Time Proof.
Time by apply : {}wp_bind {}.
Time Qed.
Time
Lemma wp_bind_proc_val {T1} {T2} (f : T1 \226\134\146 proc OpT T2) 
  s E v \206\166 :
  \226\150\183 WP f v @ s; E {{ v, \206\166 v }} -\226\136\151 WP Bind (of_val v) f @ s; E {{ v, \206\166 v }}.
Time Proof.
Time iIntros "Hwp".
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_lift_step ; first  by auto).
Time iIntros ( \207\1311 ) "?".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (fupd_intro_mask' E \226\136\133) as "Hclose" ;
 first  set_solver).
Time iSplitL "".
Time {
Time iPureIntro.
Time (destruct s; auto).
Time (inversion 1).
Time }
Time iIntros "!> !>".
Time (iIntros ( ? ? ? Hstep ); iFrame).
Time iMod "Hclose".
Time (iModIntro; iFrame).
Time (inversion Hstep; subst; by iFrame).
Time Qed.
Time
Lemma wp_bind_proc_subst {T1} {T2} (f : T1 \226\134\146 proc OpT T2) 
  s E (e : proc OpT T1) \206\166 :
  WP e @ s; E {{ v, \226\150\183 WP f v @ s; E {{ \206\166 }} }} \226\138\162 WP Bind e f @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time iApply wp_bind_proc.
Time (iApply wp_wand_l; iFrame "H").
Time iIntros ( v ).
Time rewrite wp_bind_proc_val.
Time replace (fun v : T2 => \206\166 v) with \206\166 by auto.
Time eauto.
Time Qed.
Time
Lemma wp_bind_proc_subst_weak {T1} {T2} (f : T1 \226\134\146 proc OpT T2) 
  s E (e : proc OpT T1) \206\166 :
  WP e @ s; E {{ v, WP f v @ s; E {{ \206\166 }} }} \226\138\162 WP Bind e f @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time iApply wp_bind_proc_subst.
Time (iApply wp_wand_l; iFrame "H"; eauto).
Time Qed.
Time
Lemma wp_loop {T} {R} {s} {E} {\206\166} (b : T \226\134\146 proc OpT (LoopOutcome T R))
  (init : T) :
  WP b init
  @ s; E {{ \206\187 out,
              \226\150\183 WP match out with
                   | ContinueOutcome x => Loop b x
                   | DoneWithOutcome r => Ret r
                   end @ s; E {{ \206\166 }} }} \226\138\162 WP Loop b init @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "Hwp".
Time iApply (wp_lift_pure_det_step E _ (loop1 b init)).
Time {
Time (intros; destruct s; intuition eauto using loop_non_errorable).
Time }
Time -
Time (iIntros ( \207\1311 e2 \207\1312 efs ); inversion 1; subst; auto).
Time -
Time (iIntros "!> !> !>"; iSplitR ""; auto).
Time by iApply wp_bind_proc_subst.
Time Qed.
Time #[global]
Instance Call_atomic  {T} a (op : OpT T): (Atomic \206\155 a (Call op)).
Time Proof.
Time (intros ? ? ? ? (?, (?, (Hstep, Hpure))); inversion Hpure; subst).
Time (destruct a; try econstructor; eauto).
Time Qed.
Time #[global]Instance Ret_atomic  {T} (v : T): (Atomic \206\155 a (Ret v)).
Time Proof.
Time (intros ? ? ? ? ?).
Time (inversion 1).
Time Qed.
Time #[global]
Instance Ret_IntoValue  {T} (x : T): (IntoVal (Ret x : proc OpT T) x).
Time Proof.
Time rewrite //=.
Time Qed.
Time Lemma wp_ret {T} {s} {E} {\206\166} (v : T) : \206\166 v \226\138\162 WP Ret v @ s; E {{ \206\166 }}.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> iApply wp_value =>//=).
Time Qed.
Time End lifting.
Time Ltac wp_ret := iApply wp_ret.
Time Ltac wp_bind := iApply wp_bind_proc_subst_weak.
Time Ltac wp_loop := iApply wp_loop.
