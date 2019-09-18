Time From Transitions Require Import Relations Rewriting.
Time From Transitions Require Import Relations Rewriting.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Export Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time Require Import CSL.WeakestPre.
Time Require Export Spec.Layer.
Time Require Export CSL.WeakestPre.
Time From stdpp Require Import namespaces.
Time From iris.algebra Require Import gmap auth agree gset coPset.
Time From iris.base_logic.lib Require Import wsat.
Time From iris.proofmode Require Import tactics.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
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
Definition inv\206\163 : gFunctors :=
  #[ GFunctor (authRF (gmapURF positive (agreeRF (laterOF idOF))));
  GFunctor coPset_disjUR; GFunctor (gset_disjUR positive)].
Time
Class invPreG (\206\163 : gFunctors) : Set :=
 WsatPreG {inv_inPreG :>
            inG \206\163 (authR (gmapUR positive (agreeR (laterO (iPreProp \206\163)))));
           enabled_inPreG :> inG \206\163 coPset_disjR;
           disabled_inPreG :> inG \206\163 (gset_disjR positive)}.
Time Instance subG_inv\206\163  {\206\163}: (subG inv\206\163 \206\163 \226\134\146 invPreG \206\163).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite {+2}wp_unfold /wp_pre =>Heq).
Time solve_inG.
Time Qed.
Time Lemma wsat_alloc `{invPreG \206\163} : (|==> \226\136\131 _ : invG \206\163, wsat \226\136\151 ownE \226\138\164)%I.
Time Proof.
Time iIntros.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (\226\151\143 (\226\136\133 : gmap positive _)))
 as ( \206\179I ) "HI" ; first  by rewrite auth_auth_valid).
Time rewrite Heq.
Time iIntros "Hwand".
Time iIntros ( \207\131 ) "H".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (CoPset \226\138\164)) as ( \206\179E ) "HE" ;
 first  done).
Time iMod ("Hwand" with "H") as "(Hinterp&Hwp)".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (GSet \226\136\133)) as ( \206\179D ) "HD" ;
 first  done).
Time (iModIntro; iExists (WsatG _ _ _ _ \206\179I \206\179E \206\179D)).
Time rewrite wp_unfold /wp_pre.
Time (rewrite /wsat /ownE -lock; iFrame).
Time rewrite Heq.
Time by iApply "Hwp".
Time iExists \226\136\133.
Time rewrite fmap_empty big_opM_empty.
Time by iFrame.
Time Qed.
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
Time
Definition adequate_internal {\206\163} {OpT} {T} {\206\155 : Layer OpT} 
  (s : stuckness) (e1 : proc OpT T) (\207\1311 : State \206\155)
  (\207\134 : T \226\134\146 State \206\155 \226\134\146 iProp \206\163) k : iProp \206\163 :=
  ((\226\136\128 (n : nat) \207\1312 res,
      \226\140\156exec_n \206\155 e1 n \207\1311 (Val \207\1312 res)\226\140\157
      \226\134\146 Nat.iter (S k + S (S n)) (\206\187 P, |==> \226\150\183 P)%I
          (\226\136\131 v, \226\140\156res = existT _ v\226\140\157 \226\136\167 \207\134 v \207\1312))
   \226\136\167 (\226\136\128 n : nat,
        \226\140\156s = NotStuck\226\140\157
        \226\134\146 \226\140\156exec_partial_n \206\155 e1 n \207\1311 Err\226\140\157 \226\134\146 \226\150\183^(S k + S (S n)) False))%I.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite wp_unfold /wp_pre =>{+}->).
Time
Record adequate {OpT} {T} {\206\155 : Layer OpT} (s : stuckness) 
(e1 : proc OpT T) (\207\1311 : State \206\155) (\207\134 : T \226\134\146 State \206\155 \226\134\146 Prop) :={
 adequate_result :
  forall \207\1312 res, exec \206\155 e1 \207\1311 (Val \207\1312 res) \226\134\146 \226\136\131 v, res = existT _ v \226\136\167 \207\134 v \207\1312;
 adequate_not_stuck : s = NotStuck \226\134\146 \194\172 exec_partial \206\155 e1 \207\1311 Err}.
Time
Definition recv_adequate_internal {\206\163} {OpT} {T} {R} 
  {\206\155 : Layer OpT} (s : stuckness) (e1 : proc OpT T) 
  (rec : proc OpT R) (\207\1311 : State \206\155) (\207\134 : T \226\134\146 State \206\155 \226\134\146 iProp \206\163)
  (\207\134rec : State \206\155 \226\134\146 iProp \206\163) k :=
  ((\226\136\128 n \207\1312 res,
      \226\140\156exec_n \206\155 e1 n \207\1311 (Val \207\1312 res)\226\140\157
      \226\134\146 Nat.iter (S k + S (S n)) (\206\187 P, |==> \226\150\183 P)%I
          (\226\136\131 v, \226\140\156res = existT _ v\226\140\157 \226\136\167 \207\134 v \207\1312))
   \226\136\167 (\226\136\128 n \207\1312 res,
        \226\140\156rexec_n \206\155 e1 rec n \207\1311 (Val \207\1312 res)\226\140\157
        \226\134\146 (Nat.iter (S k + (5 + n))) (\206\187 P, |==> \226\150\183 P)%I (\207\134rec \207\1312))
     \226\136\167 (\226\136\128 n : nat,
          \226\140\156s = NotStuck\226\140\157
          \226\134\146 \226\140\156rexec_n \206\155 e1 rec n \207\1311 Err\226\140\157 \226\134\146 \226\150\183^(S k + (5 + n)) False))%I.
Time
Record recv_adequate {OpT} {T} {R} {\206\155 : Layer OpT} 
(s : stuckness) (e1 : proc OpT T) (rec : proc OpT R) 
(\207\1311 : State \206\155) (\207\134 : T \226\134\146 State \206\155 \226\134\146 Prop) (\207\134rec : State \206\155 \226\134\146 Prop) :={
 recv_adequate_normal_result :
  forall \207\1312 res, exec \206\155 e1 \207\1311 (Val \207\1312 res) \226\134\146 \226\136\131 v, res = existT _ v \226\136\167 \207\134 v \207\1312;
 recv_adequate_result :
  forall \207\1312 res, rexec \206\155 e1 (rec_singleton rec) \207\1311 (Val \207\1312 res) \226\134\146 \207\134rec \207\1312;
 recv_adequate_not_stuck :
  s = NotStuck \226\134\146 \194\172 rexec \206\155 e1 (rec_singleton rec) \207\1311 Err}.
Time
Record proc_seq_adequate {OpT} {T} {R} {\206\155 : Layer OpT} 
(s : stuckness) (es : proc_seq OpT T) (rec : proc OpT R) 
(\207\1311 : State \206\155) (\207\134 : T \226\134\146 State \206\155 \226\134\146 Prop) :={proc_seq_adequate_normal_result :
                                            forall \207\1312 res,
                                            proc_exec_seq \206\155 es
                                              (rec_singleton rec) \207\1311
                                              (Val \207\1312 res) \226\134\146 
                                            \207\134 res \207\1312;
                                           proc_seq_adequate_not_stuck :
                                            s = NotStuck
                                            \226\134\146 \194\172 proc_exec_seq \206\155 es
                                                 (rec_singleton rec) \207\1311 Err}.
Time Section adequacy.
Time Context {OpT : Type \226\134\146 Type}.
Time Context `{\206\155 : Layer OpT}.
Time Context `{irisG OpT \206\155 \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Notation world' E \207\131:= (wsat \226\136\151 ownE E \226\136\151 state_interp \207\131)%I (only parsing).
Time iIntros "H" ( \207\1311 ) "H\207\131".
Time Notation world \207\131:= (world' \226\138\164 \207\131) (only parsing).
Time
Notation wptp s t:= ([\226\136\151 list] ef \226\136\136 t, WP projT2 ef @ s; \226\138\164 {{ _, True }})%I.
Time
Lemma wp_step {T} s E e1 \207\1311 (e2 : proc OpT T) \207\1312 efs 
  \206\166 :
  exec_step \206\155 e1 \207\1311 (Val \207\1312 (e2, efs))
  \226\134\146 world' E \207\1311 \226\136\151 WP e1 @ s; E {{ \206\166 }}
    ==\226\136\151 \226\150\183 (|==> \226\151\135 (world' E \207\1312 \226\136\151 WP e2 @ s; E {{ \206\166 }} \226\136\151 wptp s efs)).
Time iMod ("H" with "H\207\131") as "(%&H)".
Time Proof.
Time rewrite {+1}wp_unfold /wp_pre.
Time iModIntro.
Time iSplit.
Time by destruct s.
Time done.
Time iIntros ( ? ) "[(Hw & HE & H\207\131) H]".
Time Qed.
Time (destruct (to_val e1) eqn:Hval).
Time {
Time (apply of_to_val in Hval).
Time rewrite /of_val in  {} Hval.
Time subst.
Time (inversion H; subst).
Time }
Time rewrite // uPred_fupd_eq.
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
Time
(<ssreflect_plugin::ssrtclseq@0> iMod ("H" $! \207\1311 with "H\207\131 [Hw HE]") as
 ">(Hw & HE & _ & H)" ; first  by iFrame).
Time Qed.
Time iMod ("H" $! e2 \207\1312 efs with "[//] [$Hw $HE]") as ">(Hw & HE & H)".
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
Time iIntros "!> !>".
Time iMod "H".
Time
(<ssreflect_plugin::ssrtclseq@0> <ssreflect_plugin::ssrtclseq@0> iMod
 fupd_intro_mask' as "Hclose" ; last  iModIntro ; first  by set_solver).
Time by iMod ("H" with "[$Hw $HE]") as ">($ & $ & $)".
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s; intuition; eapply Hsafe).
Time }
Time iNext.
Time Qed.
Time iIntros ( e2 \207\1312 efs ? ).
Time (destruct (Hstep \207\1311 e2 \207\1312 efs); auto; subst).
Time iMod "Hclose" as "_".
Time iFrame "H\207\131".
Time iMod "H".
Time (iApply "H"; auto).
Time
Lemma wptp_step {T} s e1 t1 t2 \207\1311 \207\1312 \206\166 :
  exec_pool \206\155 (existT T e1 :: t1) \207\1311 (Val \207\1312 t2)
  \226\134\146 world \207\1311 \226\136\151 WP e1 @ s; \226\138\164 {{ \206\166 }} \226\136\151 wptp s t1
    ==\226\136\151 \226\136\131 e2 t2',
          \226\140\156t2 = existT T e2 :: t2'\226\140\157
          \226\136\151 \226\150\183 (|==> \226\151\135 (world \207\1312 \226\136\151 WP e2 @ s; \226\138\164 {{ \206\166 }} \226\136\151 wptp s t2')).
Time Qed.
Time Proof.
Time iIntros ( Hstep%exec_pool_equiv_alt_val ) "(HW & He & Ht)".
Time
(<ssreflect_plugin::ssrtclseq@0>
 inversion Hstep as
  [T' e1' e2' ? efs ? [| ? t1'] t2' Heq1 Heq2 Heq3 Hstep'| ] ; last  by
 congruence).
Time rewrite //= in  {} Heq1  {} Heq2  {} Heq3.
Time -
Time (inversion Heq1 as [[Heq1' Heq2']]; subst).
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
Time (assert (e1 = e1') by eauto with *; subst).
Time Proof.
Time iIntros ( ? ) "H".
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (wp_lift_step_fupd s E1 _ e1)
  =>//; iIntros ( \207\1311 ) "H\207\1311").
Time (inversion Heq3; subst; eauto).
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
Time
(<ssreflect_plugin::ssrtclseq@0> iExists e2' , (t2' ++ efs); iSplitR ; first 
 eauto).
Time by apply of_to_val.
Time Qed.
Time iFrame "Ht".
Time (iApply wp_step; eauto with iFrame).
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
Time -
Time simplify_eq /=.
Time Proof.
Time iIntros ( ? ) "H".
Time (iApply wp_lift_atomic_step_fupd; [ done |  ]).
Time iIntros ( ? ) "?".
Time iMod ("H" with "[$]") as "[$ H]".
Time
(<ssreflect_plugin::ssrtclseq@0>
 iExists e1 , (t1' ++ existT _ e2' :: t2' ++ efs); iSplitR ; first  by eauto).
Time iDestruct "Ht" as "($ & He' & $)".
Time iIntros "!> * % !> !>".
Time by iApply "H".
Time iFrame "He".
Time (iApply wp_step; eauto with iFrame).
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
Time Qed.
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
Time
Lemma wptp_steps {T} s n e1 t1 t2 \207\1311 \207\1312 \206\166 :
  bind_rep_n n (exec_pool \206\155) (existT T e1 :: t1) \207\1311 (Val \207\1312 t2)
  \226\134\146 world \207\1311 \226\136\151 WP e1 @ s; \226\138\164 {{ \206\166 }} \226\136\151 wptp s t1
    \226\138\162 Nat.iter (S n) (\206\187 P, |==> \226\150\183 P)
        (\226\136\131 e2 t2',
           \226\140\156t2 = existT T e2 :: t2'\226\140\157
           \226\136\151 world \207\1312 \226\136\151 WP e2 @ s; \226\138\164 {{ \206\166 }} \226\136\151 wptp s t2').
Time Proof.
Time
(revert e1 t1 t2 \207\1311 \207\1312; simpl; <ssreflect_plugin::ssrtclintros@0>
  induction n as [| n IH] =>e1 t1 t2 \207\1311 \207\1312).
Time {
Time (inversion_clear 1; iIntros "(?&?&?)"; subst).
Time (iExists e1 , t1; iFrame; auto).
Time (iApply "H"; eauto).
Time }
Time iIntros ( Hsteps ) "H".
Time Qed.
Time (destruct Hsteps as (t1', (\207\1311', (Hexec, Hsteps)))).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (wptp_step with "H") as ( e1' t1'' )
  "[% H]" ; first  eauto; simplify_eq).
Time (iModIntro; iNext; iMod "H" as ">?").
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
Time by iApply IH.
Time {
Time by intros; eapply Hpuredet.
Time }
Time (iApply (step_fupd_wand with "H"); iIntros "H").
Time Qed.
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
Time
Lemma bupd_iter_mono n P Q :
  (P -\226\136\151 Q)
  -\226\136\151 Nat.iter n (\206\187 P, |==> \226\150\183 P)%I P -\226\136\151 Nat.iter n (\206\187 P, |==> \226\150\183 P)%I Q.
Time Proof.
Time iIntros "HPQ".
Time *
Time (inversion H as (?, (?, (Hstep, Hpure)))).
Time iInduction n as [| n IH] "IH".
Time (inversion Hpure; subst).
Time -
Time (simpl).
Time iApply "HPQ".
Time -
Time (simpl).
Time iIntros "Hiter".
Time iMod "Hiter".
Time (repeat eexists; eauto).
Time iModIntro.
Time iNext.
Time *
Time (do 2 eexists).
Time (destruct e1; split; eauto; try econstructor).
Time iApply ("IH" with "HPQ Hiter").
Time Qed.
Time *
Time (inversion H; subst; do 2 eexists; split; econstructor).
Time *
Time (destruct \207\131 as (n, s)).
Time (destruct \207\1312 as (n2, s2)).
Time (destruct H as ([], (?, (?, ?)))).
Time
Lemma bupd_iter_le n1 n2 P :
  n1 \226\137\164 n2
  \226\134\146 Nat.iter n1 (\206\187 P, |==> \226\150\183 P)%I P -\226\136\151 Nat.iter n2 (\206\187 P, |==> \226\150\183 P)%I P.
Time Proof.
Time iIntros ( Hle ).
Time (induction Hle; auto).
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
Time -
Time (simpl).
Time iIntros "Hiter".
Time iModIntro.
Time iNext.
Time iApply (IHHle with "Hiter").
Time rewrite /fst_lift in  {} H.
Time (destruct H; subst).
Time (inversion H).
Time Qed.
Time subst.
Time eexists (Ret tt, []),(1, s2).
Time (split; try econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> do 2 eexists ; last  econstructor).
Time (rewrite /fst_lift; split; eauto).
Time *
Time (destruct \207\131 as (n, s)).
Time (destruct \207\1312 as (n2, s2)).
Time
Lemma wptp_steps_state_inv {T} s n e1 t1 t2 \207\1311 \207\1312 
  \206\166 :
  bind_rep_n n (exec_pool \206\155) (existT T e1 :: t1) \207\1311 (Val \207\1312 t2)
  \226\134\146 world \207\1311 \226\136\151 WP e1 @ s; \226\138\164 {{ \206\166 }} \226\136\151 wptp s t1
    \226\138\162 Nat.iter (S n) (\206\187 P, |==> \226\150\183 P) (world \207\1312).
Time (destruct H as ([], (?, (?, ?)))).
Time (inversion H0; subst).
Time Proof.
Time iIntros ( ? ) "H".
Time (iPoseProof (wptp_steps with "H") as "H"; eauto).
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
Time (iApply (bupd_iter_mono with "[] H"); eauto).
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
Time iIntros "H".
Time (iDestruct "H" as ( ? ? ) "(?&?&?)"; iFrame).
Time (repeat eexists; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time Qed.
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time
Lemma bupd_iter_laterN_mono n P Q `{!Plain Q} :
  (P \226\138\162 Q) \226\134\146 Nat.iter n (\206\187 P, |==> \226\150\183 P)%I P \226\138\162 \226\150\183^n Q.
Time Proof.
Time (intros HPQ).
Time (<ssreflect_plugin::ssrtclintros@0> induction n as [| n IH] =>//=).
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time by rewrite IH bupd_plain.
Time (eexists; split; eauto).
Time *
Time (inversion H as ((?, ?), (?, (Hstep, Hpure)))).
Time (inversion Hpure; subst).
Time (eexists; split; eauto).
Time Qed.
Time
Lemma bupd_iter_frame_l n R Q :
  R \226\136\151 Nat.iter n (\206\187 P, |==> \226\150\183 P) Q \226\138\162 Nat.iter n (\206\187 P, |==> \226\150\183 P) (R \226\136\151 Q).
Time -
Time (intros e1 \207\131 ? Herr).
Time (<ssreflect_plugin::ssrtclintros@0> induction e1 =>//=).
Time Proof.
Time (induction n as [| n IH]; simpl; [ done |  ]).
Time by rewrite bupd_frame_l {+1}(later_intro R) -later_sep IH.
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
Time Qed.
Time (inversion Hp).
Time *
Time (inversion Herr).
Time
Lemma wptp_result {T} {T'} s n e1 t1 v2' t2 \207\1311 \207\1312 
  \207\134 :
  bind_rep_n n (exec_pool \206\155) (existT T e1 :: t1) \207\1311
    (Val \207\1312 (existT T' (of_val v2') :: t2))
  \226\134\146 world \207\1311
    \226\136\151 WP e1 @ s; \226\138\164 {{ v, \226\136\128 \207\131, state_interp \207\131 ={\226\138\164,\226\136\133}=\226\136\151 \226\140\156\207\134 v \207\131\226\140\157 }} \226\136\151 wptp s t1
    \226\138\162 \226\150\183^(S (S n)) \226\140\156\226\136\131 v2,
                     existT T (@of_val OpT _ v2) =
                     existT T' (@of_val OpT _ v2') \226\136\167 
                     \207\134 v2 \207\1312\226\140\157.
Time **
Time exfalso.
Time (eapply spawn_non_errorable; eauto).
Time **
Time (destruct H0 as (?, (?, (?, Hp)))).
Time (inversion Hp).
Time Qed.
Time Proof.
Time (intros).
Time rewrite wptp_steps // laterN_later.
Time apply : {}bupd_iter_laterN_mono {}.
Time (iDestruct 1 as ( e2 t2' ? ) "((Hw & HE & H\207\131) & H & _)"; simplify_eq).
Time (assert (Ret v2' = e2) by eauto with *; subst).
Time iDestruct (wp_value_inv' with "H") as "H".
Time rewrite uPred_fupd_eq.
Time iMod ("H" with "[$]") as ">(Hw & HE & H)".
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
Time iExists v2'.
Time subst.
Time eauto.
Time (iMod ("H" with "H\207\131 [$]") as ">(_ & _ & %)"; auto).
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
Time Qed.
Time iSplitL "".
Time {
Time iPureIntro.
Time (destruct s; auto).
Time (inversion 1).
Time }
Time iIntros "!> !>".
Time (iIntros ( ? ? ? Hstep ); iFrame).
Time
Lemma wp_safe {T} E (e : proc OpT T) \207\131 \206\166 :
  world' E \207\131 -\226\136\151 WP e @ E {{ \206\166 }} ==\226\136\151 \226\150\183 \226\140\156non_errorable e \207\131\226\140\157.
Time Proof.
Time rewrite wp_unfold /wp_pre.
Time iMod "Hclose".
Time (iModIntro; iFrame).
Time iIntros "(Hw&HE&H\207\131) H".
Time (destruct (to_val e) as [v| ] eqn:?).
Time {
Time iIntros "!> !> !%".
Time (inversion Hstep; subst; by iFrame).
Time by eapply val_non_errorable.
Time }
Time rewrite uPred_fupd_eq.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod ("H" with "H\207\131 [-]") as ">(?&?&%&?)" ;
 first  by iFrame).
Time done.
Time Qed.
Time
Lemma wp_bind_proc_subst {T1} {T2} (f : T1 \226\134\146 proc OpT T2) 
  s E (e : proc OpT T1) \206\166 :
  WP e @ s; E {{ v, \226\150\183 WP f v @ s; E {{ \206\166 }} }} \226\138\162 WP Bind e f @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time iApply wp_bind_proc.
Time (iApply wp_wand_l; iFrame "H").
Time Qed.
Time iIntros ( v ).
Time rewrite wp_bind_proc_val.
Time replace (fun v : T2 => \206\166 v) with \206\166 by auto.
Time eauto.
Time Qed.
Time
Lemma wptp_result' {T} {T'} s n e1 t1 v2' t2 \207\1311 \207\1312 
  \207\134 :
  bind_rep_n n (exec_pool \206\155) (existT T e1 :: t1) \207\1311
    (Val \207\1312 (existT T' (of_val v2') :: t2))
  \226\134\146 world \207\1311
    \226\136\151 WP e1 @ s; \226\138\164 {{ v, \226\136\128 \207\131, state_interp \207\131 ={\226\138\164,\226\136\133}=\226\136\151 \207\134 v \207\131 }} \226\136\151 wptp s t1
    \226\138\162 Nat.iter (S (S n)) (\206\187 P, |==> \226\150\183 P)%I
        (\226\136\131 v2,
           \226\140\156existT T (@of_val OpT _ v2) = existT T' (@of_val OpT _ v2')\226\140\157
           \226\136\167 \207\134 v2 \207\1312).
Time
Lemma wp_bind_proc_subst_weak {T1} {T2} (f : T1 \226\134\146 proc OpT T2) 
  s E (e : proc OpT T1) \206\166 :
  WP e @ s; E {{ v, WP f v @ s; E {{ \206\166 }} }} \226\138\162 WP Bind e f @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "H".
Time iApply wp_bind_proc_subst.
Time Proof.
Time (intros).
Time rewrite wptp_steps // (Nat_iter_S_r (S n)).
Time (iApply wp_wand_l; iFrame "H"; eauto).
Time iApply bupd_iter_mono.
Time Qed.
Time (iDestruct 1 as ( e2 t2' ? ) "((Hw & HE & H\207\131) & H & _)"; simplify_eq).
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
Time (assert (Ret v2' = e2) by eauto with *; subst).
Time by iApply wp_bind_proc_subst.
Time Qed.
Time iDestruct (wp_value_inv' with "H") as "H".
Time #[global]
Instance Call_atomic  {T} a (op : OpT T): (Atomic \206\155 a (Call op)).
Time Proof.
Time (intros ? ? ? ? (?, (?, (Hstep, Hpure))); inversion Hpure; subst).
Time rewrite uPred_fupd_eq.
Time iMod ("H" with "[$]") as ">(Hw & HE & H)".
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
Time iExists v2'.
Time (iMod ("H" with "H\207\131 [$]") as ">(_ & _ & ?)"; auto).
Time Qed.
Time
Lemma wptp_safe {T} {T'} n (e1 : proc OpT T) (e2 : proc OpT T') 
  t1 t2 \207\1311 \207\1312 \206\166 :
  bind_rep_n n (exec_pool \206\155) (existT T e1 :: t1) \207\1311 (Val \207\1312 t2)
  \226\134\146 existT T' e2 \226\136\136 t2
    \226\134\146 world \207\1311 \226\136\151 WP e1 {{ \206\166 }} \226\136\151 wptp NotStuck t1
      \226\138\162 \226\150\183^(S (S n)) \226\140\156non_errorable e2 \207\1312\226\140\157.
Time Proof.
Time (intros ? He2).
Time rewrite wptp_steps // laterN_later.
Time apply : {}bupd_iter_laterN_mono {}.
Time (iDestruct 1 as ( e2' t2' ? ) "(Hw & H & Htp)"; simplify_eq).
Time Ltac wp_ret := iApply wp_ret.
Time Ltac wp_bind := iApply wp_bind_proc_subst_weak.
Time Ltac wp_loop := iApply wp_loop.
Time (apply elem_of_cons in He2 as [Heq| ?]).
Time -
Time (inversion Heq; subst).
Time (assert (e2 = e2') as <- by eauto with *).
Time iMod (wp_safe with "Hw H") as "$".
Time -
Time iMod (wp_safe with "Hw [Htp]") as "$".
Time (iPoseProof (big_sepL_elem_of with "Htp") as "H"; eauto).
Time Qed.
Time
Lemma wptp_invariance {T} s n e1 t1 t2 \207\1311 \207\1312 \207\134 \206\166 :
  bind_rep_n n (exec_pool \206\155) (existT T e1 :: t1) \207\1311 (Val \207\1312 t2)
  \226\134\146 (state_interp \207\1312 ={\226\138\164,\226\136\133}=\226\136\151 \226\140\156\207\134\226\140\157)
    \226\136\151 world \207\1311 \226\136\151 WP e1 @ s; \226\138\164 {{ \206\166 }} \226\136\151 wptp s t1 \226\138\162 \226\150\183^
    (S (S n)) \226\140\156\207\134\226\140\157.
Time Proof.
Time (intros ?).
Time rewrite wptp_steps // bupd_iter_frame_l laterN_later.
Time apply : {}bupd_iter_laterN_mono {}.
Time (iIntros "[Hback H]"; iDestruct "H" as ( e2' t2' -> ) "[(Hw&HE&H\207\131) _]").
Time rewrite uPred_fupd_eq.
Time (iMod ("Hback" with "H\207\131 [$Hw $HE]") as "> (_ & _ & $)"; auto).
Time Qed.
Time End adequacy.
Time
Theorem adequacy_int_to_ext {T} OpT \206\163 \206\155 s (e : proc OpT T) 
  \207\131 \207\134 k :
  adequate_internal (\206\163:=\206\163) (\206\155:=\206\155) s e \207\131 (fun v \207\131 => \226\140\156\207\134 v \207\131\226\140\157)%I k
  \226\134\146 adequate s e \207\131 \207\134.
Time Proof.
Time (intros Hinternal).
Time split.
Time *
Time (intros ? ? Hexec).
Time (apply exec_equiv_exec_n in Hexec as (n, ?)).
Time (eapply (soundness (M:=iResUR \206\163) _ (S k + S (S n)))).
Time iDestruct Hinternal as "(Hres&_)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_laterN_mono ; first  by
 reflexivity; eauto).
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  first).
Time {
Time (iApply "Hres"; eauto).
Time }
Time {
Time eauto.
Time }
Time *
Time (intros ? Hexec).
Time (apply exec_partial_equiv_exec_partial_n in Hexec as (n, ?)).
Time (eapply (soundness (M:=iResUR \206\163) _ (S k + S (S n)))).
Time iDestruct Hinternal as "(_&Hnstuck)".
Time (iApply "Hnstuck"; eauto).
Time Qed.
Time Transparent lifted_crash_step.
Time
Lemma lifted_crash_non_err {OpT} (\206\155 : Layer OpT) :
  \226\136\128 (s1 : Proc.State) (ret : Return Proc.State ()),
    lifted_crash_step \206\155 s1 ret \226\134\146 ret \226\137\160 Err.
Time Proof.
Time (intros ? ?).
Time rewrite /lifted_crash_step.
Time (destruct ret; auto).
Time (destruct s1).
Time (inversion 1).
Time *
Time (inversion H0).
Time *
Time (destruct H0 as (?, ((?, ?), (?, ?)))).
Time by apply crash_non_err in H1.
Time Qed.
Time
Lemma lifted_finish_non_err {OpT} (\206\155 : Layer OpT) :
  \226\136\128 (s1 : Proc.State) (ret : Return Proc.State ()),
    lifted_finish_step \206\155 s1 ret \226\134\146 ret \226\137\160 Err.
Time Proof.
Time (intros ? ?).
Time rewrite /lifted_finish_step.
Time (destruct ret; auto).
Time (destruct s1).
Time (inversion 1).
Time *
Time (inversion H0).
Time *
Time (destruct H0 as (?, ((?, ?), (?, ?)))).
Time by apply finish_non_err in H1.
Time Qed.
Time
Lemma recv_adequacy_int_non_stuck {T} {R} OpT \206\163 \206\155 
  (e : proc OpT T) (rec : proc OpT R) \207\131 \207\134 \207\134rec k :
  recv_adequate_internal (\206\163:=\206\163) (\206\155:=\206\155) NotStuck e rec \207\131 \207\134 \207\134rec k
  \226\134\146 \194\172 rexec \206\155 e (rec_singleton rec) \207\131 Err.
Time Proof.
Time (intros Hinternal Hrexec).
Time
(<ssreflect_plugin::ssrtclseq@0>
 apply rexec_equiv_rexec_n'_err in Hrexec as (n, ?Hrexec) ; last  by
 eapply lifted_crash_non_err).
Time (eapply (soundness (M:=iResUR \206\163) _ (S k + (5 + n)))).
Time iDestruct Hinternal as "(_&Hnstuck)".
Time (iApply "Hnstuck"; eauto).
Time Qed.
Time
Theorem recv_adequacy_int_to_ext {T} {R} OpT \206\163 \206\155 (e : proc OpT T)
  (rec : proc OpT R) \207\131 \207\134 \207\134rec k :
  recv_adequate_internal (\206\163:=\206\163) (\206\155:=\206\155) NotStuck e rec \207\131
    (fun v \207\131 => \226\140\156\207\134 v \207\131\226\140\157)%I (fun \207\131 => \226\140\156\207\134rec \207\131\226\140\157)%I k
  \226\134\146 recv_adequate NotStuck e rec \207\131 \207\134 \207\134rec.
Time Proof.
Time (intros Hinternal).
Time
(assert (\194\172 rexec \206\155 e (rec_singleton rec) \207\131 Err) by
  (eapply recv_adequacy_int_non_stuck; eauto)).
Time (split; auto).
Time -
Time (intros ? ? Hexec).
Time (apply exec_equiv_exec_n in Hexec as (n, ?)).
Time (eapply (soundness (M:=iResUR \206\163) _ (S k + S (S n)))).
Time iDestruct Hinternal as "(Hres&_&_)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_laterN_mono ; first  by
 reflexivity; eauto).
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  first).
Time {
Time (iApply "Hres"; eauto).
Time }
Time {
Time eauto.
Time }
Time -
Time (intros ? [] Hexec).
Time
(apply rexec_equiv_rexec_n'_val in Hexec as (n, ?); eauto
  using lifted_crash_non_err).
Time (eapply (soundness (M:=iResUR \206\163) _ (S k + (5 + n)))).
Time iDestruct Hinternal as "(_&Hres&_)".
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_laterN_mono ; first  by
 reflexivity; eauto).
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  first).
Time {
Time (iApply "Hres"; eauto).
Time }
Time {
Time eauto.
Time }
Time Qed.
Time
Lemma exec_partial_n_err_alt {T} OpT (\206\155 : Layer OpT) 
  (e : proc OpT T) n \207\131 :
  exec_partial_n \206\155 e n \207\131 Err
  \226\134\146 \226\136\131 n' tp1 tp2 Terr err \207\1312,
      n' \226\137\164 n
      \226\136\167 exec_step \206\155 err \207\1312 Err
        \226\136\167 bind_rep_n n' (exec_pool \206\155) [existT T e] \207\131
            (Val \207\1312 (tp1 ++ existT Terr err :: tp2)).
Time Proof.
Time (intros Hpartial).
Time (assert (Hpartial_r : bind_rep_r_n n (exec_pool \206\155) [existT T e] \207\131 Err)).
Time {
Time (apply bind_rep_lr_n in Hpartial).
Time intuition.
Time }
Time
(apply bind_rep_r_n_err_inv in Hpartial_r
  as (n', (t2, (\207\1312, (Hle, (Hpartial', Hexec)))))).
Time (apply bind_rep_lr_n_val in Hpartial').
Time (apply exec_pool_equiv_alt_err in Hexec).
Time (inversion Hexec; subst; try congruence).
Time (repeat eexists; eauto).
Time Qed.
Time
Theorem wp_strong_adequacy_internal {T} OpT \206\163 \206\155 `{invPreG \206\163} 
  s (e : proc OpT T) \207\131 \207\134 k :
  (\226\136\128 `{Hinv : invG \206\163},
     Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
       (|={\226\138\164}=> \226\136\131 stateI : State \206\155 \226\134\146 iProp \206\163,
                  let _ : irisG OpT \206\155 \206\163 := IrisG _ _ _ Hinv stateI in
                  stateI \207\131
                  \226\136\151 WP e @ s; \226\138\164 {{ v, \226\136\128 \207\131, stateI \207\131 ={\226\138\164,\226\136\133}=\226\136\151 \207\134 v \207\131 }})%I)
  \226\138\162 adequate_internal s e \207\131 \207\134 k.
Time Proof.
Time (iIntros "Hwp"; iSplit).
Time -
Time iIntros ( n \207\131' (T', v') Hexec ).
Time (destruct Hexec as (tp, Hpartial)).
Time subst.
Time (simpl).
Time rewrite Nat_iter_add.
Time iMod wsat_alloc as ( Hinv ) "[Hw HE]".
Time iSpecialize ("Hwp" $! _).
Time iModIntro.
Time iNext.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply
 (bupd_iter_mono k with "[Hw HE] [Hwp]") ; last  by iApply "Hwp").
Time iIntros "Hwp".
Time rewrite {+1}uPred_fupd_eq.
Time iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
Time iDestruct "Hwp" as ( Istate ) "[HI Hwp]".
Time
iPoseProof (@wptp_result' _ _ _ (IrisG _ _ _ Hinv Istate) with "[-]") as "H".
Time {
Time eauto.
Time }
Time {
Time iFrame.
Time rewrite //=.
Time }
Time iApply (bupd_iter_mono (S (S n)) with "[] H").
Time iIntros "H".
Time iDestruct "H" as ( v'' Heq ) "?".
Time (inversion Heq; subst).
Time (iExists v''; iSplit; auto).
Time -
Time (<ssreflect_plugin::ssrtclseq@0> destruct s ; last  done).
Time iIntros ( n ? Hpartial ).
Time
(edestruct (exec_partial_n_err_alt \206\155 e)
  as (n', (tp1, (typ2, (Terr, (err, (\207\1312, (Hle, (Hexec, Hpartial'))))))));
  eauto).
Time
(<ssreflect_plugin::ssrtclseq@0> iAssert
 (\226\150\183^(S k + S (S n')) \226\140\156@non_errorable _ _ \206\155 err \207\1312\226\140\157)%I with "[Hwp]" as "Herr"
 ; last  first).
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (laterN_le (S k + S (S n'))) ; first 
 by lia).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply laterN_mono ; last  by iApply "Herr").
Time (iPureIntro; eauto).
Time }
Time rewrite laterN_plus.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_laterN_mono ; first  by
 reflexivity).
Time iMod wsat_alloc as ( Hinv ) "[Hw HE]".
Time iSpecialize ("Hwp" $! _).
Time iModIntro.
Time iNext.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply
 (bupd_iter_mono k with "[Hw HE] [Hwp]") ; last  by iApply "Hwp").
Time iIntros "Hwp".
Time rewrite {+1}uPred_fupd_eq.
Time iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
Time iDestruct "Hwp" as ( Istate ) "[HI Hwp]".
Time
(iApply (@wptp_safe _ _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame).
Time set_solver +.
Time Qed.
Time
Theorem wp_strong_adequacy {T} OpT \206\163 \206\155 `{invPreG \206\163} 
  s (e : proc OpT T) \207\131 \207\134 k :
  (\226\136\128 `{Hinv : invG \206\163},
     Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
       (|={\226\138\164}=> \226\136\131 stateI : State \206\155 \226\134\146 iProp \206\163,
                  let _ : irisG OpT \206\155 \206\163 := IrisG _ _ _ Hinv stateI in
                  stateI \207\131
                  \226\136\151 WP e @ s; \226\138\164 {{ v, \226\136\128 \207\131, stateI \207\131 ={\226\138\164,\226\136\133}=\226\136\151 \226\140\156\207\134 v \207\131\226\140\157 }})%I)
  \226\134\146 adequate s e \207\131 \207\134.
Time Proof.
Time (intros Hwp).
Time (unshelve (eapply @adequacy_int_to_ext); eauto).
Time iApply wp_strong_adequacy_internal.
Time iIntros ( Hinv ).
Time iApply Hwp.
Time Qed.
Time
Theorem wp_adequacy {T} OpT \206\163 \206\155 `{invPreG \206\163} s (e : proc OpT T) 
  \207\131 \207\134 k :
  (\226\136\128 `{Hinv : invG \206\163},
     Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
       (|={\226\138\164}=> \226\136\131 stateI : State \206\155 \226\134\146 iProp \206\163,
                  let _ : irisG OpT \206\155 \206\163 := IrisG _ _ _ Hinv stateI in
                  stateI \207\131 \226\136\151 WP e @ s; \226\138\164 {{ v, \226\140\156\207\134 v\226\140\157 }})%I)
  \226\134\146 adequate s e \207\131 (\206\187 v _, \207\134 v).
Time Proof.
Time (intros Hwp).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (wp_strong_adequacy _ _ _ _ k)
 =>Hinv).
Time iPoseProof (Hwp _) as "Hwp".
Time iApply (bupd_iter_mono with "[] Hwp").
Time iIntros "Hwp'".
Time iMod "Hwp'" as ( stateI ) "[H\207\131 H]".
Time iExists stateI.
Time iIntros "{$H\207\131} !>".
Time iApply (wp_wand with "H").
Time iIntros ( v ? \207\131' ) "_".
Time (iMod (fupd_intro_mask' \226\138\164 \226\136\133) as "_"; auto).
Time Qed.
Time
Theorem wp_invariance {T} OpT \206\163 \206\155 `{invPreG \206\163} s (e : proc OpT T) 
  \207\1311 t2 \207\1312 \207\134 k :
  (\226\136\128 `{Hinv : invG \206\163},
     Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
       (|={\226\138\164}=> \226\136\131 stateI : State \206\155 \226\134\146 iProp \206\163,
                  let _ : irisG OpT \206\155 \206\163 := IrisG _ _ _ Hinv stateI in
                  stateI \207\1311
                  \226\136\151 WP e @ s; \226\138\164 {{ _, True }} \226\136\151 (stateI \207\1312 ={\226\138\164,\226\136\133}=\226\136\151 \226\140\156\207\134\226\140\157))%I)
  \226\134\146 exec_partial \206\155 e \207\1311 (Val \207\1312 t2) \226\134\146 \207\134.
Time Proof.
Time (intros Hwp Hpartial).
Time (apply bind_star_inv_rep_n in Hpartial as (n, Hpartial)).
Time (eapply (soundness (M:=iResUR \206\163) _ (S k + S (S n)))).
Time rewrite laterN_plus.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_laterN_mono ; first  by
 reflexivity).
Time iMod wsat_alloc as ( Hinv ) "[Hw HE]".
Time specialize (Hwp _).
Time iModIntro.
Time iNext.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (bupd_iter_mono k with "[Hw HE] []")
 ; last  by iApply Hwp).
Time iIntros "Hwp".
Time rewrite {+1}uPred_fupd_eq.
Time iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
Time iDestruct "Hwp" as ( Istate ) "(HIstate & Hwp & Hclose)".
Time
(iApply (@wptp_invariance _ _ _ (IrisG _ _ _ Hinv Istate)); eauto with iFrame).
Time Qed.
Time
Corollary wp_invariance' {T} OpT \206\163 \206\155 `{invPreG \206\163} 
  s (e : proc OpT T) \207\1311 t2 \207\1312 \207\134 :
  (\226\136\128 `{Hinv : invG \206\163},
     (|={\226\138\164}=> \226\136\131 stateI : State \206\155 \226\134\146 iProp \206\163,
                let _ : irisG OpT \206\155 \206\163 := IrisG _ _ _ Hinv stateI in
                stateI \207\1311
                \226\136\151 WP e @ s; \226\138\164 {{ _, True }}
                  \226\136\151 (stateI \207\1312 -\226\136\151 \226\136\131 E, |={\226\138\164,E}=> \226\140\156\207\134\226\140\157))%I)
  \226\134\146 exec_partial \206\155 e \207\1311 (Val \207\1312 t2) \226\134\146 \207\134.
Time Proof.
Time (intros Hwp).
Time
(<ssreflect_plugin::ssrtclseq@0> eapply wp_invariance with (k := O) ; first 
 done).
Time (intros Hinv).
Time iMod (Hwp Hinv) as ( stateI ) "(? & ? & H\207\134)".
Time iModIntro.
Time iExists stateI.
Time iFrame.
Time iIntros "H\207\131".
Time iDestruct ("H\207\134" with "H\207\131") as ( E ) ">H\207\134".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod fupd_intro_mask' as "_" ; last  by
 iModIntro).
Time solve_ndisj.
Time Qed.
Time Import RelationNotations.
Time
Lemma exec_rec_iter_split {R} OpT (\206\155 : Layer OpT) 
  (rec : proc OpT R) \207\131halt ret :
  (_ <- seq_star (_ <- lifted_crash_step \206\155; exec_halt \206\155 rec);
   _ <- lifted_crash_step \206\155; exec_halt \206\155 rec) \207\131halt ret
  \226\134\146 \226\136\131 \207\131crash \207\131rec : State \206\155,
      seq_star (_ <- lifted_crash_step \206\155; exec_halt \206\155 rec) \207\131halt
        (Val \207\131crash ())
      \226\136\167 lifted_crash_step \206\155 \207\131crash (Val \207\131rec ()) \226\136\167 exec_halt \206\155 rec \207\131rec ret.
Time Proof.
Time (intros Hrec).
Time (destruct ret as [b t| ]).
Time {
Time (destruct Hrec as ([], (\207\131halt_rec, (Hhd, ([], (?, (?, ?))))))).
Time (do 2 eexists; split_and !; eauto).
Time }
Time {
Time (destruct Hrec as [Hstar_err| ([], (\207\131halt_rec, (Hhd, Hrest)))]).
Time -
Time (remember Err as ret eqn:Heq ).
Time (revert Heq; induction Hstar_err; intros; try congruence; subst).
Time *
Time (edestruct IHHstar_err as (\207\131crash, (\207\131rec_err, (Hstar, ?))); auto).
Time (exists \207\131crash,\207\131rec_err; split; auto).
Time (econstructor; eauto).
Time *
Time (destruct H as [| ([], (\207\131, (?, ?)))]).
Time {
Time exfalso.
Time (eapply lifted_crash_non_err; eauto).
Time }
Time (exists x,\207\131; split; auto).
Time econstructor.
Time -
Time (destruct Hrest as [| ([], (\207\131, (?, ?)))]).
Time {
Time exfalso.
Time (eapply lifted_crash_non_err; eauto).
Time }
Time (do 2 eexists; split_and !; eauto).
Time }
Time Qed.
Time
Lemma rexec_n_iter_split {R} OpT (\206\155 : Layer OpT) (rec : proc OpT R) 
  \207\131halt ret n2 n3 :
  (_ <- seq_star_exec_steps \206\155 rec n2; _ <- lifted_crash_step \206\155;
   _ <- exec_n \206\155 rec n3; pure ()) \207\131halt ret
  \226\134\146 \226\136\131 (\207\131crash \207\131rec : State \206\155) n2' n3',
      (n2 + n3 >= n2' + n3')%nat
      \226\136\167 (seq_star_exec_steps \206\155 rec n2') \207\131halt (Val \207\131crash ())
        \226\136\167 lifted_crash_step \206\155 \207\131crash (Val \207\131rec ())
          \226\136\167 (_ <- exec_n \206\155 rec n3'; pure ()) \207\131rec ret.
Time Proof.
Time (intros Hrec).
Time (destruct ret as [b t| ]).
Time {
Time (destruct Hrec as ([], (\207\131halt_rec, (Hhd, ([], (?, (?, ?))))))).
Time (do 4 eexists; split_and !; eauto).
Time }
Time {
Time (destruct Hrec as [Hstar_err| ([], (\207\131halt_rec, (Hhd, Hrest)))]).
Time -
Time (remember Err as ret eqn:Heq ).
Time (revert Heq; induction Hstar_err; intros; try congruence; subst).
Time *
Time
(edestruct IHHstar_err
  as (\207\131crash, (\207\131rec_err, (n2', (n3', (Heq, (Hstar, ?)))))); auto).
Time
(<ssreflect_plugin::ssrtclseq@0> eexists \207\131crash,\207\131rec_err,_,_; split ; last 
 first).
Time {
Time (split; eauto).
Time (econstructor; eauto).
Time }
Time {
Time lia.
Time }
Time *
Time (<ssreflect_plugin::ssrtclseq@0> do 4 eexists; split ; last  first).
Time {
Time split.
Time econstructor.
Time split.
Time eauto.
Time (left; eauto).
Time }
Time {
Time lia.
Time }
Time -
Time (destruct Hrest as [| ([], (\207\131, (?, ?)))]).
Time {
Time exfalso.
Time (eapply lifted_crash_non_err; eauto).
Time }
Time (do 4 eexists; split_and !; eauto).
Time }
Time Qed.
Time
Definition recv_idemp {R} {OpT} \206\163 (\206\155 : Layer OpT) 
  `{invPreG \206\163} s (rec : proc OpT R) \207\134inv \207\134rec :=
  (\226\150\161 (\226\136\128 `{Hinv : invG \206\163} \207\1311 \207\1311' (Hcrash : lifted_crash_step \206\155 \207\1311 (Val \207\1311' tt)),
        \207\134inv \207\1311
        ={\226\138\164}=\226\136\151 \226\136\131 stateI : State \206\155 \226\134\146 iProp \206\163,
                 let _ : irisG OpT \206\155 \206\163 := IrisG _ _ _ Hinv stateI in
                 stateI \207\1311'
                 \226\136\151 WP rec @ s; \226\138\164 {{ _, \226\136\128 \207\131, stateI \207\131 ={\226\138\164,\226\136\133}=\226\136\151 \207\134rec \207\131 }}
                   \226\136\151 (\226\136\128 \207\1312', stateI \207\1312' ={\226\138\164,\226\136\133}=\226\136\151 \207\134inv \207\1312')))%I.
Time
Lemma recv_idemp_adequacy_inv {R} OpT \206\163 (\206\155 : Layer OpT) 
  `{invPreG \206\163} s (rec : proc OpT R) \207\134inv \207\134rec \207\131halt 
  \207\131crash k0 :
  seq_star_exec_steps \206\155 rec k0 \207\131halt (Val \207\131crash tt)
  \226\134\146 recv_idemp s rec \207\134inv \207\134rec
    -\226\136\151 (|==> \226\151\135 \207\134inv \207\131halt)
       -\226\136\151 Nat.iter (S k0) (\206\187 P, |==> \226\150\183 P)%I (|==> \226\151\135 \207\134inv \207\131crash).
Time Proof.
Time iIntros ( Hstar ) "#Hwp_rec Hhalt".
Time (remember (Val \207\131crash ()) as ret eqn:Heq ).
Time
(<ssreflect_plugin::ssrtclseq@0> iInduction Hstar as
 [| k0 \207\131halt \207\131halt' \207\131mid ret ? m Hcrash Hrep Hind| ] "IH" ; last  by
 congruence).
Time {
Time (inversion Heq; subst).
Time (iIntros "!> !>"; auto).
Time }
Time (inversion Heq; subst).
Time rewrite (Nat_iter_S (S m + S k)).
Time rewrite Nat_iter_add.
Time iMod wsat_alloc as ( Hinv'' ) "[Hw HE]".
Time iSpecialize ("Hwp_rec" $! Hinv'').
Time iSpecialize ("Hwp_rec" $! _ _ Hcrash).
Time rewrite uPred_fupd_eq.
Time iMod "Hhalt".
Time iModIntro.
Time iMod "Hhalt".
Time iNext.
Time iMod ("Hwp_rec" with "Hhalt [$Hw $HE]") as ">(Hw & HE & Hrest)".
Time iDestruct "Hrest" as ( stateI' ) "(Hs&Hwp&Hinv)".
Time iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
Time {
Time (eapply Hrep).
Time }
Time {
Time iFrame.
Time done.
Time }
Time iApply (bupd_iter_mono with "[Hinv] H").
Time iIntros "(Hw&HE&Hstate)".
Time (iApply "IH"; auto).
Time (iSpecialize ("Hinv" with "[Hstate]"); eauto).
Time rewrite /uPred_fupd_def.
Time by iMod ("Hinv" with "[$Hw $HE]") as ">(?&?&$)".
Time Qed.
Time
Definition wp_recovery {T} {R} {OpT} \206\163 \206\155 `{invPreG \206\163} 
  s (e : proc OpT T) (rec : proc OpT R) \207\1311 \207\134 \207\134rec 
  k :=
  (Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
     (\226\136\131 \207\134inv : State \206\155 \226\134\146 iProp \206\163,
        \226\136\128 `{Hinv : invG \206\163},
          |={\226\138\164}=> \226\136\131 stateI : State \206\155 \226\134\146 iProp \206\163,
                    let _ : irisG OpT \206\155 \206\163 := IrisG _ _ _ Hinv stateI in
                    stateI \207\1311
                    \226\136\151 WP e @ s; \226\138\164 {{ v, \226\136\128 \207\131, stateI \207\131 ={\226\138\164,\226\136\133}=\226\136\151 \207\134 v \207\131 }}
                      \226\136\151 (\226\136\128 \207\1312', stateI \207\1312' ={\226\138\164,\226\136\133}=\226\136\151 \207\134inv \207\1312')
                        \226\136\151 recv_idemp s rec \207\134inv \207\134rec))%I.
Time
Theorem wp_recovery_adequacy_internal {T} {R} OpT 
  \206\163 \206\155 `{invPreG \206\163} s (e : proc OpT T) (rec : proc OpT R) 
  \207\1311 \207\134 (\207\134rec : State \206\155 \226\134\146 iProp \206\163) k :
  s = NotStuck
  \226\134\146 wp_recovery s e rec \207\1311 \207\134 \207\134rec k
    \226\138\162 recv_adequate_internal s e rec \207\1311 \207\134 \207\134rec k.
Time Proof.
Time iIntros ( ? ) "Hwp".
Time (iSplit; [  | iSplit ]).
Time -
Time iIntros ( ? \207\1312 ? Hexec ).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply
 (wp_strong_adequacy_internal with "[Hwp]") ; last  eauto).
Time iIntros ( Hinv ).
Time iApply (bupd_iter_mono with "[] Hwp").
Time iIntros "Hwp".
Time iDestruct "Hwp" as ( \207\134inv ) "Hwp".
Time iSpecialize ("Hwp" $! Hinv).
Time iMod "Hwp" as ( stateI ) "(H\207\131&Hwp_e&?&_)".
Time iExists stateI.
Time (iIntros "{$H\207\131} !> "; auto).
Time -
Time iIntros ( n0 \207\1312 [] Hrexec_n ).
Time (inversion Hrexec_n as [? ? n k0 n3 Heq Hrexec]; subst).
Time clear Hrexec_n.
Time (destruct Hrexec as (tp, (\207\131halt, (Hpartial, Hrec)))).
Time (destruct Hrec as ([], (\207\131crash, (Hstar, Hfin)))).
Time (destruct Hfin as ([], (\207\131crash', (Hcrash, Hfin)))).
Time (destruct Hfin as (?, (?, (Hexec, Hp)))).
Time (inversion Hp; subst).
Time clear Hp.
Time
(<ssreflect_plugin::ssrtclseq@0> iPoseProof
 (wp_strong_adequacy_internal NotStuck rec \207\131crash' 
    (\206\187 _ s, \207\134rec s) (S k + S n + S k0) with "[Hwp]") as "(Had&_)" ; last 
 first).
Time {
Time
(assert
  (Heq : (S k + (5 + (n + k0 + n3)) = S (S k + S n + S k0) + S (S n3))%nat)).
Time {
Time lia.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  first).
Time {
Time rewrite Heq.
Time iApply "Had".
Time eauto.
Time }
Time iIntros "H".
Time iDestruct "H" as ( ? ? ) "$".
Time }
Time iIntros ( Hinv ).
Time rewrite Nat_iter_add.
Time rewrite Nat_iter_add.
Time iMod wsat_alloc as ( Hinv' ) "[Hw HE]".
Time iApply (bupd_iter_mono with "[Hw HE] Hwp").
Time iIntros "Hwp".
Time iDestruct "Hwp" as ( \207\134inv ) "Hwp".
Time iSpecialize ("Hwp" $! Hinv').
Time rewrite uPred_fupd_eq.
Time iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hrest)".
Time iDestruct "Hrest" as ( stateI ) "(H\207\131&Hwp_e&Hinv&#Hwp_rec)".
Time
iAssert (Nat.iter (S n) (\206\187 P, |==> \226\150\183 P)%I (|==> \226\151\135 \207\134inv \207\131halt))%I with
 "[Hw HE H\207\131 Hwp_e Hinv]" as "H\207\131halt".
Time {
Time iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
Time {
Time (eapply Hpartial).
Time }
Time {
Time iFrame.
Time done.
Time }
Time iApply (bupd_iter_mono with "[Hinv] H").
Time iIntros "(Hw&HE&Hstate)".
Time iSpecialize ("Hinv" with "Hstate").
Time (iMod ("Hinv" with "[$Hw $HE]") as "(?&?&$)"; auto).
Time }
Time (iApply (bupd_iter_mono with "[] H\207\131halt"); iIntros "H\207\131halt").
Time clear Hpartial.
Time
iAssert (Nat.iter (S k0) (\206\187 P, |==> \226\150\183 P)%I (|==> \226\151\135 \207\134inv \207\131crash))%I with
 "[H\207\131halt]" as "Hinv'".
Time {
Time (unshelve (iApply recv_idemp_adequacy_inv; eauto); eauto).
Time }
Time (iApply (bupd_iter_mono with "[] Hinv'"); iIntros ">>Hinv'").
Time iSpecialize ("Hwp_rec" $! Hinv \207\131crash \207\131crash' Hcrash with "Hinv'").
Time (iMod "Hwp_rec" as ( stateI'' ) "[H\207\131 [H _]]"; eauto).
Time iExists stateI''.
Time (iIntros "{$H\207\131} !> "; auto).
Time -
Time iIntros ( n _ Hrexec_n ).
Time (inversion Hrexec_n as [? ? n1 n2 n3 Heq Hrexec_n']; subst).
Time (destruct Hrexec_n' as [| (tp, (\207\131halt, (Hpartial, Hrec)))]).
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply laterN_le ; last  first).
Time {
Time (iApply (wp_strong_adequacy_internal with "[Hwp]"); eauto).
Time iIntros ( Hinv ).
Time iApply (bupd_iter_mono with "[] Hwp").
Time iIntros "Hwp".
Time iDestruct "Hwp" as ( \207\134inv ) "Hwp".
Time iSpecialize ("Hwp" $! Hinv).
Time iMod "Hwp" as ( stateI ) "(H\207\131&Hwp_e&?&_)".
Time iExists stateI.
Time (iIntros "{$H\207\131} !> "; auto).
Time }
Time {
Time lia.
Time }
Time }
Time
(edestruct @rexec_n_iter_split
  as (\207\131crash, (\207\131rec_err, (k0, (n', (Hle, (Hstar, (Hcrash, Herr))))))); eauto).
Time (apply bind_pure_no_err in Herr).
Time
(<ssreflect_plugin::ssrtclseq@0> iPoseProof
 (wp_strong_adequacy_internal NotStuck rec \207\131rec_err 
    (\206\187 _ s, \207\134rec s) (S k + S n1 + S k0) with "[Hwp]") as "(_&Hnst)" ; last 
 first).
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iApply laterN_le ; last  iApply "Hnst";
  eauto).
Time lia.
Time }
Time iIntros ( Hinv ).
Time rewrite Nat_iter_add.
Time rewrite Nat_iter_add.
Time iMod wsat_alloc as ( Hinv' ) "[Hw HE]".
Time iApply (bupd_iter_mono with "[Hw HE] Hwp").
Time iIntros "Hwp".
Time iDestruct "Hwp" as ( \207\134inv ) "Hwp".
Time iSpecialize ("Hwp" $! Hinv').
Time rewrite uPred_fupd_eq.
Time iMod ("Hwp" with "[$Hw $HE]") as ">(Hw & HE & Hrest)".
Time iDestruct "Hrest" as ( stateI ) "(H\207\131&Hwp_e&Hinv&#Hwp_rec)".
Time
iAssert (Nat.iter (S n1) (\206\187 P, |==> \226\150\183 P)%I (|==> \226\151\135 \207\134inv \207\131halt))%I with
 "[Hw HE H\207\131 Hwp_e Hinv]" as "H\207\131halt".
Time {
Time iDestruct (wptp_steps_state_inv with "[-Hinv]") as "H".
Time {
Time (eapply Hpartial).
Time }
Time {
Time iFrame.
Time done.
Time }
Time iApply (bupd_iter_mono with "[Hinv] H").
Time iIntros "(Hw&HE&Hstate)".
Time iSpecialize ("Hinv" with "Hstate").
Time (iMod ("Hinv" with "[$Hw $HE]") as "(?&?&$)"; auto).
Time }
Time (iApply (bupd_iter_mono with "[] H\207\131halt"); iIntros "H\207\131halt").
Time clear Hpartial Hrec.
Time
iAssert (Nat.iter (S k0) (\206\187 P, |==> \226\150\183 P)%I (|==> \226\151\135 \207\134inv \207\131crash))%I with
 "[H\207\131halt]" as "Hinv'".
Time {
Time (unshelve (iApply recv_idemp_adequacy_inv; eauto); eauto).
Time }
Time (iApply (bupd_iter_mono with "[] Hinv'"); iIntros ">>Hinv'").
Time iSpecialize ("Hwp_rec" $! Hinv \207\131crash \207\131rec_err Hcrash with "Hinv'").
Time (iMod "Hwp_rec" as ( stateI'' ) "[H\207\131 [H _]]"; eauto).
Time iExists stateI''.
Time (iIntros "{$H\207\131} !> "; auto).
Time Qed.
Time
Theorem wp_recovery_adequacy {T} {R} OpT \206\163 \206\155 `{invPreG \206\163} 
  s (e : proc OpT T) (rec : proc OpT R) \207\1311 \207\134 (\207\134rec : State \206\155 \226\134\146 Prop) 
  k :
  s = NotStuck
  \226\134\146 wp_recovery s e rec \207\1311 (fun v \207\131 => \226\140\156\207\134 v \207\131\226\140\157)%I (fun \207\131 => \226\140\156\207\134rec \207\131\226\140\157)%I k
    \226\134\146 recv_adequate s e rec \207\1311 \207\134 \207\134rec.
Time Proof.
Time (intros ? Hwp).
Time subst.
Time (unshelve (eapply @recv_adequacy_int_to_ext); eauto).
Time (iApply wp_recovery_adequacy_internal; eauto).
Time iApply Hwp.
Time Qed.
Time
Fixpoint wp_proc_seq {T R} OpT \206\163 (\206\155 : Layer OpT) `{invPreG \206\163} 
s (es : proc_seq OpT T) (rec : proc OpT R) \207\1311 \207\134 {struct es} : 
iProp \206\163 :=
  match es with
  | Proc_Seq_Nil v => (\207\134 v \207\1311)%I
  | @Proc_Seq_Bind _ _ T0 e es' =>
      wp_recovery (\206\155:=\206\155) s e rec \207\1311
        (\206\187 v \207\1312,
           \226\136\128 \207\1312' (Hfinish : \206\155.(finish_step) (snd \207\1312) (Val \207\1312' tt)),
             wp_proc_seq \206\155 s (es' (Normal (existT T0 v))) rec (1, \207\1312') \207\134)%I
        (\206\187 \207\1312,
           wp_proc_seq \206\155 s (es' (Recovered (existT _ tt))) rec (1, snd \207\1312) \207\134)
        O
  end.
Time
Lemma recv_idemp_mono {R} {OpT} \206\163 \206\155 `{invPreG \206\163} s 
  (rec : proc OpT R) \207\134inv \207\134rec \207\134rec' :
  \226\150\161 (\226\136\128 \207\131, \207\134rec \207\131 -\226\136\151 \207\134rec' \207\131)
  -\226\136\151 recv_idemp (\206\155:=\206\155) s rec \207\134inv \207\134rec -\226\136\151 recv_idemp s rec \207\134inv \207\134rec'.
Time Proof.
Time iIntros "#Hwand #Hrec !>".
Time iIntros.
Time
(unshelve iMod ("Hrec" $! _ _ _ _ with "[$]") as ( stateI ) "(H&Hwp&?)";
  eauto).
Time iModIntro.
Time iExists stateI.
Time iFrame.
Time iApply (wp_wand with "Hwp").
Time iIntros ( ? ) "Himpl".
Time iIntros.
Time iMod ("Himpl" with "[$]").
Time (iApply "Hwand"; eauto).
Time Qed.
Time
Lemma wp_recovery_mono {T} {R} {OpT} \206\163 \206\155 `{invPreG \206\163} 
  s (e : proc OpT T) (rec : proc OpT R) \207\1311 \207\134 \207\134' \207\134rec 
  \207\134rec' k :
  (\226\136\128 v \207\131, \207\134 v \207\131 -\226\136\151 \207\134' v \207\131)
  -\226\136\151 \226\150\161 (\226\136\128 \207\131, \207\134rec \207\131 -\226\136\151 \207\134rec' \207\131)
     -\226\136\151 wp_recovery (\206\155:=\206\155) s e rec \207\1311 \207\134 \207\134rec k
        -\226\136\151 wp_recovery s e rec \207\1311 \207\134' \207\134rec' k.
Time Proof.
Time iIntros "Hwand1 Hwand2 Hrec".
Time rewrite /wp_recovery.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply
 (bupd_iter_mono with "[Hwand1 Hwand2]") ; last  iApply "Hrec").
Time iIntros "Hrec".
Time iDestruct "Hrec" as ( \207\134inv ) "Hrec".
Time iExists \207\134inv.
Time iIntros ( ? ).
Time iMod ("Hrec" $! _) as ( ? ) "(?&Hwp&Hinv&Hrec)".
Time iModIntro.
Time iExists _.
Time iFrame.
Time iSplitL "Hwp Hwand1".
Time *
Time iApply (wp_wand with "Hwp").
Time iIntros ( ? ) "Himpl".
Time iIntros.
Time iMod ("Himpl" with "[$]").
Time (iApply "Hwand1"; eauto).
Time *
Time by iApply (recv_idemp_mono with "Hwand2 Hrec").
Time Qed.
Time
Lemma wp_proc_seq_mono {T} {R} {OpT} \206\163 \206\155 `{invPreG \206\163} 
  s (es : proc_seq OpT T) (rec : proc OpT R) \207\1311 \207\134 
  \207\134' :
  \226\150\161 (\226\136\128 v \207\131, \207\134 v \207\131 -\226\136\151 \207\134' v \207\131)
  -\226\136\151 wp_proc_seq (\206\155:=\206\155) s es rec \207\1311 \207\134 -\226\136\151 wp_proc_seq s es rec \207\1311 \207\134'.
Time Proof.
Time revert \207\1311.
Time (<ssreflect_plugin::ssrtclintros@0> induction es as [| ? ? es IH] =>\207\1311).
Time -
Time rewrite //=.
Time iIntros "H".
Time iApply "H".
Time -
Time iIntros "#H".
Time (iApply wp_recovery_mono; rewrite -/wp_proc_seq).
Time *
Time iIntros ( ? ? ) "H2".
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> iApply IH ; first  by eauto).
Time iApply "H2".
Time eauto.
Time *
Time iAlways.
Time iIntros.
Time rewrite -/wp_proc_seq.
Time (iApply IH; eauto).
Time Qed.
Time
Lemma wp_proc_seq_ind {T0} {T} {R} OpT \206\163 (\206\155 : Layer OpT) 
  `{invPreG \206\163} (p : proc OpT T0) (rx : ExecOutcome \226\134\146 proc_seq OpT T)
  (rec : proc OpT R) \207\1311 \207\1311' \207\134 k res :
  exec_or_rexec \206\155 p (rec_singleton rec) \207\1311 (Val \207\1311' res)
  \226\134\146 Nat.iter k (\206\187 P, |==> \226\150\183 P)%I
      (wp_proc_seq NotStuck (Proc_Seq_Bind p rx) rec \207\1311 \207\134)
    \226\134\146 \226\136\131 n,
        Nat.iter n (\206\187 P, |==> \226\150\183 P)%I
          (wp_proc_seq NotStuck (rx res) rec \207\1311' \207\134).
Time Proof.
Time (intros Hhd Hwp).
Time (destruct Hhd as [Hnorm| Hrecv]).
Time **
Time (destruct Hnorm as (v, (x, (Hexec, Hfinish)))).
Time (destruct Hfinish as ([], ((?, ?), (Hfinish, Hpure)))).
Time (destruct Hfinish as ([], ((?, ?), (Hput, Hfin)))).
Time (destruct x).
Time (inversion Hput; subst).
Time (inversion H0).
Time subst.
Time (inversion Hfin; subst).
Time (inversion Hpure; subst).
Time rewrite exec_equiv_exec_n in  {} Hexec *.
Time (intros (n', Hexec)).
Time exists (S k + S (S n'))%nat.
Time iPoseProof Hwp as "Hwp".
Time
(iPoseProof (wp_recovery_adequacy_internal with "Hwp") as "(Hnorm&_)"; eauto).
Time
unshelve
 (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  iApply
   "Hnorm"; eauto).
Time iIntros "Hrec".
Time iDestruct "Hrec" as ( v' Hp ) "Hrec".
Time subst.
Time rewrite -/wp_proc_seq.
Time (iApply "Hrec"; eauto).
Time **
Time (destruct Hrecv as ([], (x, (Hrexec, Hfinish)))).
Time (destruct Hfinish as ([], ((?, ?), (Hfinish, Hpure)))).
Time (destruct x).
Time (inversion Hfinish; subst).
Time (inversion H0).
Time subst.
Time (inversion Hpure; subst).
Time (rewrite rexec_equiv_rexec_n'_val in  {} Hrexec *; swap 1 3).
Time {
Time (eapply recv_adequacy_int_non_stuck; eauto).
Time iPoseProof Hwp as "Hwp".
Time (iApply (@wp_recovery_adequacy_internal with "Hwp"); eauto).
Time }
Time {
Time (eapply lifted_crash_non_err).
Time }
Time (intros (n', Hrexec)).
Time exists (S k + (5 + n'))%nat.
Time iPoseProof Hwp as "Hwp".
Time
(iPoseProof (wp_recovery_adequacy_internal with "Hwp") as "(_&Hrecv)"; eauto).
Time
unshelve
 (<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  iApply
   "Hrecv"; eauto).
Time iIntros "Hrec".
Time eauto.
Time Qed.
Time
Theorem wp_proc_seq_adequacy {T} {R} OpT \206\163 (\206\155 : Layer OpT) 
  `{invPreG \206\163} s (es : proc_seq OpT T) (rec : proc OpT R) 
  \207\1311 \207\134 k :
  Nat.iter k (\206\187 P, |==> \226\150\183 P)%I (wp_proc_seq s es rec \207\1311 (\206\187 v \207\1312, \226\140\156\207\134 v \207\1312\226\140\157%I))
  \226\134\146 s = NotStuck \226\134\146 proc_seq_adequate (\206\155:=\206\155) s es rec \207\1311 \207\134.
Time Proof.
Time (intros Hwp ->).
Time split.
Time -
Time revert k \207\1311 Hwp.
Time (<ssreflect_plugin::ssrtclintros@0> induction es =>k \207\1311 Hwp \207\1312 res).
Time *
Time (inversion 1; subst).
Time (eapply (soundness (M:=iResUR \206\163) _ k)).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_laterN_mono ; first  by
 reflexivity).
Time iApply Hwp.
Time *
Time (destruct 1 as (res0, (\207\1311', (Hhd, Hrest)))).
Time (edestruct @wp_proc_seq_ind; eauto).
Time -
Time revert k \207\1311 Hwp.
Time
(<ssreflect_plugin::ssrtclintros@0> induction es as [| ? ? ? IH] =>k \207\1311 Hwp
 \207\1312).
Time *
Time (inversion 1; subst).
Time *
Time (destruct 1 as [[Hnorm| Hrec]| Htl]).
Time **
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct Hnorm as [Hnorm| (?, (?, (?, Hfalse)))] ; last  first).
Time {
Time (apply bind_pure_no_err, lifted_finish_non_err in Hfalse; eauto).
Time }
Time (eapply exec_err_rexec_err in Hnorm).
Time (eapply recv_adequate_not_stuck; eauto).
Time
(<ssreflect_plugin::ssrtclseq@0>
 eapply wp_recovery_adequacy with (\207\1340 := fun _ _ => True)
  (\207\134rec := fun _ => True) ; first  done).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  iApply Hwp).
Time rewrite /wp_proc_seq -/wp_proc_seq.
Time iIntros "Hwp".
Time (iApply (wp_recovery_mono with "[] [] Hwp"); eauto).
Time **
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct Hrec as [Hrec| (?, ((?, ?), (?, Hfalse)))] ; last  first).
Time {
Time (apply bind_pure_no_err in Hfalse; eauto).
Time (inversion Hfalse).
Time }
Time (eapply recv_adequate_not_stuck; eauto).
Time
(<ssreflect_plugin::ssrtclseq@0>
 eapply wp_recovery_adequacy with (\207\1340 := fun _ _ => True)
  (\207\134rec := fun _ => True) ; first  done).
Time
(<ssreflect_plugin::ssrtclseq@0> iApply bupd_iter_mono ; last  iApply Hwp).
Time rewrite /wp_proc_seq -/wp_proc_seq.
Time iIntros "Hwp".
Time (iApply (wp_recovery_mono with "[] [] Hwp"); eauto).
Time **
Time (destruct Htl as (?, (?, (Hhd, ?)))).
Time (edestruct @wp_proc_seq_ind; eauto).
Time (eapply IH; eauto).
Time Qed.
