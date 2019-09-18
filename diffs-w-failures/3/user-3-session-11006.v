Time From iris.algebra Require Import auth gmap list.
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
Time Definition CrashInner \206\147 := (CommitInner True \206\147 \226\136\151 CrashStarter \206\147)%I.
Time Definition CrashInv \206\147 := (source_ctx \226\136\151 inv liN (CommitInner True \206\147))%I.
Time
Lemma someone_writing_weaken P Q p je :
  (P -\226\136\151 Q) -\226\136\151 someone_writing P p je -\226\136\151 someone_writing Q p je.
Time Proof.
Time rewrite ?someone_writing_unfold.
Time iIntros "HPQ".
Time iIntros "H".
Time iDestruct "H" as ( K ? ) "(HP&?&?)".
Time iExists _ , _.
Time iFrame.
Time by iApply "HPQ".
Time Qed.
Time #[global]
Instance CommitInner'_timeless  P \206\147 flag plog pcurr 
 psrc: (Timeless P \226\134\146 Timeless (CommitInner' P \206\147 flag plog pcurr psrc)).
Time Proof.
Time (intros).
Time (destruct flag as (c, ?)).
Time (destruct c; apply _).
Time Qed.
Time #[global]
Instance CommitInner_timeless  P \206\147: (Timeless P \226\134\146 Timeless (CommitInner P \206\147)).
Time Proof.
Time (intros).
Time (apply _).
Time Qed.
Time #[global]
Instance sep_into_sep_single_named  {PROP : bi} (i : string) 
 (P : PROP): (IntoSepEnv (named i P) [(LNamed i, P)]).
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iFrame.
Time eauto.
Time Qed.
Time #[global]
Instance sep_into_sep_cons  {PROP : bi} (i : string) 
 (P Q : PROP) Ps:
 (IntoSepEnv Q Ps \226\134\146 IntoSepEnv (named i P \226\136\151 Q) ((LNamed i, P) :: Ps)) |10.
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iIntros ( ? ) "(?&?)".
Time iFrame.
Time by iApply H1.
Time Qed.
Time #[global]
Instance sep_into_sep_anon_cons  {PROP : bi} (P Q : PROP) 
 Ps: (IntoSepEnv Q Ps \226\134\146 IntoSepEnv (P \226\136\151 Q) ((LAnon, P) :: Ps)) |50.
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iIntros ( ? ) "(?&?)".
Time iFrame.
Time by iApply H1.
Time Qed.
Time #[global]
Instance sep_into_sep_single_anon  {PROP : bi} (P : PROP):
 (IntoSepEnv P [(LAnon, P)]) |100.
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iFrame.
Time eauto.
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
Time Proof.
Time iIntros ( \206\166 ).
Time (iIntros "(Hinv&Hlog&Hflag) H\206\166"; iAssignNames).
Time (log_step "Hinv").
Time by iApply "H\206\166"; iFrame.
Time Qed.
Time
Lemma write_log_snd (m : iProp \206\163) {H' : Timeless m} 
  \206\147 flagsnd (plog2 : nat) x j i :
  {{{ inv liN (CommitInner m \206\147)
      \226\136\151 named i (lease log_snd plog2)
        \226\136\151 named j (own \206\147.(\206\179flag) (\226\151\175 Excl' (0, flagsnd))) }}} 
  write_disk log_snd x {{{ RET tt; named i (lease log_snd x)
                                   \226\136\151 named j
                                       (own \206\147.(\206\179flag) (\226\151\175 Excl' (0, flagsnd)))}}}.
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog&Hflag) H\206\166"; iAssignNames).
Time (log_step "Hinv").
Time by iApply "H\206\166"; iFrame.
Time Qed.
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
Time by iApply "H\206\166"; iFrame.
Time Qed.
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
Time (iIntros ( \206\166 ) "(Hinv&Hlog&Hflag) H\206\166"; iAssignNames).
Time (log_step "Hinv").
Time by iApply "H\206\166"; iFrame.
Time Qed.
Time
Lemma read_main_fst (m : iProp \206\163) {H' : Timeless m} 
  \206\147 pcurr i :
  {{{ inv liN (CommitInner m \206\147) \226\136\151 named i (lease main_fst pcurr) }}} 
  read_disk main_fst {{{ RET pcurr; named i (lease main_fst pcurr)}}}.
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog) H\206\166"; iAssignNames).
Time (log_step "Hinv").
Time by iApply "H\206\166"; iFrame.
Time Qed.
Time
Lemma read_main_snd (m : iProp \206\163) {H' : Timeless m} 
  \206\147 pcurr i :
  {{{ inv liN (CommitInner m \206\147) \226\136\151 named i (lease main_snd pcurr) }}} 
  read_disk main_snd {{{ RET pcurr; named i (lease main_snd pcurr)}}}.
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog) H\206\166"; iAssignNames).
Time (log_step "Hinv").
Time by iApply "H\206\166"; iFrame.
Time Qed.
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
Time
(destruct_commit_inner "H"; iLDestruct "Hlog_inv"; iLDestruct "Hcommit_inv").
Time (repeat unify_ghost).
Time (destruct p; simpl).
Time (repeat unify_lease).
Time
iMod
 (ghost_var_update (\206\179flag \206\147)
    (1,
    (j, existT _ (K (Call (AtomicPair.Write _))))
      : prodO natO (procTC AtomicPair.Op)) with "Hflag_auth [$]") as
 "(Hflag_auth&Hflag_ghost)".
Time wp_step.
Time recommit.
Time iModIntro.
Time iNamed iFrame.
Time iFrame.
Time iSplitL "Hm Hj".
Time {
Time iNext.
Time iIntros.
Time (simpl).
Time rewrite /CommitOn.
Time rewrite someone_writing_unfold.
Time iExists K , _.
Time iFrame.
Time (simpl).
Time (destruct_pairs; auto).
Time }
Time iApply "H\206\166".
Time iFrame.
Time Qed.
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
Time (destruct p as (p1, p2)).
Time (repeat unify_ghost).
Time destruct_pairs.
Time (repeat unify_lease).
Time (simpl).
Time rewrite /CommitOn.
Time rewrite someone_writing_unfold.
Time iDestruct "Hsomewriter" as ( ? K' ) "(Hreg&%&Hj)".
Time (simpl).
Time wp_step.
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
iMod (ghost_var_update (\206\179src \206\147) (p1, p2) with "Hsrc_auth Hsrc_ghost") as
 "(Hsrc_auth&Hsrc_ghost)".
Time
iMod
 (ghost_var_update (\206\179flag \206\147) (0, (0, existT _ (Ret tt) : procTC _))
 with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
Time iModIntro.
Time handle_pairs recommit; iNamed iFrame.
Time iNamed iFrame.
Time iSplitL "".
Time {
Time iNext.
Time rewrite /CommitOff.
Time auto.
Time }
Time iApply "H\206\166".
Time iFrame.
Time Qed.
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
Time Proof.
Time
(iIntros ( \206\166 )
  "(Hsource_inv&Hinv&Hflag&Hcommit_flag&Hmain1&Hmain2&Hlog1&Hlog2&Hsrc_ghost) H\206\166";
  iAssignNames).
Time iInv "Hinv" as "H".
Time
(destruct_commit_inner "H"; iLDestruct "Hmain_inv"; iLDestruct "Hcommit_inv";
  iLDestruct "Hlog_inv"; iLDestruct "Hsrc_inv").
Time (destruct p as (p1, p2)).
Time (simpl).
Time destruct_pairs.
Time (repeat unify_ghost).
Time (repeat unify_lease).
Time (simpl).
Time rewrite /CommitOn.
Time rewrite someone_writing_unfold.
Time iDestruct "Hsomewriter" as ( ? K' ) "(Hreg&%&Hj)".
Time (simpl).
Time wp_step.
Time (destruct thd).
Time (simpl).
Time (inversion H4).
Time rewrite H6.
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
iMod (ghost_var_update (\206\179src \206\147) (p1, p2) with "Hsrc_auth Hsrc_ghost") as
 "(Hsrc_auth&Hsrc_ghost)".
Time
iMod
 (ghost_var_update (\206\179flag \206\147) (0, (0, existT _ (Ret tt) : procTC _))
 with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
Time iModIntro.
Time handle_pairs recommit; iNamed iFrame.
Time (eexists; shelve).
Time rewrite /CommitInner'.
Time iNamed iFrame.
Time iNamed iFrame.
Time iSplitL "".
Time {
Time iNext.
Time rewrite /CommitOff.
Time auto.
Time }
Time iApply "H\206\166".
Time iFrame.
Time Qed.
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
Time
iNamed iApply (set_commit Registered _ _ p with "[$]"); iIntros "!>"; iLIntro.
Time (wp_lock "(Hlocked'&HML)").
Time iDestruct "HML" as ( pmain ) "(Hmain_lease1&Hmain_lease2&Hsrc_ghost)".
Time (repeat wp_step).
Time
iNamed
 iApply (unset_commit Registered _ _ p with "[$]"); iIntros "!>"; iLIntro.
Time (wp_unlock "[Hlog_l1 Hlog_l2 Hcommit_lease Hflag_ghost]").
Time {
Time (iExists _; iFrame).
Time }
Time (wp_unlock "[Hmain_lease1 Hmain_lease2 Hsrc_ghost]").
Time {
Time (iExists _; iFrame).
Time }
Time iApply "H\206\166".
Time iFrame.
Time Qed.
Time
Lemma read_refinement {T} j K
  `{LanguageCtx AtomicPair.Op (nat * nat) T AtomicPair.l K} :
  {{{ j \226\164\135 K (Call AtomicPair.Read) \226\136\151 Registered \226\136\151 ExecInv }}} read {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 ) "(#Hsource_inv&#Hmain_lock&Hlog_lock&#Hinv)".
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
Time {
Time rewrite /size.
Time lia.
Time }
Time iDestruct "H" as "(H&_)".
Time (repeat iDestruct "H" as "((?&?)&H)").
Time iFrame.
Time Qed.
Time End refinement_triples.
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
Time Module lRO: exmach_refinement_obligations lRT.
Time Module eRD:=  lRD.
Time Import lRT lRD.
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
Time (red).
Time (intros).
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&?)".
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
Time (destruct flag as (flag, thd)).
Time (simpl).
Time (destruct flag).
Time *
Time recommit.
Time iNamed iFrame.
Time iFrame.
Time iModIntro.
Time wp_ret.
Time iInv "Hinv" as "H" "_".
Time (destruct_commit_inner "H").
Time (iLDestruct "Hsrc_inv").
Time (iLDestruct "Hcommit_inv").
Time (iLDestruct "Hmain_inv").
Time (iLDestruct "Hlog_inv").
Time (simpl).
Time (repeat unify_ghost).
Time (do 5 unify_lease).
Time (simpl).
Time rewrite /CommitOff.
Time (iDestruct "Hsomewriter" as % Hpeq; subst).
Time iApply fupd_mask_weaken.
Time {
Time solve_ndisj.
Time }
Time iExists psrc , psrc.
Time iFrame "Hsrc".
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by
 iPureIntro; econstructor).
Time iClear "Hctx Hinv".
Time iIntros ( ? ? ? ) "(#Hctx&Hsrc)".
Time
iMod
 (@ghost_var_update _ _ _ (\206\179flag \206\147) (0, (0, existT _ (Ret tt) : procTC _))
 with "Hflag_auth Hflag_ghost") as "(Hflag_auth&Hflag_ghost)".
Time iClear "Hmain1 Hmain2 Hlog1 Hlog2 Hcommit_lease".
Time iMod (disk_next with "Hmain_fst") as "(Hmain_fst&Hmain1)".
Time iMod (disk_next with "Hmain_snd") as "(Hmain_snd&Hmain2)".
Time iMod (disk_next with "Hlog_fst") as "(Hlog_fst&Hlog1)".
Time iMod (disk_next with "Hlog_snd") as "(Hlog_snd&Hlog2)".
Time iMod (disk_next with "Hcommit") as "(Hcommit&Hcommit_lease)".
Time iModIntro.
Time iExists \206\147 , 0 , 0.
Time iFrame.
Time iSplitL "Hmain1 Hmain2 Hsrc_ghost".
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
Time *
Time (destruct plog as (plog1, plog2)).
Time recommit.
Time iNamed iFrame.
Time iFrame.
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
