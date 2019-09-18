Time From iris.algebra Require Import auth gmap list.
Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct.
Time Require Export CSL.Refinement.
Time
Require Import AtomicPairAPI AtomicPair.ImplShadow ExMach.WeakestPre
  ExMach.RefinementAdequacy.
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
Time Require Import AtomicPair.Helpers.
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
Time Qed.
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
Time #[global]Opaque someone_writing.
Time
Definition FlagInv (\206\147 : ghost_names) flag :=
  (named "Hflag_auth" (own (\206\179flag \206\147) (\226\151\143 Excl' flag))
   \226\136\151 named "Hcommit" (log_commit d\226\134\166 fst flag))%I.
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
Time
Definition CommitOff (pcurr psrc : nat * nat) : iProp \206\163 := \226\140\156pcurr = psrc\226\140\157%I.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&#Hsource_inv&Hinv) H\206\166".
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
Time iDestruct "Hinv" as ( \206\179lock ) "(#Hlockinv&#Hinv)".
Time Definition CrashInner \206\147 := (CommitInner True \206\147 \226\136\151 CrashStarter \206\147)%I.
Time Definition CrashInv \206\147 := (source_ctx \226\136\151 inv liN (CommitInner True \206\147))%I.
Time
Lemma someone_writing_weaken P Q p je :
  (P -\226\136\151 Q) -\226\136\151 someone_writing P p je -\226\136\151 someone_writing Q p je.
Time Proof.
Time rewrite ?someone_writing_unfold.
Time iIntros "HPQ".
Time iIntros "H".
Time (wp_lock "(Hlocked&HEL)").
Time iDestruct "H" as ( K ? ) "(HP&?&?)".
Time iExists _ , _.
Time iFrame.
Time by iApply "HPQ".
Time Qed.
Time
iDestruct "HEL" as ( ptr_val pcurr pother )
 "(Hptr_ghost&Hpair1_ghost&Hpair2_ghost&Hother1_ghost&Hother2_ghost)".
Time #[global]
Instance CommitInner'_timeless  P \206\147 flag plog pcurr 
 psrc: (Timeless P \226\134\146 Timeless (CommitInner' P \206\147 flag plog pcurr psrc)).
Time Proof.
Time (intros).
Time (destruct flag as (c, ?)).
Time (destruct c; apply _).
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_einner "H").
Time Qed.
Time wp_step.
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
Time (simpl).
Time iFrame.
Time iModIntro.
Time wp_bind.
Time iInv "Hinv" as "H".
Time (destruct_einner "H").
Time iDestruct "Hcase" as "(Ho1&Ho2&Hfst&Hsnd)".
Time wp_step.
Time (iModIntro; iExists _ , _; iFrame).
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
Time (rewrite ?read_of_swap ?write_of_swap; iFrame).
Time by iApply "H\206\166"; iFrame.
Time Qed.
Time iModIntro.
Time (wp_unlock "[-H\206\166 Hreg Hj]"; iFrame).
Time
Lemma read_main_fst (m : iProp \206\163) {H' : Timeless m} 
  \206\147 pcurr i :
  {{{ inv liN (CommitInner m \206\147) \226\136\151 named i (lease main_fst pcurr) }}} 
  read_disk main_fst {{{ RET pcurr; named i (lease main_fst pcurr)}}}.
Time Proof.
Time (iIntros ( \206\166 ) "(Hinv&Hlog) H\206\166"; iAssignNames).
Time (log_step "Hinv").
Time {
Time iExists _ , (_, _) , (_, _).
Time iFrame.
Time (rewrite ?read_of_swap ?write_of_swap; iFrame).
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
