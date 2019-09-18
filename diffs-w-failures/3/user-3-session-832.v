Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time
From Armada.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap.
Time From Armada.Goose.Examples Require Import MailServer.
Time From Armada.Goose.Proof Require Import Interp.
Time Require Import Goose.Proof.Interp.
Time From Armada Require AtomicPair.Helpers.
Time From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Armada.Goose Require Import Machine.
Time From Armada.Goose Require Import GoZeroValues.
Time Unset Implicit Arguments.
Time
Inductive ghost_init_status {gm : GoModel} {gmwf : GoModelWf gm} :=
  | Uninit : _
  | Started_Init :
      forall (j : nat) {T2} K `{LanguageCtx _ unit T2 Mail.l K}, _
  | Finished_Init : _.
Time
Lemma map_Permutation (A B : Type) (f : A \226\134\146 B) (al : list A) 
  (bl : list B) :
  Permutation.Permutation (map f al) bl
  \226\134\146 \226\136\131 al', Permutation.Permutation al al' \226\136\167 map f al' = bl.
Time Proof.
Time (intros Hperm).
Time (remember (map f al) as bl0 eqn:Heq ).
Time revert Heq.
Time revert al.
Time (<ssreflect_plugin::ssrtclintros@0> induction Hperm =>al Heq).
Time -
Time (destruct al).
Time exists [].
Time eauto.
Time (inversion Heq).
Time -
Time (destruct al as [| a al]; inversion Heq; subst).
Time (simpl in Heq).
Time (edestruct (IHHperm) as (al', (?, ?)); eauto).
Time subst.
Time exists (a :: al').
Time (split; eauto).
Time -
Time (destruct al as [| a [| b al]]; try inversion Heq; subst).
Time (exists (b :: a :: al); split; eauto).
Time econstructor.
Time -
Time (edestruct (IHHperm1) as (al1, (?, ?)); eauto).
Time (edestruct (IHHperm2) as (al2, (?, ?)); eauto).
Time (exists al2; split; eauto).
Time (etransitivity; try eassumption; eauto).
Time Qed.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep.
Time Set Default Goal Selector "!".
Time Notation contents := (gmap string (Datatypes.list byte)).
Time
Canonical Structure contentsC {m : GoModel} {wf : GoModelWf m} :=
  leibnizC contents.
Time
Canonical Structure contentsF {m : GoModel} {wf : GoModelWf m} :=
  discreteC contents.
Time
Canonical Structure ghost_init_statusC {m : GoModel} 
  {wf : GoModelWf m} := leibnizC ghost_init_status.
Time
Canonical Structure ghost_init_statusF {m : GoModel} 
  {wf : GoModelWf m} := discreteC ghost_init_status.
Time
Definition UserDir {model : GoModel} (user : uint64) :=
  ("user" ++ uint64_to_string user)%string.
Time Set Default Proof Using "Type".
Time Section refinement_triples.
Time Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Time Context {hGcontents : ghost_mapG contentsC \206\163}.
Time Context {hGinit : ghost_mapG ghost_init_statusC \206\163}.
Time Context {hGTmp : gen_heapG string Filesys.FS.Inode \206\163}.
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time Import Mail.
Time
Definition InboxLockInv (\206\179 : gname) (n : nat) :=
  (\226\136\131 S1 S2,
     ghost_mapsto_auth \206\179 (A:=discreteC contents) S1
     \226\136\151 ghost_mapsto (A:=discreteC contents) \206\179 O S2)%I.
Time
Definition MailboxStatusInterp (uid : uint64) (lk : LockRef) 
  (\206\179 : gname) (ls : MailboxStatus) (msgs : contents) 
  (open : bool) :=
  (if open
   then match ls with
        | MUnlocked =>
            UserDir uid \226\134\166 Unlocked
            \226\136\168 UserDir uid \226\134\166{ - 1} ReadLocked 0 \226\136\151 InboxLockInv \206\179 O
        | MPickingUp =>
            wlocked lk
            \226\136\151 (\226\136\131 S : contents,
                 ghost_mapsto_auth \206\179 (A:=contentsC) S \226\136\151 \226\140\156S \226\138\134 msgs\226\140\157)
        | MLocked => wlocked lk \226\136\151 InboxLockInv \206\179 O \226\136\151 UserDir uid \226\134\166 Unlocked
        end else \226\140\156ls = ls\226\140\157 \226\136\151 UserDir uid \226\134\166 Unlocked)%I.
Time Definition boxN : namespace := nroot.@"inbox_lock".
Time
Definition InboxInv (uid : uint64) (lk : LockRef) 
  (\206\179 : gname) (ls : MailboxStatus)
  (msgs : gmap.gmap string (Datatypes.list byte)) 
  (open : bool) :=
  ((if open then is_lock boxN lk (InboxLockInv \206\179) True else True)
   \226\136\151 MailboxStatusInterp uid lk \206\179 ls msgs open
     \226\136\151 UserDir uid \226\134\166 dom (gset string) msgs
       \226\136\151 ([\226\136\151 map] mid\226\134\166msgData \226\136\136 msgs, \226\136\131 inode (n : nat),
                                        path.mk (UserDir uid) mid \226\134\166 inode
                                        \226\136\151 inode \226\134\166{ n} msgData))%I.
Time
Definition InboxInv_weak (uid : uint64) (lk : LockRef) 
  (\206\179 : gname) (ls : MailboxStatus)
  (msgs : gmap.gmap string (Datatypes.list byte)) 
  (open : bool) :=
  (MailboxStatusInterp uid lk \206\179 ls msgs open
   \226\136\151 UserDir uid \226\134\166 dom (gset string) msgs
     \226\136\151 ([\226\136\151 map] mid\226\134\166msgData \226\136\136 msgs, \226\136\131 inode (n : nat),
                                      path.mk (UserDir uid) mid \226\134\166 inode
                                      \226\136\151 inode \226\134\166{ n} msgData))%I.
Time #[global]
Instance InboxInv_timeless  uid lk \206\179 ls msgs open':
 (Timeless (InboxInv_weak uid lk \206\179 ls msgs open')).
Time Proof.
Time rewrite /InboxInv_weak.
Time (destruct ls, open'; apply _).
Time Qed.
Time
Definition GlobalInv ls (open : bool) : iProp \206\163 :=
  (if open
   then \226\136\131 (lsptr : slice.t LockRef) (q : nat),
          global \226\134\166{ q} Some lsptr \226\136\151 lsptr \226\134\166{ q} (ls, ls) else 
   global \226\134\166 None)%I.
Time
Lemma GlobalInv_split ls :
  GlobalInv ls true
  \226\138\162 GlobalInv ls true
    \226\136\151 (\226\136\131 lsptr, global \226\134\166{ - 1} Some lsptr \226\136\151 lsptr \226\134\166{ - 1} (ls, ls)).
Time Proof.
Time iIntros "HG".
Time iDestruct "HG" as ( lsptr q ) "(HP1&HP2)".
Time iDestruct "HP2" as ( Heq ? ) "HP2".
Time rewrite //= @read_split /ptr_mapsto Count_Typed_Heap.read_split_join.
Time iDestruct "HP1" as "(HP1&HR1)".
Time iDestruct "HP2" as "(HP2&HR2)".
Time iSplitL "HP1 HP2".
Time {
Time iExists lsptr , (S q).
Time iFrame.
Time by iFrame.
Time }
Time iExists _.
Time iFrame.
Time by iFrame.
Time Qed.
Time
Definition MsgInv (\206\147 : gmap uint64 gname) ls uid lm 
  (open : bool) : iProp \206\163 :=
  (\226\136\131 lk \206\179,
     \226\140\156\206\147 !! uid = Some \206\179\226\140\157
     \226\136\151 \226\140\156if open then List.nth_error ls uid = Some lk else True\226\140\157
       \226\136\151 InboxInv uid lk \206\179 (fst lm) (snd lm) open)%I.
Time
Definition MsgInv_weak (\206\147 : gmap uint64 gname) uid 
  lm (open : bool) : iProp \206\163 :=
  (\226\136\131 lk \206\179,
     \226\140\156\206\147 !! uid = Some \206\179\226\140\157 \226\136\151 InboxInv_weak uid lk \206\179 (fst lm) (snd lm) open)%I.
Time #[global]
Instance MsgInv_weak_timeless  \206\147 uid x open:
 (Timeless (MsgInv_weak \206\147 uid x open)).
Time Proof.
Time rewrite /MsgInv_weak.
Time (apply _).
Time Qed.
Time
Definition userRange_ok (s : gset uint64) :=
  forall uid : uint64, (uid < 100 -> uid \226\136\136 s) /\ (uid >= 100 -> \194\172 uid \226\136\136 s).
Time
Definition RootDirInv (\207\131 : Mail.State) : iProp \206\163 :=
  (rootdir
   \226\134\166{ - 1} (set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
   \226\136\151 \226\140\156userRange_ok (dom (gset uint64) \207\131.(messages))\226\140\157)%I.
Time
Lemma RootDirInv_range_ok \207\131 :
  RootDirInv \207\131 -\226\136\151 \226\140\156userRange_ok (dom (gset _) \207\131.(messages))\226\140\157.
Time Proof.
Time by iIntros "(?&$)".
Time Qed.
Time Lemma userRange_ok_eq s s' : userRange_ok s \226\134\146 userRange_ok s' \226\134\146 s = s'.
