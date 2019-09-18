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
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>Hok1 Hok2).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>i).
Time clear - Hok1 Hok2.
Time (destruct (Hok1 i) as (Hlt1, Hge1)).
Time (destruct (Hok2 i) as (Hlt2, Hge2)).
Time (destruct (lt_dec i 100) as [Hlt| Hnlt]).
Time -
Time intuition.
Time -
Time (assert (i >= 100) by lia).
Time intuition.
Time Qed.
Time
Definition InitInv (\206\147 : gmap uint64 gname) \206\179 \207\131 :=
  (\226\136\131 v : ghost_init_status,
     ghost_mapsto_auth \206\179 v
     \226\136\151 match v with
       | Uninit =>
           ghost_mapsto \206\179 O v
           \226\136\151 \226\140\156\207\131.(open) = false\226\140\157
             \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), \226\136\131 \206\179uid,
                                                 \226\140\156
                                                 \206\147 !! uid = Some \206\179uid\226\140\157
                                                 \226\136\151 
                                                 InboxLockInv \206\179uid O)
       | Started_Init j K => j \226\164\135 K (Call Open) \226\136\151 \226\140\156\207\131.(open) = false\226\140\157
       | Finished_Init => \226\140\156\207\131.(open) = true\226\140\157
       end)%I.
Time
Definition MsgsInv (\206\147 : gmap uint64 gname) (\206\179 : gname) 
  (\207\131 : Mail.State) : iProp \206\163 :=
  (\226\136\131 ls,
     GlobalInv ls \207\131.(open)
     \226\136\151 RootDirInv \207\131
       \226\136\151 InitInv \206\147 \206\179 \207\131
         \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm \207\131.(open)))%I.
Time
Lemma MsgInv_pers_split \206\147 ls uid lm :
  MsgInv \206\147 ls uid lm true
  -\226\136\151 \226\136\131 lk \206\179,
       \226\140\156\206\147 !! uid = Some \206\179\226\140\157
       \226\136\151 \226\140\156List.nth_error ls uid = Some lk\226\140\157
         \226\136\151 is_lock boxN lk (InboxLockInv \206\179) True.
Time Proof.
Time iIntros "HG".
Time iDestruct "HG" as ( lk \206\179 Hlookup1 Hlookup2 ) "(#Hlock&HI)".
Time iExists _ , _.
Time iFrame "%".
Time iFrame "Hlock".
Time Qed.
Time
Lemma MsgsInv_pers_split \206\147 \207\131 ls uid v :
  \207\131.(messages) !! uid = Some v
  \226\134\146 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm true)
    -\226\136\151 \226\136\131 lk \206\179,
         \226\140\156\206\147 !! uid = Some \206\179\226\140\157
         \226\136\151 \226\140\156List.nth_error ls uid = Some lk\226\140\157
           \226\136\151 is_lock boxN lk (InboxLockInv \206\179) True.
Time Proof.
Time iIntros ( ? ) "Hm".
Time (iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto).
Time iDestruct (MsgInv_pers_split with "Huid") as "$".
Time Qed.
Time
Lemma MsgInv_weaken \206\147 lks uid lm open :
  MsgInv \206\147 lks uid lm open -\226\136\151 MsgInv_weak \206\147 uid lm open.
Time Proof.
Time iIntros "H".
Time iDestruct "H" as ( lk \206\179 Hlookup ) "(_&Hinbox)".
Time iExists _ , _.
Time (iSplitL ""; auto).
Time iDestruct "Hinbox" as "(?&Hmb&?&?)".
Time iFrame.
Time Qed.
Time #[global]
Instance tmp_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo _ _) :=
 {| generic_mapsto := \206\187 l q v, Count_GHeap.mapsto (hG:=hGTmp) l q v |}%I.
Time
Definition TmpInv : iProp \206\163 :=
  (\226\136\131 tmps_map,
     SpoolDir \226\134\166 dom (gset string) tmps_map
     \226\136\151 SpoolDir \226\134\166 Unlocked
       \226\136\151 gen_heap_ctx tmps_map
         \226\136\151 ([\226\136\151 map] name\226\134\166inode \226\136\136 tmps_map, path.mk SpoolDir name \226\134\166 inode))%I.
Time Definition execN : namespace := nroot.@"msgs_inv".
Time #[global]
Instance InboxLockInv_Timeless  \206\179 n: (Timeless (InboxLockInv \206\179 n)).
Time Proof.
Time (apply _).
Time Qed.
Time
Definition ExecInv :=
  (\226\136\131 \206\147 \206\179,
     source_ctx
     \226\136\151 inv execN (\226\136\131 \207\131, source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv))%I.
Time
Definition ExecInner :=
  (\226\136\131 \206\147 \206\179 \207\131,
     \226\140\156\207\131.(open) = false\226\140\157 \226\136\151 source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv)%I.
Time
Lemma GlobalInv_unify lsptr ls ls' :
  global \226\134\166{ - 1} Some lsptr
  -\226\136\151 lsptr \226\134\166{ - 1} (ls, ls) -\226\136\151 GlobalInv ls' true -\226\136\151 \226\140\156ls = ls'\226\140\157.
Time Proof.
Time iIntros "Hgptr Hlsptr HG".
Time iDestruct "HG" as ( lsptr' ? ) "(Hgptr'&Hlsptr')".
Time rewrite //=.
Time
iDestruct (ghost_var_agree2 (A:=discreteC sliceLockC) with "Hgptr Hgptr'") as
 % Heq.
Time (inversion Heq; subst).
Time (iDestruct (slice_agree with "Hlsptr Hlsptr'") as "(?&?)"; eauto).
Time Qed.
Time
Lemma InboxLockInv_set_msgs \206\179 n S :
  InboxLockInv \206\179 n
  ==\226\136\151 ghost_mapsto_auth \206\179 (A:=discreteC contents) S
      \226\136\151 ghost_mapsto (A:=discreteC contents) \206\179 O S.
Time Proof.
Time iIntros "Hlockinv".
Time iDestruct "Hlockinv" as ( ? ? ) "(H1&H2)".
Time
by iMod (ghost_var_update (A:=discreteC contents) with "H1 H2") as "($&$)".
Time Qed.
Time
Lemma slice_mapsto_len {T} (s : slice.t T) (ls0 ls : Datatypes.list T) :
  s \226\134\166 (ls0, ls) -\226\136\151 \226\140\156s.(slice.length) = length ls\226\140\157.
Time Proof.
Time iIntros "Hpts".
Time iDestruct "Hpts" as ( ? ? ) "Hpts".
Time iPureIntro.
Time symmetry.
Time (eapply getSliceModel_len_inv; eauto).
Time Qed.
Time
Lemma slice_mapsto_len' {T} (s : slice.t T) (ls : Datatypes.list T) :
  s \226\134\166 ls -\226\136\151 \226\140\156s.(slice.length) = length ls\226\140\157.
Time Proof.
Time iIntros "Hpts".
Time iDestruct "Hpts" as ( ? ? ) "Hpts".
Time iPureIntro.
Time symmetry.
Time (eapply getSliceModel_len_inv; eauto).
Time Qed.
Time
Definition writeBuf {model : GoModel} f (data : slice.t byte) :=
  (Loop
     (fun buf =>
      if compare_to (slice.length buf) 4096 Lt
      then _ <- FS.append f buf; LoopRet tt
      else _ <- FS.append f (slice.take 4096 buf);
           Continue (slice.skip 4096 buf)) data)%proc.
Time
Lemma slice_take_split {A} k data (bs0 bs : List.list A) 
  q :
  k \226\137\164 data.(slice.length)
  \226\134\146 data \226\134\166{ q} (bs0, bs)
    -\226\136\151 slice.take k data \226\134\166{ q} (bs0, take k bs)
       \226\136\151 (slice.take k data \226\134\166{ q} (bs0, take k bs) -\226\136\151 data \226\134\166{ q} (bs0, bs)).
Time Proof.
Time iIntros ( Hlen ) "H".
Time iDestruct "H" as ( HgetSlice ) "H".
Time iSplitL "H".
Time *
Time iFrame.
Time iPureIntro.
Time move : {}HgetSlice {}.
Time rewrite /Data.getSliceModel //=.
Time rewrite /sublist_lookup /mguard /option_guard.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by inversion 1).
Time (<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by lia).
Time (inversion 1).
Time subst.
Time f_equal.
Time rewrite take_take.
Time f_equal.
Time lia.
Time *
Time iIntros "H".
Time iDestruct "H" as ( HgetSlice' ) "H".
Time (simpl).
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma skipn_firstn_comm' {A} (m n : nat) (l : Datatypes.list A) :
  drop m (take n l) = take (n - m) (drop m l).
Time Proof.
Time revert n l.
Time (induction m; intros [] []; rewrite ?skipn_O -?minus_n_O ?take_nil //=).
Time Qed.
Time
Lemma slice_skip_split {A} k data (bs0 bs : List.list A) 
  q :
  k \226\137\164 data.(slice.length)
  \226\134\146 data \226\134\166{ q} (bs0, bs)
    -\226\136\151 slice.skip k data \226\134\166{ q} (bs0, drop k bs)
       \226\136\151 (slice.skip k data \226\134\166{ q} (bs0, drop k bs) -\226\136\151 data \226\134\166{ q} (bs0, bs)).
Time Proof.
Time iIntros ( Hlen ) "H".
Time iDestruct "H" as ( HgetSlice ) "H".
Time iSplitL "H".
Time *
Time iFrame.
Time iPureIntro.
Time move : {}HgetSlice {}.
Time rewrite /Data.getSliceModel //=.
Time rewrite /sublist_lookup /mguard /option_guard.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by inversion 1).
Time (<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by lia).
Time (inversion 1).
Time subst.
Time f_equal.
Time rewrite skipn_firstn_comm' drop_drop //.
Time *
Time iIntros "H".
Time iDestruct "H" as ( HgetSlice' ) "H".
Time (simpl).
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma wp_writeBuf f data inode bs0 bs1 bs2 q :
  {{{ f \226\134\166 (inode, Write) \226\136\151 inode \226\134\166 bs1 \226\136\151 data \226\134\166{ q} (bs0, bs2) }}} 
  writeBuf f data {{{ RET tt; f \226\134\166 (inode, Write)
                              \226\136\151 inode \226\134\166 (bs1 ++ bs2) \226\136\151 data \226\134\166{ q} (bs0, bs2)}}}.
Time Proof.
Time rewrite /writeBuf.
Time rewrite -MAX_WRITE_LEN_unfold.
Time iIntros ( \206\166 ) "(Hf&Hinode&Hdata) H\206\166".
Time iL\195\182b as "IH" forall ( data bs1 bs2 q ).
Time wp_loop.
Time (destruct compare_to).
Time -
Time wp_bind.
Time iAssert \226\140\156length bs2 < MAX_WRITE_LEN\226\140\157%I with "[-]" as "%".
Time {
Time iDestruct "Hdata" as "(%&?)".
Time iPureIntro.
Time (erewrite getSliceModel_len_inv; eauto).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_append with "[$]") ; first  by
 lia).
Time iIntros "!> H".
Time (do 2 wp_ret).
Time by iApply "H\206\166".
Time -
Time wp_bind.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (slice_take_split MAX_WRITE_LEN with "Hdata") as "(Htake&Hwand)" ; first  by
 lia).
Time iApply (wp_append with "[$]").
Time {
Time rewrite take_length.
Time lia.
Time }
Time iIntros "!> (Hf&Hinode&Hdata)".
Time iDestruct ("Hwand" with "Hdata") as "Hdata".
Time wp_ret.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct
 (slice_skip_split MAX_WRITE_LEN with "Hdata") as "(Hdrop&Hwand)" ; first  by
 lia).
Time iApply ("IH" with "Hf Hinode Hdrop [H\206\166 Hwand]").
Time iIntros "!> (Hf&Hinode&Hdata)".
Time iDestruct ("Hwand" with "Hdata") as "Hdata".
Time iApply "H\206\166".
Time iFrame.
Time rewrite -app_assoc take_drop //.
Time Qed.
Time
Definition readMessage_handle f :=
  (fileContents <- Data.newPtr (slice.t byte);
   initData <- Data.newSlice byte 0;
   _ <-
   Loop
     (fun pf =>
      buf <- FS.readAt f pf.(partialFile.off) 512;
      newData <- Data.sliceAppendSlice pf.(partialFile.data) buf;
      if compare_to (slice.length buf) 512 Lt
      then _ <- Data.writePtr fileContents newData; LoopRet tt
      else Continue
             {|
             partialFile.off := pf.(partialFile.off) + slice.length buf;
             partialFile.data := newData |})
     {| partialFile.off := 0; partialFile.data := initData |};
   fileData <- Data.readPtr fileContents;
   fileStr <- Data.bytesToString fileData; _ <- FS.close f; Ret fileStr)%proc.
Time
Lemma readMessage_unfold_open userDir name :
  readMessage userDir name =
  (let! f <- FS.open userDir name; readMessage_handle f)%proc.
Time Proof.
Time auto.
Time Qed.
Time Opaque readMessage.
Time
Lemma take_length_lt {A} (l : Datatypes.list A) (n : nat) :
  length (take n l) < n \226\134\146 take n l = l.
Time Proof.
Time (intros Hlen).
Time (apply take_ge).
Time rewrite take_length in  {} Hlen.
Time lia.
Time Qed.
Time
Lemma wp_readMessage_handle f inode ls q2 :
  {{{ f \226\134\166 (inode, Read) \226\136\151 inode \226\134\166{ q2} ls }}} readMessage_handle f {{{ RET 
  bytes_to_string ls; inode \226\134\166{ q2} ls}}}.
Time Proof.
Time rewrite /readMessage_handle.
Time (<ssreflect_plugin::ssrtclintros@0> generalize 512 =>k).
Time iIntros ( \206\166 ) "(Hf&Hinode) H\206\166".
Time wp_bind.
Time iApply (wp_newAlloc with "[//]").
Time iIntros ( fileContents ) "!> HfC".
Time wp_bind.
Time iApply (@wp_newSlice with "[//]").
Time iIntros ( fileSlice ) "!> HfS".
Time (simpl repeat).
Time replace [] with take 0 ls by auto.
Time (<ssreflect_plugin::ssrtclintros@0> generalize 0 =>idx).
Time wp_bind.
Time iAssert (fileSlice \226\134\166 take idx ls)%I with "[HfS]" as "HfS".
Time {
Time (iExists _; eauto).
Time }
Time iL\195\182b as "IH" forall ( fileSlice idx ).
Time wp_loop.
Time wp_bind.
Time iApply (wp_readAt with "[$]").
Time iIntros ( s ) "!> (Hf&Hinode&Hs)".
Time wp_bind.
Time iApply (wp_sliceAppendSlice with "[HfS Hs]").
Time {
Time iFrame.
Time }
Time (simpl).
Time clear fileSlice.
Time iIntros ( fileSlice ) "!> (HfS&Hs)".
Time iDestruct (slice_mapsto_len with "Hs") as % ->.
Time iClear "Hs".
Time (destruct lt_dec as [Hlt| Hnlt]).
Time -
Time wp_bind.
Time iApply (wp_writePtr with "[$]").
Time iIntros "!> HfC".
Time wp_ret.
Time iNext.
Time wp_ret.
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time iIntros "!> HfC".
Time wp_bind.
Time iApply (wp_bytesToString' with "HfS").
Time iIntros "!> _".
Time wp_bind.
Time iApply (wp_close with "Hf").
Time iIntros "!> _".
Time wp_ret.
Time (apply take_length_lt in Hlt).
Time rewrite Hlt.
Time rewrite take_drop.
Time iApply "H\206\166".
Time iFrame.
Time -
Time wp_ret.
Time iNext.
Time iApply ("IH" with "[$] [$] [$] [$]").
Time rewrite take_take_drop.
Time
(<ssreflect_plugin::ssrtclseq@0>
 assert (length (take k (drop idx ls)) = k) as -> ; last  by eauto).
Time
(<ssreflect_plugin::ssrtclseq@0> cut (length (take k (drop idx ls)) \226\137\164 k) ;
 first  by lia).
Time (eapply firstn_le_length).
Time Qed.
Time
Lemma createMessages_length msgs : length (createMessages msgs) = length msgs.
Time Proof.
Time by rewrite map_length.
Time Qed.
Time
Lemma nth_error_map {A B : Type} (f : A \226\134\146 B) (n : nat) 
  l (b : B) :
  nth_error (map f l) n = Some b \226\134\146 \226\136\131 a, f a = b \226\136\167 nth_error l n = Some a.
Time Proof.
Time revert l.
Time (<ssreflect_plugin::ssrtclintros@0> induction n =>l //=).
Time *
Time (<ssreflect_plugin::ssrtclintros@0> destruct l as [| a l] =>//=).
Time (intros).
Time (exists a; split; congruence).
Time *
Time (<ssreflect_plugin::ssrtclintros@0> destruct l as [| a l] =>//=).
Time (intros).
Time eauto.
Time Qed.
Time
Lemma take_snoc_S {A} (ls : List.list A) (i : nat) 
  a : nth_error ls i = Some a \226\134\146 take (i + 1) ls = take i ls ++ [a].
Time Proof.
Time (intros Hin).
Time revert ls Hin.
Time (<ssreflect_plugin::ssrtclintros@0> induction i =>ls Hin).
Time -
Time rewrite //=.
Time (destruct ls; inversion Hin; subst).
Time (simpl).
Time by rewrite firstn_O.
Time -
Time rewrite //=.
Time (destruct ls; inversion Hin).
Time (simpl).
Time f_equal.
Time eauto.
Time Qed.
Time
Lemma writeTmp_unfold_writeBuf msg :
  writeTmp msg =
  (let! (f, name) <- createTmp; _ <- writeBuf f msg; _ <- close f; Ret name)%proc.
Time Proof.
Time trivial.
Time Qed.
Time Opaque writeTmp.
Time #[global]
Instance ghost_init_status_inhabited : (Inhabited ghost_init_status).
Time Proof.
Time econstructor.
Time exact Uninit.
Time Qed.
Time Lemma userRange_in_elim s k : userRange_ok s \226\134\146 k \226\136\136 s \226\134\146 k < NumUsers.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>Hrange ?).
Time (destruct (lt_dec k NumUsers) as [?| Hn]; auto).
Time (assert (k \226\137\165 NumUsers) by lia).
Time (exfalso; eapply Hrange; eauto).
Time Qed.
Time
Lemma nth_error_snoc {A : Type} (l : List.list A) 
  (a : A) : nth_error (l ++ [a]) (length l) = Some a.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> induction l =>//=).
Time Qed.
Time
Lemma nth_error_snoc_ne {A : Type} (l : List.list A) 
  (a : A) k : k \226\137\160 length l \226\134\146 nth_error (l ++ [a]) k = nth_error l k.
Time Proof.
Time (intros Hneq).
Time (destruct (lt_dec k (length l)) as [?| Hgt]).
Time -
Time rewrite nth_error_app1 //.
Time -
Time (assert (length l < k) by lia).
Time etransitivity.
Time *
Time (eapply nth_error_None).
Time rewrite app_length //=.
Time lia.
Time *
Time symmetry.
Time (eapply nth_error_None).
Time lia.
Time Qed.
Time
Lemma open_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} :
  {{{ j \226\164\135 K (Call Open) \226\136\151 Registered \226\136\151 ExecInv }}} MailServer.Open {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
Time iDestruct "Hrest" as ( \206\147 \206\179 ) "(#Hsource&#Hinv)".
Time rewrite /MailServer.Open.
Time wp_bind.
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iDestruct "Hmsgs" as ( ls ) "(Hglobal&>Hrootdir&Hinit&Hm)".
Time iDestruct (RootDirInv_range_ok with "Hrootdir") as % Hrange_ok.
Time iDestruct "Hinit" as ( init_stat ) "Hinit".
Time iMod (open_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)".
Time {
Time solve_ndisj.
Time }
Time (destruct init_stat; swap 1 3).
Time {
Time iDestruct "Hinit" as ">(?&%)".
Time exfalso.
Time congruence.
Time }
Time {
Time iDestruct "Hinit" as ">(?&Hj'&%)".
Time iMod (open_open_step_inv with "Hj Hj' [$] [$]").
Time {
Time solve_ndisj.
Time }
Time eauto.
Time }
Time iDestruct "Hinit" as ">(Hauth&Hfrag&%&Hghosts)".
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  by auto).
Time iIntros ( locks0 ) "!> Hlocks0".
Time iExists _.
Time iFrame.
Time iExists _.
Time iFrame.
Time
iMod (ghost_var_update (A:=ghost_init_statusC) with "[$] [$]") as
 "(Hauth&Hfrag)".
Time iSplitL "Hauth Hj".
Time {
Time iExists (Started_Init _ _).
Time iFrame.
Time eauto.
Time }
Time iModIntro.
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply @wp_newSlice ; first  by auto).
Time iIntros ( locks ) "!> Hlocks".
Time wp_bind.
Time iApply (wp_writePtr with "[$]").
Time iIntros "!> Hlocks0".
Time (simpl repeat).
Time wp_bind.
Time (remember (@nil LockRef) as lock_list eqn:Heq_lock_list ).
Time
(<ssreflect_plugin::ssrtclseq@0> replace 0 with length lock_list 
  at 1 ; last  first).
Time {
Time rewrite Heq_lock_list //.
Time }
Time iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
Time
iAssert
 ([\226\136\151 set] k \226\136\136 dom (gset _) \207\131.(messages), \226\136\131 \206\179uid : gname,
                                           \226\140\156\206\147 !! k = Some \206\179uid\226\140\157
                                           \226\136\151 match nth_error lock_list k with
                                             | Some lk =>
                                                 is_lock boxN lk
                                                 (InboxLockInv \206\179uid) True
                                             | None => InboxLockInv \206\179uid 0
                                             end)%I with "[Hghosts]" as
 "Hghosts".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_mono ; last  auto).
Time iIntros ( k Hin ) "H".
Time iDestruct "H" as ( \206\179uid ) "(Heq&Hlock)".
Time (iExists _; iFrame).
Time rewrite Heq_lock_list.
Time (destruct k; auto).
Time }
Time
(assert (Hlen : length lock_list <= NumUsers) by
  (rewrite Heq_lock_list; cbn[length]; lia)).
Time clear Heq_lock_list.
Time iL\195\182b as "IH" forall ( lock_list locks Hlen ).
Time wp_loop.
Time (destruct equal).
Time -
Time iClear "IH".
Time wp_ret.
Time wp_ret.
Time iIntros "!>".
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time iIntros "!> Hlocks0".
Time iInv "Hinv" as "H".
Time iDestruct "H" as ( \207\131' ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
Time iDestruct "Hmsgs" as ( ls' ) "(Hglobal&>Hrootdir&Hinit&Hm)".
Time iDestruct (RootDirInv_range_ok with "Hrootdir") as % Hrange_ok'.
Time iDestruct "Hinit" as ( init_stat ) "Hinit".
Time iDestruct "Hinit" as "(>Hauth&Hinit)".
Time
iDestruct (ghost_var_agree (A:=ghost_init_statusC) with "Hauth Hfrag") as %
 Heq.
Time subst.
Time iDestruct "Hinit" as ">(Hj&Hopen')".
Time iDestruct "Hopen'" as % Hopen'.
Time rewrite Hopen'.
Time (simpl GlobalInv).
Time iDestruct "Hglobal" as ">Hglobal".
Time iApply (wp_setX with "[$]").
Time iIntros "!> Hglobal".
Time rewrite (userRange_ok_eq _ _ Hrange_ok Hrange_ok').
Time
iAssert
 ([\226\136\151 set] k \226\136\136 dom (gset uint64) \207\131'.(messages), \226\136\131 \206\179uid lk,
                                                 \226\140\156
                                                 \206\147 !! k = Some \206\179uid\226\140\157
                                                 \226\136\151 
                                                 \226\140\156
                                                 lock_list !! k = Some lk\226\140\157
                                                 \226\136\151 
                                                 is_lock boxN lk
                                                 (InboxLockInv \206\179uid) True)%I
 with "[Hghosts]" as "Hghosts".
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_mono ; last  eauto).
Time iIntros ( k Hin ) "H".
Time iDestruct "H" as ( \206\179uid Heq ) "H".
Time iExists \206\179uid.
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct nth_error as [lk| ] eqn:Heq_nth_error ; last  first).
Time {
Time exfalso.
Time rewrite nth_error_None in  {} Heq_nth_error *.
Time (eapply userRange_in_elim in Hin; auto).
Time rewrite e.
Time lia.
Time }
Time iExists lk.
Time (iSplitL ""; auto).
Time (iSplitL ""; auto).
Time iPureIntro.
Time rewrite -nth_error_lookup //.
Time }
Time iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
Time {
Time (intros).
Time econstructor.
Time
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
Time (econstructor; eauto).
Time (do 2 eexists; split).
Time {
Time rewrite /reads Hopen'.
Time eauto.
Time }
Time (do 2 econstructor; split; econstructor).
Time }
Time {
Time solve_ndisj.
Time }
Time iExists _.
Time iFrame.
Time iExists lock_list.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "Hj H\206\166 Hreg" ; last  first).
Time {
Time iModIntro.
Time (iApply "H\206\166"; iFrame).
Time }
Time iExists _ , O.
Time iFrame.
Time
iMod (ghost_var_update (A:=ghost_init_statusC) with "Hauth Hfrag") as
 "(Hauth&Hfrag)".
Time iSplitL "Hrootdir".
Time {
Time iModIntro.
Time rewrite /RootDirInv.
Time (simpl).
Time (rewrite dom_fmap_L //; eauto).
Time }
Time iSplitL "Hauth".
Time {
Time iExists Finished_Init.
Time iFrame.
Time eauto.
Time }
Time iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
Time iDestruct (big_sepM_sep with "[Hm Hghosts]") as "Hm".
Time {
Time iFrame.
Time }
Time iModIntro.
Time iNext.
Time rewrite big_sepM_fmap.
Time (iApply big_sepM_mono; iFrame).
Time iIntros ( k (mstat, msgs) Hin ) "(H1&H2)".
Time iDestruct "H1" as ( \206\179' lk' ? ? ) "H".
Time (simpl).
Time iDestruct "H2" as ( ? ? _ _ _ ) "((Hinterp&?)&?&Hin)".
Time iExists _ , _.
Time rewrite nth_error_lookup.
Time (iSplitL ""; auto).
Time (iSplitL ""; auto).
Time iFrame.
Time -
Time wp_bind.
Time iApply (wp_readPtr with "[$]").
Time iIntros "!> Hlocks0".
Time wp_bind.
Time (assert (length lock_list \226\136\136 dom (gset uint64) \207\131.(messages))).
Time {
Time (eapply Hrange_ok).
Time move : {}Hlen {}n {}.
Time rewrite /NumUsers.
Time (inversion 1; eauto).
Time *
Time congruence.
Time *
Time subst.
Time lia.
Time }
