Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq6RXUKB"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 104.
Set Silent.
From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Armada.Examples.MailServer Require Import MailAPI MailAPILemmas MailHeap.
From Armada.Goose.Examples Require Import MailServer.
From Armada.Goose.Proof Require Import Interp.
Require Import Goose.Proof.Interp.
From Armada Require AtomicPair.Helpers.
From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Armada.Goose Require Import Machine.
From Armada.Goose Require Import GoZeroValues.
Unset Implicit Arguments.
Inductive ghost_init_status {gm : GoModel} {gmwf : GoModelWf gm} :=
  | Uninit : _
  | Started_Init : forall (j : nat) {T2} K `{LanguageCtx _ unit T2 Mail.l K}, _
  | Finished_Init : _.
Lemma map_Permutation (A B : Type) (f : A \226\134\146 B) (al : list A) (bl : list B) :
  Permutation.Permutation (map f al) bl \226\134\146 \226\136\131 al', Permutation.Permutation al al' \226\136\167 map f al' = bl.
Proof.
(intros Hperm).
(remember (map f al) as bl0 eqn:Heq ).
revert Heq.
revert al.
(<ssreflect_plugin::ssrtclintros@0> induction Hperm =>al Heq).
-
(destruct al).
exists [].
eauto.
(inversion Heq).
-
(destruct al as [| a al]; inversion Heq; subst).
(simpl in Heq).
(edestruct (IHHperm) as (al', (?, ?)); eauto).
subst.
exists (a :: al').
(split; eauto).
-
(destruct al as [| a [| b al]]; try inversion Heq; subst).
(exists (b :: a :: al); split; eauto).
econstructor.
-
(edestruct (IHHperm1) as (al1, (?, ?)); eauto).
(edestruct (IHHperm2) as (al2, (?, ?)); eauto).
(exists al2; split; eauto).
(etransitivity; try eassumption; eauto).
Qed.
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.
Set Default Goal Selector "!".
Notation contents := (gmap string (Datatypes.list byte)).
Canonical Structure contentsC {m : GoModel} {wf : GoModelWf m} := leibnizC contents.
Canonical Structure contentsF {m : GoModel} {wf : GoModelWf m} := discreteC contents.
Canonical Structure ghost_init_statusC {m : GoModel} {wf : GoModelWf m} := leibnizC ghost_init_status.
Canonical Structure ghost_init_statusF {m : GoModel} {wf : GoModelWf m} := discreteC ghost_init_status.
Definition UserDir {model : GoModel} (user : uint64) := ("user" ++ uint64_to_string user)%string.
Set Default Proof Using "Type".
Section refinement_triples.
Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Context {hGcontents : ghost_mapG contentsC \206\163}.
Context {hGinit : ghost_mapG ghost_init_statusC \206\163}.
Context {hGTmp : gen_heapG string Filesys.FS.Inode \206\163}.
Import Filesys.FS.
Import GoLayer.Go.
Import Mail.
Definition InboxLockInv (\206\179 : gname) (n : nat) :=
  (\226\136\131 S1 S2,
     ghost_mapsto_auth \206\179 (A:=discreteC contents) S1 \226\136\151 ghost_mapsto (A:=discreteC contents) \206\179 O S2)%I.
Definition MailboxStatusInterp (uid : uint64) (lk : LockRef) (\206\179 : gname) (ls : MailboxStatus)
  (msgs : contents) (open : bool) :=
  (if open
   then match ls with
        | MUnlocked => UserDir uid \226\134\166 Unlocked \226\136\168 UserDir uid \226\134\166{ - 1} ReadLocked 0 \226\136\151 InboxLockInv \206\179 O
        | MPickingUp =>
            wlocked lk \226\136\151 (\226\136\131 S : contents, ghost_mapsto_auth \206\179 (A:=contentsC) S \226\136\151 \226\140\156S \226\138\134 msgs\226\140\157)
        | MLocked => wlocked lk \226\136\151 InboxLockInv \206\179 O \226\136\151 UserDir uid \226\134\166 Unlocked
        end else \226\140\156ls = ls\226\140\157 \226\136\151 UserDir uid \226\134\166 Unlocked)%I.
Definition boxN : namespace := nroot.@"inbox_lock".
Definition InboxInv (uid : uint64) (lk : LockRef) (\206\179 : gname) (ls : MailboxStatus)
  (msgs : gmap.gmap string (Datatypes.list byte)) (open : bool) :=
  ((if open then is_lock boxN lk (InboxLockInv \206\179) True else True)
   \226\136\151 MailboxStatusInterp uid lk \206\179 ls msgs open
     \226\136\151 UserDir uid \226\134\166 dom (gset string) msgs
       \226\136\151 ([\226\136\151 map] mid\226\134\166msgData \226\136\136 msgs, \226\136\131 inode (n : nat),
                                        path.mk (UserDir uid) mid \226\134\166 inode \226\136\151 inode \226\134\166{ n} msgData))%I.
Definition InboxInv_weak (uid : uint64) (lk : LockRef) (\206\179 : gname) (ls : MailboxStatus)
  (msgs : gmap.gmap string (Datatypes.list byte)) (open : bool) :=
  (MailboxStatusInterp uid lk \206\179 ls msgs open
   \226\136\151 UserDir uid \226\134\166 dom (gset string) msgs
     \226\136\151 ([\226\136\151 map] mid\226\134\166msgData \226\136\136 msgs, \226\136\131 inode (n : nat),
                                      path.mk (UserDir uid) mid \226\134\166 inode \226\136\151 inode \226\134\166{ n} msgData))%I.
#[global]
Instance InboxInv_timeless  uid lk \206\179 ls msgs open': (Timeless (InboxInv_weak uid lk \206\179 ls msgs open')).
Proof.
rewrite /InboxInv_weak.
(destruct ls, open'; apply _).
Qed.
Definition GlobalInv ls (open : bool) : iProp \206\163 :=
  (if open then \226\136\131 (lsptr : slice.t LockRef) (q : nat), global \226\134\166{ q} Some lsptr \226\136\151 lsptr \226\134\166{ q} (ls, ls)
   else global \226\134\166 None)%I.
Lemma GlobalInv_split ls :
  GlobalInv ls true \226\138\162 GlobalInv ls true \226\136\151 (\226\136\131 lsptr, global \226\134\166{ - 1} Some lsptr \226\136\151 lsptr \226\134\166{ - 1} (ls, ls)).
Proof.
iIntros "HG".
iDestruct "HG" as ( lsptr q ) "(HP1&HP2)".
iDestruct "HP2" as ( Heq ? ) "HP2".
rewrite //= @read_split /ptr_mapsto Count_Typed_Heap.read_split_join.
iDestruct "HP1" as "(HP1&HR1)".
iDestruct "HP2" as "(HP2&HR2)".
iSplitL "HP1 HP2".
{
iExists lsptr , (S q).
iFrame.
by iFrame.
}
iExists _.
iFrame.
by iFrame.
Qed.
Definition MsgInv (\206\147 : gmap uint64 gname) ls uid lm (open : bool) : iProp \206\163 :=
  (\226\136\131 lk \206\179,
     \226\140\156\206\147 !! uid = Some \206\179\226\140\157
     \226\136\151 \226\140\156if open then List.nth_error ls uid = Some lk else True\226\140\157
       \226\136\151 InboxInv uid lk \206\179 (fst lm) (snd lm) open)%I.
Definition MsgInv_weak (\206\147 : gmap uint64 gname) uid lm (open : bool) : iProp \206\163 :=
  (\226\136\131 lk \206\179, \226\140\156\206\147 !! uid = Some \206\179\226\140\157 \226\136\151 InboxInv_weak uid lk \206\179 (fst lm) (snd lm) open)%I.
#[global]Instance MsgInv_weak_timeless  \206\147 uid x open: (Timeless (MsgInv_weak \206\147 uid x open)).
Proof.
rewrite /MsgInv_weak.
(apply _).
Qed.
Definition userRange_ok (s : gset uint64) :=
  forall uid : uint64, (uid < 100 -> uid \226\136\136 s) /\ (uid >= 100 -> \194\172 uid \226\136\136 s).
Definition RootDirInv (\207\131 : Mail.State) : iProp \206\163 :=
  (rootdir \226\134\166{ - 1} (set_map UserDir (dom (gset uint64) \207\131.(messages)) \226\136\170 {[SpoolDir]})
   \226\136\151 \226\140\156userRange_ok (dom (gset uint64) \207\131.(messages))\226\140\157)%I.
Lemma RootDirInv_range_ok \207\131 : RootDirInv \207\131 -\226\136\151 \226\140\156userRange_ok (dom (gset _) \207\131.(messages))\226\140\157.
Proof.
by iIntros "(?&$)".
Qed.
Lemma userRange_ok_eq s s' : userRange_ok s \226\134\146 userRange_ok s' \226\134\146 s = s'.
Proof.
(<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>Hok1 Hok2).
(<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>i).
clear - Hok1 Hok2.
(destruct (Hok1 i) as (Hlt1, Hge1)).
(destruct (Hok2 i) as (Hlt2, Hge2)).
(destruct (lt_dec i 100) as [Hlt| Hnlt]).
-
intuition.
-
(assert (i >= 100) by lia).
intuition.
Qed.
Definition InitInv (\206\147 : gmap uint64 gname) \206\179 \207\131 :=
  (\226\136\131 v : ghost_init_status,
     ghost_mapsto_auth \206\179 v
     \226\136\151 match v with
       | Uninit =>
           ghost_mapsto \206\179 O v
           \226\136\151 \226\140\156\207\131.(open) = false\226\140\157
             \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), \226\136\131 \206\179uid, \226\140\156\206\147 !! uid = Some \206\179uid\226\140\157 \226\136\151 InboxLockInv \206\179uid O)
       | Started_Init j K => j \226\164\135 K (Call Open) \226\136\151 \226\140\156\207\131.(open) = false\226\140\157
       | Finished_Init => \226\140\156\207\131.(open) = true\226\140\157
       end)%I.
Definition MsgsInv (\206\147 : gmap uint64 gname) (\206\179 : gname) (\207\131 : Mail.State) : iProp \206\163 :=
  (\226\136\131 ls,
     GlobalInv ls \207\131.(open)
     \226\136\151 RootDirInv \207\131 \226\136\151 InitInv \206\147 \206\179 \207\131 \226\136\151 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm \207\131.(open)))%I.
Lemma MsgInv_pers_split \206\147 ls uid lm :
  MsgInv \206\147 ls uid lm true
  -\226\136\151 \226\136\131 lk \206\179,
       \226\140\156\206\147 !! uid = Some \206\179\226\140\157 \226\136\151 \226\140\156List.nth_error ls uid = Some lk\226\140\157 \226\136\151 is_lock boxN lk (InboxLockInv \206\179) True.
Proof.
iIntros "HG".
iDestruct "HG" as ( lk \206\179 Hlookup1 Hlookup2 ) "(#Hlock&HI)".
iExists _ , _.
iFrame "%".
iFrame "Hlock".
Qed.
Lemma MsgsInv_pers_split \206\147 \207\131 ls uid v :
  \207\131.(messages) !! uid = Some v
  \226\134\146 ([\226\136\151 map] uid\226\134\166lm \226\136\136 \207\131.(messages), MsgInv \206\147 ls uid lm true)
    -\226\136\151 \226\136\131 lk \206\179,
         \226\140\156\206\147 !! uid = Some \206\179\226\140\157
         \226\136\151 \226\140\156List.nth_error ls uid = Some lk\226\140\157 \226\136\151 is_lock boxN lk (InboxLockInv \206\179) True.
Proof.
iIntros ( ? ) "Hm".
(iDestruct (big_sepM_lookup_acc with "Hm") as "(Huid&Hm)"; eauto).
iDestruct (MsgInv_pers_split with "Huid") as "$".
Qed.
Lemma MsgInv_weaken \206\147 lks uid lm open : MsgInv \206\147 lks uid lm open -\226\136\151 MsgInv_weak \206\147 uid lm open.
Proof.
iIntros "H".
iDestruct "H" as ( lk \206\179 Hlookup ) "(_&Hinbox)".
iExists _ , _.
(iSplitL ""; auto).
iDestruct "Hinbox" as "(?&Hmb&?&?)".
iFrame.
Qed.
#[global]
Instance tmp_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo _ _) :=
 {| generic_mapsto := \206\187 l q v, Count_GHeap.mapsto (hG:=hGTmp) l q v |}%I.
Definition TmpInv : iProp \206\163 :=
  (\226\136\131 tmps_map,
     SpoolDir \226\134\166 dom (gset string) tmps_map
     \226\136\151 SpoolDir \226\134\166 Unlocked
       \226\136\151 gen_heap_ctx tmps_map \226\136\151 ([\226\136\151 map] name\226\134\166inode \226\136\136 tmps_map, path.mk SpoolDir name \226\134\166 inode))%I.
Definition execN : namespace := nroot.@"msgs_inv".
#[global]Instance InboxLockInv_Timeless  \206\179 n: (Timeless (InboxLockInv \206\179 n)).
Proof.
(apply _).
Qed.
Definition ExecInv :=
  (\226\136\131 \206\147 \206\179, source_ctx \226\136\151 inv execN (\226\136\131 \207\131, source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv))%I.
Definition ExecInner :=
  (\226\136\131 \206\147 \206\179 \207\131, \226\140\156\207\131.(open) = false\226\140\157 \226\136\151 source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv)%I.
Lemma GlobalInv_unify lsptr ls ls' :
  global \226\134\166{ - 1} Some lsptr -\226\136\151 lsptr \226\134\166{ - 1} (ls, ls) -\226\136\151 GlobalInv ls' true -\226\136\151 \226\140\156ls = ls'\226\140\157.
Proof.
iIntros "Hgptr Hlsptr HG".
iDestruct "HG" as ( lsptr' ? ) "(Hgptr'&Hlsptr')".
rewrite //=.
iDestruct (ghost_var_agree2 (A:=discreteC sliceLockC) with "Hgptr Hgptr'") as % Heq.
(inversion Heq; subst).
(iDestruct (slice_agree with "Hlsptr Hlsptr'") as "(?&?)"; eauto).
Qed.
Lemma InboxLockInv_set_msgs \206\179 n S :
  InboxLockInv \206\179 n
  ==\226\136\151 ghost_mapsto_auth \206\179 (A:=discreteC contents) S \226\136\151 ghost_mapsto (A:=discreteC contents) \206\179 O S.
Proof.
iIntros "Hlockinv".
iDestruct "Hlockinv" as ( ? ? ) "(H1&H2)".
by iMod (ghost_var_update (A:=discreteC contents) with "H1 H2") as "($&$)".
Qed.
Lemma slice_mapsto_len {T} (s : slice.t T) (ls0 ls : Datatypes.list T) :
  s \226\134\166 (ls0, ls) -\226\136\151 \226\140\156s.(slice.length) = length ls\226\140\157.
Proof.
iIntros "Hpts".
iDestruct "Hpts" as ( ? ? ) "Hpts".
iPureIntro.
symmetry.
(eapply getSliceModel_len_inv; eauto).
Qed.
Lemma slice_mapsto_len' {T} (s : slice.t T) (ls : Datatypes.list T) :
  s \226\134\166 ls -\226\136\151 \226\140\156s.(slice.length) = length ls\226\140\157.
Proof.
iIntros "Hpts".
iDestruct "Hpts" as ( ? ? ) "Hpts".
iPureIntro.
symmetry.
(eapply getSliceModel_len_inv; eauto).
Qed.
Definition writeBuf {model : GoModel} f (data : slice.t byte) :=
  (Loop
     (fun buf =>
      if compare_to (slice.length buf) 4096 Lt then _ <- FS.append f buf; LoopRet tt
      else _ <- FS.append f (slice.take 4096 buf); Continue (slice.skip 4096 buf)) data)%proc.
Lemma slice_take_split {A} k data (bs0 bs : List.list A) q :
  k \226\137\164 data.(slice.length)
  \226\134\146 data \226\134\166{ q} (bs0, bs)
    -\226\136\151 slice.take k data \226\134\166{ q} (bs0, take k bs)
       \226\136\151 (slice.take k data \226\134\166{ q} (bs0, take k bs) -\226\136\151 data \226\134\166{ q} (bs0, bs)).
Proof.
iIntros ( Hlen ) "H".
iDestruct "H" as ( HgetSlice ) "H".
iSplitL "H".
*
iFrame.
iPureIntro.
move : {}HgetSlice {}.
rewrite /Data.getSliceModel //=.
rewrite /sublist_lookup /mguard /option_guard.
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by inversion 1).
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by lia).
(inversion 1).
subst.
f_equal.
rewrite take_take.
f_equal.
lia.
*
iIntros "H".
iDestruct "H" as ( HgetSlice' ) "H".
(simpl).
iFrame.
eauto.
Qed.
Lemma skipn_firstn_comm' {A} (m n : nat) (l : Datatypes.list A) :
  drop m (take n l) = take (n - m) (drop m l).
Proof.
revert n l.
(induction m; intros [] []; rewrite ?skipn_O -?minus_n_O ?take_nil //=).
Qed.
Lemma slice_skip_split {A} k data (bs0 bs : List.list A) q :
  k \226\137\164 data.(slice.length)
  \226\134\146 data \226\134\166{ q} (bs0, bs)
    -\226\136\151 slice.skip k data \226\134\166{ q} (bs0, drop k bs)
       \226\136\151 (slice.skip k data \226\134\166{ q} (bs0, drop k bs) -\226\136\151 data \226\134\166{ q} (bs0, bs)).
Proof.
iIntros ( Hlen ) "H".
iDestruct "H" as ( HgetSlice ) "H".
iSplitL "H".
*
iFrame.
iPureIntro.
move : {}HgetSlice {}.
rewrite /Data.getSliceModel //=.
rewrite /sublist_lookup /mguard /option_guard.
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by inversion 1).
(<ssreflect_plugin::ssrtclseq@0> destruct decide_rel ; last  by lia).
(inversion 1).
subst.
f_equal.
rewrite skipn_firstn_comm' drop_drop //.
*
iIntros "H".
iDestruct "H" as ( HgetSlice' ) "H".
(simpl).
iFrame.
eauto.
Qed.
Lemma wp_writeBuf f data inode bs0 bs1 bs2 q :
  {{{ f \226\134\166 (inode, Write) \226\136\151 inode \226\134\166 bs1 \226\136\151 data \226\134\166{ q} (bs0, bs2) }}} writeBuf f data {{{ RET tt; 
  f \226\134\166 (inode, Write) \226\136\151 inode \226\134\166 (bs1 ++ bs2) \226\136\151 data \226\134\166{ q} (bs0, bs2)}}}.
Proof.
rewrite /writeBuf.
rewrite -MAX_WRITE_LEN_unfold.
iIntros ( \206\166 ) "(Hf&Hinode&Hdata) H\206\166".
iL\195\182b as "IH" forall ( data bs1 bs2 q ).
wp_loop.
(destruct compare_to).
-
wp_bind.
iAssert \226\140\156length bs2 < MAX_WRITE_LEN\226\140\157%I with "[-]" as "%".
{
iDestruct "Hdata" as "(%&?)".
iPureIntro.
(erewrite getSliceModel_len_inv; eauto).
}
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_append with "[$]") ; first  by lia).
iIntros "!> H".
(do 2 wp_ret).
by iApply "H\206\166".
-
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iDestruct (slice_take_split MAX_WRITE_LEN with "Hdata") as
 "(Htake&Hwand)" ; first  by lia).
iApply (wp_append with "[$]").
{
rewrite take_length.
lia.
}
iIntros "!> (Hf&Hinode&Hdata)".
iDestruct ("Hwand" with "Hdata") as "Hdata".
wp_ret.
(<ssreflect_plugin::ssrtclseq@0> iDestruct (slice_skip_split MAX_WRITE_LEN with "Hdata") as
 "(Hdrop&Hwand)" ; first  by lia).
iApply ("IH" with "Hf Hinode Hdrop [H\206\166 Hwand]").
iIntros "!> (Hf&Hinode&Hdata)".
iDestruct ("Hwand" with "Hdata") as "Hdata".
iApply "H\206\166".
iFrame.
rewrite -app_assoc take_drop //.
Qed.
Definition readMessage_handle f :=
  (fileContents <- Data.newPtr (slice.t byte);
   initData <- Data.newSlice byte 0;
   _ <-
   Loop
     (fun pf =>
      buf <- FS.readAt f pf.(partialFile.off) 512;
      newData <- Data.sliceAppendSlice pf.(partialFile.data) buf;
      if compare_to (slice.length buf) 512 Lt then _ <- Data.writePtr fileContents newData; LoopRet tt
      else Continue
             {|
             partialFile.off := pf.(partialFile.off) + slice.length buf;
             partialFile.data := newData |}) {| partialFile.off := 0; partialFile.data := initData |};
   fileData <- Data.readPtr fileContents;
   fileStr <- Data.bytesToString fileData; _ <- FS.close f; Ret fileStr)%proc.
Lemma readMessage_unfold_open userDir name :
  readMessage userDir name = (let! f <- FS.open userDir name; readMessage_handle f)%proc.
Proof.
auto.
Qed.
Opaque readMessage.
Lemma take_length_lt {A} (l : Datatypes.list A) (n : nat) : length (take n l) < n \226\134\146 take n l = l.
Proof.
(intros Hlen).
(apply take_ge).
rewrite take_length in  {} Hlen.
lia.
Qed.
Lemma wp_readMessage_handle f inode ls q2 :
  {{{ f \226\134\166 (inode, Read) \226\136\151 inode \226\134\166{ q2} ls }}} readMessage_handle f {{{ RET 
  bytes_to_string ls; inode \226\134\166{ q2} ls}}}.
Proof.
rewrite /readMessage_handle.
(<ssreflect_plugin::ssrtclintros@0> generalize 512 =>k).
iIntros ( \206\166 ) "(Hf&Hinode) H\206\166".
wp_bind.
iApply (wp_newAlloc with "[//]").
iIntros ( fileContents ) "!> HfC".
wp_bind.
iApply (@wp_newSlice with "[//]").
iIntros ( fileSlice ) "!> HfS".
(simpl repeat).
replace [] with take 0 ls by auto.
(<ssreflect_plugin::ssrtclintros@0> generalize 0 =>idx).
wp_bind.
iAssert (fileSlice \226\134\166 take idx ls)%I with "[HfS]" as "HfS".
{
(iExists _; eauto).
}
iL\195\182b as "IH" forall ( fileSlice idx ).
wp_loop.
wp_bind.
iApply (wp_readAt with "[$]").
iIntros ( s ) "!> (Hf&Hinode&Hs)".
wp_bind.
iApply (wp_sliceAppendSlice with "[HfS Hs]").
{
iFrame.
}
(simpl).
clear fileSlice.
iIntros ( fileSlice ) "!> (HfS&Hs)".
iDestruct (slice_mapsto_len with "Hs") as % ->.
iClear "Hs".
(destruct lt_dec as [Hlt| Hnlt]).
-
wp_bind.
iApply (wp_writePtr with "[$]").
iIntros "!> HfC".
wp_ret.
iNext.
wp_ret.
wp_bind.
iApply (wp_readPtr with "[$]").
iIntros "!> HfC".
wp_bind.
iApply (wp_bytesToString' with "HfS").
iIntros "!> _".
wp_bind.
iApply (wp_close with "Hf").
iIntros "!> _".
wp_ret.
(apply take_length_lt in Hlt).
rewrite Hlt.
rewrite take_drop.
iApply "H\206\166".
iFrame.
-
wp_ret.
iNext.
iApply ("IH" with "[$] [$] [$] [$]").
rewrite take_take_drop.
(<ssreflect_plugin::ssrtclseq@0> assert (length (take k (drop idx ls)) = k) as -> ; last  by eauto).
(<ssreflect_plugin::ssrtclseq@0> cut (length (take k (drop idx ls)) \226\137\164 k) ; first  by lia).
(eapply firstn_le_length).
Qed.
Lemma createMessages_length msgs : length (createMessages msgs) = length msgs.
Proof.
by rewrite map_length.
Qed.
Lemma nth_error_map {A B : Type} (f : A \226\134\146 B) (n : nat) l (b : B) :
  nth_error (map f l) n = Some b \226\134\146 \226\136\131 a, f a = b \226\136\167 nth_error l n = Some a.
Proof.
revert l.
(<ssreflect_plugin::ssrtclintros@0> induction n =>l //=).
*
(<ssreflect_plugin::ssrtclintros@0> destruct l as [| a l] =>//=).
(intros).
(exists a; split; congruence).
*
(<ssreflect_plugin::ssrtclintros@0> destruct l as [| a l] =>//=).
(intros).
eauto.
Qed.
Lemma take_snoc_S {A} (ls : List.list A) (i : nat) a :
  nth_error ls i = Some a \226\134\146 take (i + 1) ls = take i ls ++ [a].
Proof.
(intros Hin).
revert ls Hin.
(<ssreflect_plugin::ssrtclintros@0> induction i =>ls Hin).
-
rewrite //=.
(destruct ls; inversion Hin; subst).
(simpl).
by rewrite firstn_O.
-
rewrite //=.
(destruct ls; inversion Hin).
(simpl).
f_equal.
eauto.
Qed.
Lemma writeTmp_unfold_writeBuf msg :
  writeTmp msg = (let! (f, name) <- createTmp; _ <- writeBuf f msg; _ <- close f; Ret name)%proc.
Proof.
trivial.
Qed.
Opaque writeTmp.
#[global]Instance ghost_init_status_inhabited : (Inhabited ghost_init_status).
Proof.
econstructor.
exact Uninit.
Qed.
Lemma userRange_in_elim s k : userRange_ok s \226\134\146 k \226\136\136 s \226\134\146 k < NumUsers.
Proof.
(<ssreflect_plugin::ssrtclintros@0> rewrite /userRange_ok =>Hrange ?).
(destruct (lt_dec k NumUsers) as [?| Hn]; auto).
(assert (k \226\137\165 NumUsers) by lia).
(exfalso; eapply Hrange; eauto).
Qed.
Lemma nth_error_snoc {A : Type} (l : List.list A) (a : A) : nth_error (l ++ [a]) (length l) = Some a.
Proof.
(<ssreflect_plugin::ssrtclintros@0> induction l =>//=).
Qed.
Lemma nth_error_snoc_ne {A : Type} (l : List.list A) (a : A) k :
  k \226\137\160 length l \226\134\146 nth_error (l ++ [a]) k = nth_error l k.
Proof.
(intros Hneq).
(destruct (lt_dec k (length l)) as [?| Hgt]).
-
rewrite nth_error_app1 //.
-
(assert (length l < k) by lia).
etransitivity.
*
(eapply nth_error_None).
rewrite app_length //=.
lia.
*
symmetry.
(eapply nth_error_None).
lia.
Qed.
Lemma open_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} :
  {{{ j \226\164\135 K (Call Open) \226\136\151 Registered \226\136\151 ExecInv }}} MailServer.Open {{{ v,  RET v; 
  j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Proof.
iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
iDestruct "Hrest" as ( \206\147 \206\179 ) "(#Hsource&#Hinv)".
rewrite /MailServer.Open.
wp_bind.
iInv "Hinv" as "H".
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iDestruct "Hmsgs" as ( ls ) "(Hglobal&>Hrootdir&Hinit&Hm)".
iDestruct (RootDirInv_range_ok with "Hrootdir") as % Hrange_ok.
iDestruct "Hinit" as ( init_stat ) "Hinit".
iMod (open_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)".
{
solve_ndisj.
}
(destruct init_stat; swap 1 3).
{
iDestruct "Hinit" as ">(?&%)".
exfalso.
congruence.
}
{
iDestruct "Hinit" as ">(?&Hj'&%)".
iMod (open_open_step_inv with "Hj Hj' [$] [$]").
{
solve_ndisj.
}
eauto.
}
iDestruct "Hinit" as ">(Hauth&Hfrag&%&Hghosts)".
(<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  by auto).
iIntros ( locks0 ) "!> Hlocks0".
iExists _.
iFrame.
iExists _.
iFrame.
iMod (ghost_var_update (A:=ghost_init_statusC) with "[$] [$]") as "(Hauth&Hfrag)".
iSplitL "Hauth Hj".
{
iExists (Started_Init _ _).
iFrame.
eauto.
}
iModIntro.
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iApply @wp_newSlice ; first  by auto).
iIntros ( locks ) "!> Hlocks".
wp_bind.
iApply (wp_writePtr with "[$]").
iIntros "!> Hlocks0".
(simpl repeat).
wp_bind.
(remember (@nil LockRef) as lock_list eqn:Heq_lock_list ).
(<ssreflect_plugin::ssrtclseq@0> replace 0 with length lock_list  at 1 ; last  first).
{
rewrite Heq_lock_list //.
}
iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
iAssert
 ([\226\136\151 set] k \226\136\136 dom (gset _) \207\131.(messages), \226\136\131 \206\179uid : gname,
                                           \226\140\156\206\147 !! k = Some \206\179uid\226\140\157
                                           \226\136\151 match nth_error lock_list k with
                                             | Some lk => is_lock boxN lk (InboxLockInv \206\179uid) True
                                             | None => InboxLockInv \206\179uid 0
                                             end)%I with "[Hghosts]" as "Hghosts".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_mono ; last  auto).
iIntros ( k Hin ) "H".
iDestruct "H" as ( \206\179uid ) "(Heq&Hlock)".
(iExists _; iFrame).
rewrite Heq_lock_list.
(destruct k; auto).
}
(assert (Hlen : length lock_list <= NumUsers) by (rewrite Heq_lock_list; cbn[length]; lia)).
clear Heq_lock_list.
iL\195\182b as "IH" forall ( lock_list locks Hlen ).
wp_loop.
(destruct equal).
-
iClear "IH".
wp_ret.
wp_ret.
iIntros "!>".
wp_bind.
iApply (wp_readPtr with "[$]").
iIntros "!> Hlocks0".
iInv "Hinv" as "H".
iDestruct "H" as ( \207\131' ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iDestruct "Hmsgs" as ( ls' ) "(Hglobal&>Hrootdir&Hinit&Hm)".
iDestruct (RootDirInv_range_ok with "Hrootdir") as % Hrange_ok'.
iDestruct "Hinit" as ( init_stat ) "Hinit".
iDestruct "Hinit" as "(>Hauth&Hinit)".
iDestruct (ghost_var_agree (A:=ghost_init_statusC) with "Hauth Hfrag") as % Heq.
subst.
iDestruct "Hinit" as ">(Hj&Hopen')".
iDestruct "Hopen'" as % Hopen'.
rewrite Hopen'.
(simpl GlobalInv).
iDestruct "Hglobal" as ">Hglobal".
iApply (wp_setX with "[$]").
iIntros "!> Hglobal".
rewrite (userRange_ok_eq _ _ Hrange_ok Hrange_ok').
iAssert
 ([\226\136\151 set] k \226\136\136 dom (gset uint64) \207\131'.(messages), \226\136\131 \206\179uid lk,
                                                 \226\140\156\206\147 !! k = Some \206\179uid\226\140\157
                                                 \226\136\151 \226\140\156lock_list !! k = Some lk\226\140\157
                                                   \226\136\151 is_lock boxN lk (InboxLockInv \206\179uid) True)%I with
 "[Hghosts]" as "Hghosts".
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepS_mono ; last  eauto).
iIntros ( k Hin ) "H".
iDestruct "H" as ( \206\179uid Heq ) "H".
iExists \206\179uid.
(<ssreflect_plugin::ssrtclseq@0> destruct nth_error as [lk| ] eqn:Heq_nth_error ; last  first).
{
exfalso.
rewrite nth_error_None in  {} Heq_nth_error *.
(eapply userRange_in_elim in Hin; auto).
rewrite e.
lia.
}
iExists lk.
(iSplitL ""; auto).
(iSplitL ""; auto).
iPureIntro.
rewrite -nth_error_lookup //.
}
iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
{
(intros).
econstructor.
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
(econstructor; eauto).
(do 2 eexists; split).
{
rewrite /reads Hopen'.
eauto.
}
(do 2 econstructor; split; econstructor).
}
{
solve_ndisj.
}
iExists _.
iFrame.
iExists lock_list.
iFrame.
(<ssreflect_plugin::ssrtclseq@0> iSplitR "Hj H\206\166 Hreg" ; last  first).
{
iModIntro.
(iApply "H\206\166"; iFrame).
}
iExists _ , O.
iFrame.
iMod (ghost_var_update (A:=ghost_init_statusC) with "Hauth Hfrag") as "(Hauth&Hfrag)".
iSplitL "Hrootdir".
{
iModIntro.
rewrite /RootDirInv.
(simpl).
(rewrite dom_fmap_L //; eauto).
}
iSplitL "Hauth".
{
iExists Finished_Init.
iFrame.
eauto.
}
iDestruct (big_sepM_dom with "Hghosts") as "Hghosts".
iDestruct (big_sepM_sep with "[Hm Hghosts]") as "Hm".
{
iFrame.
}
iModIntro.
iNext.
rewrite big_sepM_fmap.
(iApply big_sepM_mono; iFrame).
iIntros ( k (mstat, msgs) Hin ) "(H1&H2)".
iDestruct "H1" as ( \206\179' lk' ? ? ) "H".
(simpl).
iDestruct "H2" as ( ? ? _ _ _ ) "((Hinterp&?)&?&Hin)".
iExists _ , _.
rewrite nth_error_lookup.
(iSplitL ""; auto).
(iSplitL ""; auto).
iFrame.
-
wp_bind.
iApply (wp_readPtr with "[$]").
iIntros "!> Hlocks0".
wp_bind.
(assert (length lock_list \226\136\136 dom (gset uint64) \207\131.(messages))).
{
(eapply Hrange_ok).
move : {}Hlen {}n {}.
rewrite /NumUsers.
(inversion 1; eauto).
*
congruence.
*
subst.
lia.
}
iDestruct (big_sepS_delete with "Hghosts") as "(Huid&Hghosts)".
{
eauto.
}
iDestruct "Huid" as ( \206\179uid Heq_\206\179uid ) "Hlockinv".
(assert (nth_error lock_list (length lock_list) = None) as ->).
{
(apply nth_error_None).
trivial.
}
iApply (wp_newLock boxN _ _ (InboxLockInv \206\179uid) True%I with "[Hlockinv]").
{
iFrame.
iSplitL "".
-
iModIntro.
by iIntros ( i ) "$".
-
iModIntro.
by iIntros ( i ) "(?&$)".
}
iIntros ( lk ) "!> #His_lock".
wp_bind.
iApply (wp_sliceAppend with "[$]").
iIntros ( locks' ) "!> Hlocks'".
wp_bind.
iApply (wp_writePtr with "[$]").
iIntros "!> Hlocks0".
wp_ret.
(<ssreflect_plugin::ssrtclseq@0> replace (length lock_list + 1) with length (lock_list ++ [lk]) ; last 
 first).
{
rewrite app_length //=.
}
iApply ("IH" with "[] [$] [$] [$] [$] [$] [Hghosts]").
{
iPureIntro.
rewrite app_length //=.
(inversion Hlen; eauto).
*
congruence.
*
subst.
rewrite /NumUsers.
lia.
}
iApply (big_sepS_delete with "[Hghosts]").
{
eauto.
}
{
iSplitL "".
-
iExists \206\179uid.
(iSplitL ""; auto).
rewrite nth_error_snoc //.
-
iApply (big_sepS_mono with "Hghosts").
iIntros ( k Hin ) "H".
iDestruct "H" as ( \206\179uid' ? ) "H".
iExists \206\179uid'.
(iSplitL ""; auto).
(rewrite nth_error_snoc_ne; eauto).
set_solver.
}
Qed.
Lemma wp_createTmp \206\147 \206\179 :
  {{{ inv execN (\226\136\131 \207\131 : l.(OpState), source_state \207\131 \226\136\151 MsgsInv \206\147 \206\179 \207\131 \226\136\151 HeapInv \207\131 \226\136\151 TmpInv) }}} createTmp {{{ 
  (f : File)name(inode : Inode),  RET (f, name); name \226\134\166 inode \226\136\151 inode \226\134\166 [] \226\136\151 f \226\134\166 (inode, Write)}}}.
Proof.
iIntros ( \206\166 ) "#Hinv H\206\166".
rewrite /createTmp.
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
iIntros ( id ) "!> _".
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  auto).
iIntros ( finalName ) "!> HfinalName".
(simpl repeat).
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  auto).
iIntros ( finalFile ) "!> HfinalFile".
wp_bind.
iL\195\182b as "IH" forall ( id ).
wp_loop.
wp_bind.
rewrite /ExecInv.
(iFastInv "Hinv" "H").
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iDestruct "Htmp" as ( tmps_map ) "(Hspool&Hspool_unlocked&Htmp_auth&Htmps)".
(destruct (decide (gmodel.(@uint64_to_string) id \226\136\136 dom (gset string) tmps_map)) as [Hin| Hfresh]).
*
iApply (wp_create_not_new with "[Hspool]").
{
iFrame.
eauto.
}
iIntros ( ? ) "!> Hspool".
iExists _.
iFrame.
iExists _.
iFrame.
iModIntro.
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
iIntros ( id' ) "!> _".
wp_ret.
iNext.
iApply ("IH" with "H\206\166 [$] [$]").
*
iApply (wp_create_new with "[Hspool]").
{
iFrame.
eauto.
}
iIntros ( inode f ) "!> (Hf&Hinode&Hspool&Hpath)".
iMod (gen_heap_alloc tmps_map (gmodel.(@uint64_to_string) id) inode with "Htmp_auth") as
 "(Htmp_auth&Htmp_frag)".
{
(eapply not_elem_of_dom; eauto).
}
iExists _.
iFrame.
iPoseProof (big_sepM_insert_2 with "[Hpath] Htmps") as "Htmps".
{
iApply "Hpath".
}
iExists _.
iFrame.
rewrite dom_insert_L comm_L.
iFrame.
iModIntro.
wp_bind.
iApply (wp_writePtr with "HfinalName").
iIntros "!> HfinalName".
wp_bind.
iApply (wp_writePtr with "HfinalFile").
iIntros "!> HfinalFile".
wp_ret.
iNext.
wp_ret.
wp_bind.
iApply (wp_readPtr with "HfinalName").
iIntros "!> HfinalName".
wp_bind.
iApply (wp_readPtr with "HfinalFile").
iIntros "!> _".
wp_ret.
(iApply "H\206\166"; by iFrame).
Qed.
Lemma TmpInv_path_acc name inode :
  name \226\134\166 inode
  -\226\136\151 TmpInv -\226\136\151 name \226\134\166 inode \226\136\151 path.mk SpoolDir name \226\134\166 inode \226\136\151 (path.mk SpoolDir name \226\134\166 inode -\226\136\151 TmpInv).
Proof.
iIntros "Hn Htmp".
rewrite /TmpInv.
iDestruct "Htmp" as ( tmp_map ) "(?&?&Htmp_auth&Hpaths)".
iDestruct (@gen_heap_valid with "[$] [$]") as % Hlookup.
(iDestruct (@big_sepM_lookup_acc with "[$]") as "(Hpath&Hpaths)"; eauto).
iFrame.
iIntros.
iExists _.
iFrame.
by iApply "Hpaths".
Qed.
Lemma MailboxStatusInterp_insert uid lk \206\179 mstat mbox name body :
  mbox !! name = None
  \226\134\146 MailboxStatusInterp uid lk \206\179 mstat mbox true
    -\226\136\151 MailboxStatusInterp uid lk \206\179 mstat (<[name:=body]> mbox) true.
Proof.
iIntros ( Hfresh ) "Hinterp".
(destruct mstat; auto).
iDestruct "Hinterp" as "($&HS)".
iDestruct "HS" as ( S ) "(Hauth&%)".
(iExists _; iFrame).
iPureIntro.
(<ssreflect_plugin::ssrtclseq@0> etransitivity ; first  eauto).
(apply insert_subseteq; eauto).
Qed.
Lemma TmpInv_path_delete name inode :
  name \226\134\166 inode
  -\226\136\151 TmpInv
     -\226\136\151 |==> \226\136\131 S : gset string,
               path.mk SpoolDir name \226\134\166 inode
               \226\136\151 SpoolDir \226\134\166 S
                 \226\136\151 SpoolDir \226\134\166 Unlocked \226\136\151 (SpoolDir \226\134\166 (S \226\136\150 {[name]}) -\226\136\151 SpoolDir \226\134\166 Unlocked -\226\136\151 TmpInv).
Proof.
iIntros "Hn Htmp".
rewrite /TmpInv.
iDestruct "Htmp" as ( tmp_map ) "(?&?&Htmp_auth&Hpaths)".
iDestruct (@gen_heap_valid with "[$] [$]") as % Hlookup.
iMod (@gen_heap_dealloc with "[$] [$]") as "Htmp_auth".
(iDestruct (big_sepM_delete with "Hpaths") as "(Hcurr&Hpaths)"; eauto).
iExists _.
iFrame.
iIntros "!> ??".
iExists (map_delete name tmp_map).
rewrite dom_delete_L.
iFrame.
Qed.
Lemma InitInv_open_update \206\147 \206\179 \207\131 \207\131' :
  \207\131.(open) = true \226\134\146 \207\131'.(open) = true \226\134\146 InitInv \206\147 \206\179 \207\131 -\226\136\151 InitInv \206\147 \206\179 \207\131'.
Proof.
iIntros ( Ho1 Ho2 ) "H".
iDestruct "H" as ( v ) "(?&H)".
(destruct v).
-
iDestruct "H" as "(?&%&?)".
congruence.
-
iDestruct "H" as "(?&%)".
congruence.
-
rewrite /InitInv.
iExists Finished_Init.
eauto.
Qed.
Lemma deliver_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid msg :
  {{{ j \226\164\135 K (deliver uid msg) \226\136\151 Registered \226\136\151 ExecInv }}} MailServer.Deliver uid msg {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Proof.
iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
wp_bind.
wp_ret.
rewrite -fupd_wp.
iInv "Hinv" as "H".
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
rewrite /deliver.
iMod
 (deliver_start_step_inv_do j (\206\187 x, K (Bind x (\206\187 x, Call (Deliver_End uid msg))))
 with "Hj Hsource Hstate") as ( s alloc vs s' Heq ) "(Hj&Hstate)".
{
solve_ndisj.
}
iMod (ghost_step_bind_ret with "Hj Hsource") as "Hj".
{
solve_ndisj.
}
(destruct Heq as (Heq1, (Heq2, Heq3))).
iExists _.
iFrame.
iDestruct (big_sepDM_insert_acc (dec:=sigPtr_eq_dec) with "Hheap") as "((Hp&%)&Hheap)".
{
eauto.
}
iAssert
 (\226\150\183 HeapInv (RecordSet.set heap (RecordSet.set Data.allocs (updDyn msg.(slice.ptr) (s', alloc))) \207\131)
  \226\136\151 msg.(slice.ptr) \226\134\166{ - 1} alloc)%I with "[Hp Hheap]" as "($&Hp)".
{
(destruct s; inversion Heq3).
*
(simpl).
iDestruct (Count_Typed_Heap.read_split_join with "Hp") as "(Hp&$)".
(<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  eauto).
(iApply "Hheap"; eauto).
*
(simpl).
iDestruct (Count_Typed_Heap.read_split_join with "Hp") as "(Hp&$)".
(<ssreflect_plugin::ssrtclseq@0> iSplitR "" ; last  eauto).
(iApply "Hheap"; eauto).
}
iModIntro.
iModIntro.
rewrite writeTmp_unfold_writeBuf.
wp_bind.
wp_bind.
iApply (wp_createTmp with "Hinv").
iIntros ( f name inode ) "!> (Hghost&Hinode&Hf)".
wp_bind.
iApply (wp_writeBuf with "[Hf Hinode Hp]").
{
iFrame.
eauto.
}
iIntros "!> (Hf&Hinode&Hp)".
wp_bind.
iApply (wp_close with "[$]").
iIntros "!> _".
wp_ret.
rewrite app_nil_l.
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
iIntros ( id ) "!> _".
wp_bind.
iL\195\182b as "IH" forall ( id ).
wp_loop.
wp_bind.
iInv "Hinv" as "H".
clear \207\131 Heq1 Heq2 Heq3.
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)"; auto).
{
(simpl; auto).
}
{
solve_ndisj.
}
iMod (deliver_end_step_inv j K with "Hj Hsource Hstate") as ( (mstat, mbox) msg_stat' alloc' vs'
 lstatus Heq ) "(Hj&Hstate)".
{
solve_ndisj.
}
(destruct Heq as (He1, (Heq2, (Heq3, Heq4)))).
rewrite /MsgsInv.
rewrite Hopen.
iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
(iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
iDestruct "Huid" as ( lk \206\179 ) "(>%&>%&#Hlock&Hinbox)".
iDestruct "Hinbox" as "(Hmbox&>Hdircontents&Hmsgs)".
iDestruct (TmpInv_path_acc with "[$] [$]") as "(Hghost&Hpath&Htmp)".
(destruct (decide (("msg" ++ uint64_to_string id)%string \226\136\136 dom (gset string) mbox)) as [Hin| Hfresh]).
-
iApply (wp_link_not_new with "[Hpath Hdircontents]").
{
iFrame.
eauto.
}
iIntros "!> (Hpath&Hdircontents)".
iDestruct ("Htmp" with "Hpath") as "Htmp".
iDestruct ("Hm" with "[Hmsgs Hmbox Hdircontents]") as "Hm".
{
iExists _ , _.
(iFrame; eauto).
}
(<ssreflect_plugin::ssrtclseq@0> rewrite insert_id ; last  eauto).
iExists _.
iFrame.
rewrite Hopen.
iExists _.
iFrame.
iModIntro.
wp_bind.
(<ssreflect_plugin::ssrtclseq@0> iApply wp_randomUint64 ; first  auto).
iIntros ( id' ) "!> _".
wp_ret.
iNext.
iApply ("IH" with "[$] [$] [$] [$] [$] [$]").
-
iClear "IH".
iApply (wp_link_new with "[Hpath Hdircontents]").
{
iFrame.
eauto.
}
iIntros "!> (Hpath&Hpathnew&Hdircontents)".
iDestruct ("Htmp" with "Hpath") as "Htmp".
iDestruct (big_sepM_insert_2 with "[Hpathnew Hinode] Hmsgs") as "Hmsgs".
{
(simpl).
iExists _ , _.
iFrame.
replace (0 : Z) with O : Z by auto.
iFrame.
}
iDestruct
 ("Hm" $! (mstat, <[("msg" ++ uint64_to_string id)%string:=vs]> mbox)
 with "[Hmsgs Hmbox Hdircontents]") as "Hm".
{
iExists _ , _.
iFrame.
rewrite dom_insert_L comm_L.
iFrame.
iFrame "Hlock".
(<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  eauto).
(<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  eauto).
(simpl).
(iApply MailboxStatusInterp_insert; eauto).
(eapply not_elem_of_dom; eauto).
}
iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
{
(intros).
econstructor.
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
(econstructor; eauto).
(apply opened_step; auto).
econstructor.
eexists.
split.
-
rewrite /lookup /readSome.
rewrite He1.
eauto.
-
(do 2 eexists; split).
{
(econstructor; eauto).
(eapply not_elem_of_dom; eauto).
}
(do 2 eexists; split).
{
rewrite /readUnlockSlice.
(do 2 eexists; split).
{
rewrite /readSome Heq2 //.
}
(do 2 eexists; split).
{
rewrite /readSome Heq4 //.
}
(do 2 eexists; split).
{
econstructor.
}
{
rewrite /readSome Heq3 //.
}
}
econstructor.
}
{
solve_ndisj.
}
(iDestruct (HeapInv_agree_slice with "[$] [$]") as % (?, ?); eauto).
subst.
iExists _.
iFrame.
iSplitL "Hheap Hm Hglobal Hp Hrootdir Hinit".
{
iExists _.
iFrame.
(simpl open).
rewrite Hopen.
iFrame.
iDestruct (big_sepDM_insert_acc (dec:=sigPtr_eq_dec) with "Hheap") as "((Hlookup&%)&Hclose)".
{
eauto.
}
(iDestruct (InitInv_open_update with "[$]") as "$"; auto).
iSplitL "Hrootdir".
{
iModIntro.
rewrite /RootDirInv.
(simpl).
(rewrite dom_insert_L_in //; eauto).
{
(eapply elem_of_dom).
(eexists; eauto).
}
}
iApply "Hclose".
(iSplitR ""; auto).
iModIntro.
(destruct msg_stat'; inversion Heq4; [  ]).
(simpl).
iDestruct "Hp" as ( ? ? ) "Hp".
iDestruct (Count_Typed_Heap.read_split_join with "[$]") as "H".
(destruct num; inv_step; eauto).
}
wp_ret.
wp_ret.
iModIntro.
iNext.
rewrite /delete.
iInv "Hinv" as "H".
iDestruct "H" as ( ? ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
iMod (TmpInv_path_delete with "[$] Htmp") as ( S ) "(Hpath&Hdir&Hdirlock&Hwand)".
iApply (wp_delete with "[$]").
iIntros "!> (?&?)".
iDestruct ("Hwand" with "[$] [$]") as "Htmp".
iExists _.
iFrame.
iApply "H\206\166".
by iFrame.
Qed.
Lemma delete_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid msg :
  {{{ j \226\164\135 K (Call (Delete uid msg)) \226\136\151 Registered \226\136\151 ExecInv }}} MailServer.Delete uid msg {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Proof.
iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
wp_bind.
wp_ret.
iInv "Hinv" as "H".
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)"; auto).
{
(simpl; auto).
}
{
solve_ndisj.
}
rewrite /MsgsInv ?Hopen.
iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
iDestruct "Hread" as ( lsptr ) "(Hglobal_read&Hlsptr)".
iMod (delete_step_inv with "Hj Hsource Hstate") as ( v body (Heq1, Heq2) ) "(Hj&Hstate)".
{
solve_ndisj.
}
(iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
iDestruct "Huid" as ( lk \206\179 ) "(>%&>%&#Hlock&>Hinbox)".
iDestruct "Hinbox" as "(Hmbox&Hdircontents&Hmsgs)".
iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
{
(intros).
econstructor.
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
(econstructor; eauto).
(eapply opened_step; auto).
econstructor.
eexists.
split.
-
rewrite /lookup /readSome.
rewrite Heq1.
eauto.
-
(simpl).
(do 2 eexists; split).
*
rewrite Heq2 //=.
*
econstructor.
}
{
solve_ndisj.
}
(iDestruct (big_sepM_delete with "Hmsgs") as "(Hcurr_msg&Hmsgs)"; eauto).
iDestruct "Hmbox" as "(Hlocked&Hlockinv&Hdirlock)".
iDestruct "Hcurr_msg" as ( inode q ) "(Hpath&Hinode)".
iApply (wp_delete with "[Hpath Hdircontents Hdirlock]").
{
iFrame.
}
iIntros "!> (Hdircontents&Hdirlock)".
iExists _.
iFrame.
iModIntro.
iSplitR "H\206\166 Hreg Hj".
-
iNext.
iExists _.
iFrame.
(simpl open).
rewrite Hopen.
iFrame.
(iDestruct (InitInv_open_update with "[$]") as "$"; auto).
iSplitL "Hrootdir".
{
rewrite /RootDirInv //=.
rewrite dom_insert_L_in //.
(eapply elem_of_dom).
eauto.
}
iApply "Hm".
iExists _ , _.
iFrame.
(do 2 (iSplitL ""; eauto)).
iFrame "Hlock".
rewrite dom_delete_L.
iFrame.
-
iApply "H\206\166".
iFrame.
Qed.
Lemma lock_refinement {T} j K `{LanguageCtx _ _ T Mail.l K} uid :
  {{{ j \226\164\135 K (Call (Lock uid)) \226\136\151 Registered \226\136\151 ExecInv }}} MailServer.Lock uid {{{ 
  v,  RET v; j \226\164\135 K (Ret v) \226\136\151 Registered}}}.
Proof.
iIntros ( \206\166 ) "(Hj&Hreg&Hrest) H\206\166".
iDestruct "Hrest" as ( \206\147 \206\179init ) "(#Hsource&#Hinv)".
wp_bind.
iInv "Hinv" as "H".
iDestruct "H" as ( \207\131 ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(Hj&Hstate)"; auto).
{
(simpl; auto).
}
{
solve_ndisj.
}
rewrite /MsgsInv ?Hopen.
iDestruct "Hmsgs" as ( ls ) "(>Hglobal&Hrootdir&Hinit&Hm)".
iDestruct (GlobalInv_split with "Hglobal") as "(Hglobal&Hread)".
iDestruct "Hread" as ( lsptr ) "(Hglobal_read&Hlsptr)".
(iApply (wp_getX with "[$]"); iIntros "!> Hglobal_read").
iMod (lock_step_inv with "Hj Hsource Hstate") as ( v Heq ) "(Hj&Hstate)".
{
solve_ndisj.
}
(iDestruct (big_sepM_insert_acc with "Hm") as "(Huid&Hm)"; eauto).
iDestruct "Huid" as ( lk \206\179 ) "(%&%&#Hlock&Hinbox)".
iDestruct "Hinbox" as "(Hmbox&Hdircontents&Hmsgs)".
iMod (ghost_step_call with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
{
(intros).
econstructor.
(<ssreflect_plugin::ssrtclseq@0> eexists; split ; last  by econstructor).
(econstructor; eauto).
(eapply opened_step; auto).
econstructor.
eexists.
split.
-
rewrite /lookup /readSome.
rewrite Heq.
eauto.
-
(simpl).
(do 2 eexists; split; constructor).
}
{
solve_ndisj.
}
iExists _.
iFrame.
iExists _.
(simpl open).
rewrite Hopen.
Unset Silent.
Set Diffs "off".
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhh41zf" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnKcFDd" SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Printing Width 104.
Show.
iFrame.
Unset Silent.
Set Diffs "off".
Set Printing Width 104.
Show.
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hmbox" as "[>Hmbox|Hmbox]" ; last  first).
