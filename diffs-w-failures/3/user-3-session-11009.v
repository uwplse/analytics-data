Time From iris.algebra Require Import auth gmap list.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
Time From Perennial.Examples.MailServer Require Import MailAPI.
Time From Perennial.Goose.Examples Require Import MailServer.
Time From Perennial.Goose.Proof Require Import Interp.
Time Require Import Goose.Proof.Interp.
Time From Perennial Require AtomicPair.Helpers.
Time From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Perennial.Goose Require Import Machine.
Time From Perennial.Goose Require Import GoZeroValues.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Time Existing Instance AtomicPair.Helpers.from_exist_left_sep.
Time Set Default Goal Selector "!".
Time Set Default Proof Using "Type".
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time Import Mail.
Time
Ltac
 non_err' :=
  match goal with
  | |- context [ ?x = Some _ ] =>
        match x with
        | None => fail 1
        | Some _ => fail 1
        | _ => let Heq := fresh "Heq" in
               destruct x as [?| ] eqn:Heq
        end
  | |- lookup _ _ _ _ => unfold lookup
  | |- unwrap _ _ _ => unfold unwrap
  | |- readSome _ _ _ => unfold readSome
  | |- context [ match ?x with
                 | _ => _
                 end ] => match goal with
                          | H:x = _ |- _ => rewrite H
                          end
  end.
Time Ltac non_err := repeat non_err'; trivial.
Time
Ltac
 ghost_err :=
  iMod (ghost_step_err with "[$] [$] [$]") ||
    match goal with
    | |- context [ (_ \226\164\135 ?K _)%I ] => iMod
      (@ghost_step_err _ _ _ _ _ _ _ _ _ _ (\206\187 x, K (Bind x _))
      with "[$] [$] [$]")
    end; eauto.
Time Ltac do_then := repeat (do 2 eexists; split; non_err).
Time
Ltac
 err_start := <ssreflect_plugin::ssrtclseq@0>
 left; right; do_then; destruct (open) ; last  by econstructor.
Time Ltac err_hd := left; non_err; try econstructor.
Time Ltac err_cons := right; do_then.
Time Ltac err0 := err_start; err_hd.
Time Ltac err1 := err_start; err_cons; err_hd.
Time Ltac err2 := err_start; err_cons; err_cons; err_hd.
Time Ltac err3 := err_start; err_cons; err_cons; err_cons; err_hd.
Time Ltac solve_err := ghost_err; (solve [ err0 | err1 | err2 | err3 ]).
Time Section api_lemmas.
Time Context `{@gooseG gmodel gmodelHwf \206\163} `{!@cfgG Mail.Op Mail.l \206\163}.
Time #[global]Instance source_state_inhab : (Inhabited State).
Time Proof.
Time eexists.
Time exact {| heap := \226\136\133; messages := \226\136\133; open := false |}.
Time Qed.
Time #[global]Instance LockRef_inhab : (Inhabited LockRef).
Time Proof.
Time eexists.
Time (apply nullptr).
Time Qed.
Time
Lemma open_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call Open)
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\140\156\207\131.(open) = false\226\140\157 \226\136\151 j \226\164\135 K (Call Open) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (destruct \207\131.(open) as [| ] eqn:Heq).
Time -
Time ghost_err.
Time (intros n).
Time left.
Time right.
Time (do 2 eexists).
Time split.
Time {
Time rewrite /reads.
Time rewrite Heq.
Time econstructor.
Time }
Time (simpl).
Time econstructor.
Time -
Time by iFrame.
Time Qed.
Time
Lemma open_open_step_inv {T} {T'} j j' K K' `{LanguageCtx _ _ T Mail.l K}
  `{LanguageCtx _ _ T' Mail.l K'} (\207\131 : l.(OpState)) 
  E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call Open)
    -\226\136\151 j' \226\164\135 K' (Call Open) -\226\136\151 source_ctx -\226\136\151 source_state \207\131 ={E}=\226\136\151 False.
Time Proof.
Time iIntros ( ? ) "Hj Hj' #Hsrc Hstate".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (open_step_inv with "[$] [$] [$]") as (
 Hopen ) "(?&?)" ; first  auto).
Time iMod (ghost_step_call with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  by econstructor).
Time (econstructor; auto).
Time (do 2 eexists; split).
Time {
Time rewrite /reads Hopen //=.
Time }
Time (simpl).
Time (do 2 eexists).
Time split.
Time *
Time econstructor.
Time *
Time econstructor.
Time }
Time {
Time auto.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (open_step_inv with "[$] [$] [$]") as (
 Hopen' ) "(?&?)" ; first  auto).
Time (simpl in Hopen').
Time congruence.
Time Qed.
Time
Lemma pickup_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (pickup uid)
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\140\156\226\136\131 v, \207\131.(messages) !! uid = Some v\226\140\157
                 \226\136\151 j \226\164\135 K (pickup uid) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time (iIntros; iFrame; eauto).
Time Qed.
Time
Lemma pickup_end_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) msgs E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Pickup_End uid msgs))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v,
                   \226\140\156\207\131.(messages) !! uid = Some (MPickingUp, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Pickup_End uid msgs)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time non_err.
Time -
Time (destruct p as ([], ?); try by iFrame; auto; solve_err).
Time -
Time solve_err.
Time Qed.
Time
Lemma lock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Lock uid))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v,
                   \226\140\156\207\131.(messages) !! uid = Some (MUnlocked, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Lock uid)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time non_err.
Time -
Time (destruct p as ([], ?); try by iFrame; eauto; solve_err).
Time -
Time solve_err.
Time Qed.
Time
Lemma unlock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Unlock uid))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v,
                   \226\140\156\207\131.(messages) !! uid = Some (MLocked, v)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Unlock uid)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time non_err.
Time -
Time (destruct p as ([], ?); try by iFrame; eauto; solve_err).
Time -
Time solve_err.
Time Qed.
Time
Lemma delete_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  uid msg (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Delete uid msg))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v body,
                   \226\140\156\207\131.(messages) !! uid = Some (MLocked, v)
                    \226\136\167 v !! msg = Some body\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Delete uid msg)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time non_err.
Time -
Time (destruct p as ([], msgs); try by iFrame; eauto; try solve_err).
Time iExists _.
Time non_err.
Time *
Time iFrame.
Time eauto.
Time *
Time solve_err.
Time -
Time solve_err.
Time Qed.
Time
Lemma is_opened_step_inv {T} {T2} j K `{LanguageCtx _ T T2 Mail.l K} 
  op (\207\131 : l.(OpState)) E :
  match op with
  | Open => False
  | _ => True
  end
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 K (Call op)
      -\226\136\151 source_ctx
         -\226\136\151 source_state \207\131
            ={E}=\226\136\151 \226\140\156\207\131.(open) = true\226\140\157 \226\136\151 j \226\164\135 K (Call op) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct \207\131.(open) as [| ] eqn:Heq ; last 
 first).
Time -
Time ghost_err.
Time (intros n).
Time left.
Time right.
Time (do 2 eexists).
Time split.
Time {
Time rewrite /reads.
Time rewrite Heq.
Time econstructor.
Time }
Time (simpl).
Time (destruct op; try econstructor).
Time (exfalso; eauto).
Time -
Time by iFrame.
Time Qed.
Time
Lemma is_opened_step_inv' {T} {T1} {T2} j K f `{LanguageCtx _ T1 T2 Mail.l K}
  (op : Op T) (\207\131 : l.(OpState)) E :
  match op with
  | Open => False
  | _ => True
  end
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 K (Bind (Call op) f)
      -\226\136\151 source_ctx
         -\226\136\151 source_state \207\131
            ={E}=\226\136\151 \226\140\156\207\131.(open) = true\226\140\157
                   \226\136\151 j \226\164\135 K (Bind (Call op) f) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct \207\131.(open) as [| ] eqn:Heq ; last 
 first).
Time -
Time ghost_err.
Time (intros n).
Time left.
Time right.
Time (do 2 eexists).
Time split.
Time {
Time rewrite /reads.
Time rewrite Heq.
Time econstructor.
Time }
Time (simpl).
Time (destruct op; try econstructor).
Time (exfalso; eauto).
Time -
Time by iFrame.
Time Qed.
Time
Lemma if_relation_left {A} {B} {T} b (P Q : relation A B T) 
  a o : b = true \226\134\146 P a o \226\134\146 (if b then P else Q) a o.
Time Proof.
Time (intros ->).
Time trivial.
Time Qed.
Time
Lemma opened_step {T} (op : Op T) \207\131 ret :
  \207\131.(open) = true \226\134\146 step_open op \207\131 ret \226\134\146 l.(Proc.step) op \207\131 ret.
Time Proof.
Time (intros Heq Hstep).
Time (destruct ret).
Time -
Time (do 2 eexists).
Time split.
Time {
Time (rewrite /reads; eauto).
Time }
Time rewrite Heq.
Time eauto.
Time -
Time right.
Time (do 2 eexists).
Time split.
Time {
Time (rewrite /reads; eauto).
Time }
Time (rewrite Heq; eauto).
Time Qed.
Time
Lemma deref_step_inv_do {T} {T2} j K `{LanguageCtx _ T T2 Mail.l K} 
  p off (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.PtrDeref p off)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc v,
                   \226\140\156Data.getAlloc p \207\131.(heap) = Some (s, alloc)
                    \226\136\167 lock_available Reader s = Some tt
                      \226\136\167 List.nth_error alloc off = Some v\226\140\157
                   \226\136\151 j \226\164\135 K (Ret v) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time iMod (ghost_step_call _ _ _ _ with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (eapply opened_step; auto).
Time eexists.
Time *
Time (repeat (do 2 eexists; split; non_err)).
Time *
Time (unfold RecordSet.set).
Time (destruct \207\131; eauto).
Time }
Time {
Time eauto.
Time }
Time iExists _.
Time iFrame.
Time (inv_step; eauto).
Time Qed.
Time
Lemma store_start_step_inv_do {T} {T2} j K `{LanguageCtx _ unit T2 Mail.l K}
  p off (x : T) (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.PtrStore p off x Begin)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc,
                   \226\140\156Data.getAlloc p \207\131.(heap) = Some (s, alloc)
                    \226\136\167 lock_acquire Writer s = Some Locked\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs
                               (updDyn p (Locked, alloc))) \207\131).
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
iMod
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; split; non_err)).
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time eauto.
Time (destruct s; simpl in *; try congruence; inv_step; subst; eauto).
Time Qed.
Time
Lemma store_finish_step_inv_do {T} {T2} j K `{LanguageCtx _ unit T2 Mail.l K}
  p off (x : T) xh (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.PtrStore p off x (FinishArgs xh))))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc alloc',
                   \226\140\156Data.getAlloc p \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.list_nth_upd alloc off x = Some alloc'
                      \226\136\167 lock_release Writer s = Some Unlocked\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs
                               (updDyn p (Unlocked, alloc'))) \207\131).
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (non_err; try solve_err).
Time
iMod
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; try split; non_err)).
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time eauto.
Time (destruct s; simpl in *; try congruence).
Time inv_step.
Time eauto.
Time Qed.
Time
Lemma slice_append_step_inv {T} {T2} j K `{LanguageCtx _ _ T2 Mail.l K} 
  p (x : T) (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.SliceAppend p x)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc val,
                   \226\140\156Data.getAlloc p.(slice.ptr) \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.getSliceModel p alloc = Some val
                      \226\136\167 lock_available Writer s = Some tt\226\140\157
                   \226\136\151 j \226\164\135 K (Call (DataOp (Data.SliceAppend p x)))
                     \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time iExists _.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time inv_step.
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma bytes_to_string_step_inv_do {T2} j K `{LanguageCtx _ _ T2 Mail.l K} 
  p (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.BytesToString p)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc val,
                   \226\140\156Data.getAlloc p.(slice.ptr) \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.getSliceModel p alloc = Some val
                      \226\136\167 lock_available Reader s = Some tt\226\140\157
                   \226\136\151 j \226\164\135 K (Ret (bytes_to_string val)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p0 as (s, alloc)).
Time iExists s , alloc.
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time (<ssreflect_plugin::ssrtclseq@0> non_err' ; last  by solve_err).
Time iExists _.
Time inv_step.
Time iMod (ghost_step_call _ _ _ _ with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (eapply opened_step; auto).
Time eexists.
Time *
Time (repeat (do 2 eexists; split; non_err)).
Time {
Time (unfold Data.getAlloc).
Time rewrite Heq //=.
Time }
Time (repeat (do 2 eexists; try split; non_err)).
Time *
Time (unfold RecordSet.set).
Time (destruct \207\131; eauto).
Time }
Time {
Time solve_ndisj.
Time }
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma lock_release_step_inv_do {T} j K `{LanguageCtx _ _ T Mail.l K} 
  lk m (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.LockRelease lk m)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s s',
                   \226\140\156Data.getAlloc lk \207\131.(heap) = Some (s, tt)
                    \226\136\167 lock_release m s = Some s'\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs (updDyn lk (s', ())))
                            \207\131).
Time Proof.
Time iIntros.
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  first).
Time {
Time ghost_err.
Time (intros n).
Time err_start.
Time err_hd.
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time }
Time (destruct p as (?, [])).
Time iExists _.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  first).
Time {
Time ghost_err.
Time (intros n).
Time err_start.
Time err_cons.
Time {
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time }
Time (simpl).
Time rewrite Heq0.
Time econstructor.
Time }
Time iExists _.
Time eauto.
Time
iMod
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; try split; non_err)).
Time {
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time }
Time (simpl).
Time rewrite Heq0.
Time econstructor.
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma lock_acquire_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} 
  lk m (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (DataOp (Data.LockAcquire lk m)))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s,
                   \226\140\156Data.getAlloc lk \207\131.(heap) = Some (s, tt)\226\140\157
                   \226\136\151 j \226\164\135 K (Call (DataOp (Data.LockAcquire lk m)))
                     \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  first).
Time {
Time ghost_err.
Time (intros n).
Time err_start.
Time err_hd.
Time (unfold Data.getAlloc in Heq).
Time by rewrite Heq.
Time }
Time (destruct p as (?, [])).
Time iExists _.
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma deliver_start_step_inv_do {T2} j K `{LanguageCtx _ unit T2 Mail.l K}
  uid msg (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Deliver_Start uid msg))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 s alloc vs s',
                   \226\140\156Data.getAlloc msg.(slice.ptr) \207\131.(heap) = Some (s, alloc)
                    \226\136\167 Data.getSliceModel msg alloc = Some vs
                      \226\136\167 lock_acquire Reader s = Some s'\226\140\157
                   \226\136\151 j \226\164\135 K (Ret tt)
                     \226\136\151 source_state
                         (RecordSet.set heap
                            (RecordSet.set Data.allocs
                               (updDyn msg.(slice.ptr) (s', alloc))) \207\131).
Time Proof.
Time iIntros.
Time (<ssreflect_plugin::ssrtclseq@0> non_err ; last  by solve_err).
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time (destruct p as (s, alloc)).
Time iExists s , alloc.
Time (non_err; try solve_err).
Time
iMod
 (ghost_step_call _ _ _ tt (RecordSet.set heap _ \207\131 : l.(OpState))
 with "[$] [$] [$]") as "(?&?&?)".
Time {
Time (intros n).
Time
(<ssreflect_plugin::ssrtclseq@0> do 2 eexists; split ; last  econstructor).
Time (eexists; auto).
Time (eapply opened_step; auto).
Time (<ssreflect_plugin::ssrtclseq@0> eexists ; last  eauto).
Time (repeat (do 2 eexists; try split; non_err)).
Time }
Time {
Time eauto.
Time }
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma deliver_end_step_inv {T2} j K `{LanguageCtx _ unit T2 Mail.l K} 
  uid msg (\207\131 : l.(OpState)) E :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Call (Deliver_End uid msg))
    -\226\136\151 source_ctx
       -\226\136\151 source_state \207\131
          ={E}=\226\136\151 \226\136\131 v s alloc vs s',
                   \226\140\156\207\131.(messages) !! uid = Some v
                    \226\136\167 Data.getAlloc msg.(slice.ptr) \207\131.(heap) =
                      Some (s, alloc)
                      \226\136\167 Data.getSliceModel msg alloc = Some vs
                        \226\136\167 lock_release Reader s = Some s'\226\140\157
                   \226\136\151 j \226\164\135 K (Call (Deliver_End uid msg)) \226\136\151 source_state \207\131.
Time Proof.
Time iIntros.
Time
(iMod (is_opened_step_inv with "[$] [$] [$]") as ( Hopen ) "(?&?)"; auto).
Time {
Time (simpl; auto).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (\207\131.(messages) !! uid) as [(ms, mbox)| ] eqn:Heq_uid ; last  first).
Time {
Time solve_err.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (Data.getAlloc msg.(slice.ptr) \207\131.(heap))
  as [(s, alloc)| ] eqn:Heq_lookup ; last  first).
Time {
Time ghost_err.
Time (intros n).
Time left.
Time (eapply opened_step; auto).
Time right.
Time (do 2 eexists; split; non_err).
Time right.
Time exists (fresh (dom (gset string) mbox)).
Time (eexists; split).
Time {
Time econstructor.
Time (eapply (not_elem_of_dom (D:=gset string)), is_fresh).
Time }
Time left.
Time rewrite /readUnlockSlice.
Time err_hd.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (lock_release Reader s) as [?| ] eqn:Heq_avail ; last  first).
Time {
Time ghost_err.
Time (intros n).
Time left.
Time (eapply opened_step; auto).
Time right.
Time (do 2 eexists; split; non_err).
Time right.
Time exists (fresh (dom (gset string) mbox)).
Time (eexists; split).
Time {
Time econstructor.
Time (eapply (not_elem_of_dom (D:=gset string)), is_fresh).
Time }
Time left.
Time (err_cons; err_hd).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (Data.getSliceModel msg alloc) as [alloc'| ] eqn:Heq_upd ; last 
 first).
Time {
Time ghost_err.
Time (intros n).
Time left.
Time (eapply opened_step; auto).
Time right.
Time (do 2 eexists; split; non_err).
Time right.
Time exists (fresh (dom (gset string) mbox)).
Time (eexists; split).
Time {
Time econstructor.
Time (eapply (not_elem_of_dom (D:=gset string)), is_fresh).
Time }
Time err3.
Time }
Time iFrame.
Time iExists _ , _ , _ , _ , _.
Time (iPureIntro; eauto).
Time Qed.
Time End api_lemmas.
