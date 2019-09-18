Time From Classes Require Import EqualDec.
Time From iris.algebra Require Import auth gmap frac agree.
Time From Armada Require Export Spec.Proc.
Time From Armada Require Export Spec.LockDefs.
Time From Armada.Goose Require Export GoZeroValues.
Time From Armada.Goose Require Export GoLayer.
Time Export EqualDecNotation.
Time Export ProcNotations.
Time Open Scope proc.
Time Open Scope string.
Time Notation proc := (Proc.proc Op).
Time From iris.algebra Require Export functions csum.
Time From iris.base_logic.lib Require Export invariants.
Time Require CSL.Count_Heap.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.Count_Ghost
  CSL.Count_Typed_Heap CSL.ThreadReg CSL.Count_Double_Heap CSL.Count_GHeap.
Time From iris.proofmode Require Export tactics.
Time From Armada.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Armada.Goose Require Import Machine.
Time From Armada.Goose Require Import GoZeroValues.
Time Set Default Proof Using "Type".
Time Import Data.
Time Import Filesys.FS.
Time Import GoLayer.Go.
Time Notation heap_inG := (@gen_typed_heapG Ptr.ty Ptr ptrRawModel).
Time
Class fsG (m : GoModel) {wf : GoModelWf m} \206\163 :=
 FsG {go_fs_dlocks_inG :> Count_Heap.gen_heapG string unit \206\163;
      go_fs_dirs_inG :> gen_heapG string (gset string) \206\163;
      go_fs_paths_inG :> gen_dirG string string Inode \206\163;
      go_fs_inodes_inG :> gen_heapG Inode (List.list byte) \206\163;
      go_fs_fds_inG :> gen_heapG File (Inode * OpenMode) \206\163;
      go_fs_domalg_inG :> ghost_mapG (discreteC (gset string)) \206\163;
      go_fs_dom_name : gname}.
Time
Canonical Structure sliceLockC {m : GoModel} {wf : GoModelWf m} :=
  leibnizC (option (slice.t LockRef)).
Time
Class globalG (m : GoModel) {wf : GoModelWf m} \206\163 :=
 GlobalG {go_global_alg_inG :> ghost_mapG (discreteC sliceLockC) \206\163;
          go_global_name : gname}.
Time
Class gooseG (m : GoModel) {model_wf : GoModelWf m} \206\163 :=
 GooseG {go_invG : invG \206\163;
         go_heap_inG :> @gen_typed_heapG Ptr.ty Ptr ptrRawModel \206\163 _;
         go_fs_inG :> fsG m \206\163;
         go_global_inG :> globalG m \206\163;
         go_treg_inG :> tregG \206\163}.
Time
Definition heap_interp {\206\163} `{model_wf : GoModelWf} 
  (hM : heap_inG \206\163) : FS.State \226\134\146 iProp \206\163 :=
  \206\187 s : FS.State, gen_typed_heap_ctx s.(heap).(allocs).
Time
Definition fs_interp {\206\163} {model} {hwf} (F : @fsG model hwf \206\163) :
  FS.State \226\134\146 iProp \206\163 :=
  (\206\187 s,
     gen_heap_ctx (hG:=go_fs_dirs_inG)
       (fmap (dom (gset string) (Dom:=gset_dom)) s.(dirents))
     \226\136\151 Count_Heap.gen_heap_ctx (hG:=go_fs_dlocks_inG)
         (\206\187 l, s.(dirlocks) !! l)
       \226\136\151 gen_dir_ctx (hG:=go_fs_paths_inG) s.(dirents)
         \226\136\151 gen_heap_ctx (hG:=go_fs_inodes_inG) s.(inodes)
           \226\136\151 gen_heap_ctx (hG:=go_fs_fds_inG) s.(fds)
             \226\136\151 (\226\136\131 n : nat,
                  ghost_mapsto (A:=discreteC (gset string)) go_fs_dom_name n
                    (dom (gset string) s.(dirents)))
               \226\136\151 \226\140\156dom (gset string) s.(dirents) =
                  dom (gset string) s.(dirlocks)\226\140\157)%I.
Time
Definition global_interp {m} {Hwf} {\206\163} (G : @globalG m Hwf \206\163) :
  Globals.State (slice.t LockRef) \226\134\146 iProp \206\163 :=
  \206\187 s, ghost_mapsto_auth (A:=discreteC (@sliceLockC m Hwf)) go_global_name s.
Time
Definition goose_interp {m} {Hwf} {\206\163} {G : @gooseG m Hwf \206\163} :=
  (\206\187 s : State,
     heap_interp go_heap_inG (fs s)
     \226\136\151 fs_interp go_fs_inG (fs s) \226\136\151 global_interp go_global_inG (maillocks s))%I.
Time
Instance gooseG_irisG  `{gooseG \206\163}: (irisG GoLayer.Op GoLayer.Go.l \206\163) := {
 iris_invG :=go_invG;
 state_interp :=(\206\187 s, thread_count_interp (fst s) \226\136\151 goose_interp (snd s))%I}.
Time
Class GenericMapsTo `{gooseG \206\163} (Addr : Type) (ValTy : Type) :={
 generic_mapsto : Addr -> Z \226\134\146 ValTy -> iProp \206\163}.
Time
Notation "l \226\134\166{ q } v" := (generic_mapsto l q v) (at level 20) : bi_scope.
Time Notation "l \226\134\166 v" := (generic_mapsto l 0 v) (at level 20) : bi_scope.
Time
Definition ptr_mapsto `{gooseG \206\163} {T} (l : ptr T) 
  q (v : Datatypes.list T) : iProp \206\163 :=
  (\226\140\156l \226\137\160 nullptr _\226\140\157 \226\136\151 Count_Typed_Heap.mapsto (hG:=go_heap_inG) l q Unlocked v)%I.
Time
Definition map_mapsto `{gooseG \206\163} {T} (l : Map T) 
  q v : iProp \206\163 :=
  (\226\140\156l \226\137\160 nullptr _\226\140\157 \226\136\151 Count_Typed_Heap.mapsto (hG:=go_heap_inG) l q Unlocked v)%I.
Time
Instance ptr_gen_mapsto  `{gooseG \206\163} T: (GenericMapsTo (ptr T) _) :=
 {| generic_mapsto := ptr_mapsto |}.
Time
Instance map_gen_mapsto  `{gooseG \206\163} T: (GenericMapsTo (Map T) _) :=
 {| generic_mapsto := map_mapsto |}.
Time
Definition slice_mapsto `{gooseG \206\163} {T} (l : slice.t T) 
  q vss : iProp \206\163 :=
  (\226\140\156getSliceModel l (fst vss) = Some (snd vss)\226\140\157 \226\136\151 l.(slice.ptr) \226\134\166{ q} fst vss)%I.
Time
Definition slice_mapsto' `{gooseG \206\163} {T} (l : slice.t T) 
  q (vs : Datatypes.list T) : iProp \206\163 :=
  (\226\136\131 vs0, slice_mapsto l q (vs0, vs))%I.
Time
Instance slice_gen_mapsto  `{gooseG \206\163} T: (GenericMapsTo (slice.t T) _) :=
 {| generic_mapsto := slice_mapsto |}.
Time
Instance slice_gen_mapsto'  `{gooseG \206\163} T: (GenericMapsTo (slice.t T) _) :=
 {| generic_mapsto := slice_mapsto' |}.
Time
Definition dir_mapsto `{gooseG \206\163} (d : string) q (fs : gset string) :
  iProp \206\163 := mapsto (hG:=go_fs_dirs_inG) d q fs.
Time
Definition dirlock_mapsto `{gooseG \206\163} (d : string) 
  q s : iProp \206\163 := Count_Heap.mapsto (hG:=go_fs_dlocks_inG) d q s tt.
Time
Definition path_mapsto `{gooseG \206\163} (p : path.t) q 
  (i : Inode) : iProp \206\163 :=
  Count_Double_Heap.mapsto (hG:=go_fs_paths_inG) (path.dir p) 
    (path.fname p) q i.
Time
Definition inode_mapsto `{gooseG \206\163} (i : Inode) q 
  (bs : List.list byte) : iProp \206\163 := mapsto (hG:=go_fs_inodes_inG) i q bs.
Time
Definition fd_mapsto `{gooseG \206\163} (fd : File) q (v : Inode * OpenMode) :
  iProp \206\163 := mapsto (hG:=go_fs_fds_inG) fd q v.
Time Inductive GLOBAL : Set :=
         global : _.
Time Inductive ROOTDIR : Set :=
         rootdir : _.
Time #[program]
Instance global_gen_mapsto  `{gooseG \206\163}:
 (GenericMapsTo GLOBAL (option (slice.t LockRef))) :=
 {|
 generic_mapsto := \206\187 _ q v,
                     ghost_mapsto (A:=discreteC (@sliceLockC _ _))
                       go_global_name q v |}.
Time #[program]
Instance rootdir_gen_mapsto  `{gooseG \206\163}:
 (GenericMapsTo ROOTDIR (gset string)) :=
 {|
 generic_mapsto := \206\187 _ q v,
                     ghost_mapsto (A:=discreteC (gset string)) go_fs_dom_name
                       q v |}.
Time
Instance dir_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo string (gset string)) :=
 {| generic_mapsto := dir_mapsto |}.
Time
Instance dirlock_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo string LockStatus)
 := {| generic_mapsto := dirlock_mapsto |}.
Time
Instance path_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo path.t _) :=
 {| generic_mapsto := path_mapsto |}.
Time
Instance inode_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo Inode _) :=
 {| generic_mapsto := inode_mapsto |}.
Time
Instance fd_gen_mapsto  `{gooseG \206\163}: (GenericMapsTo File _) :=
 {| generic_mapsto := fd_mapsto |}.
Time
Ltac
 inj_pair2 :=
  repeat
   match goal with
   | H:existT ?x ?o1 = existT ?x ?o2
     |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
   | H:existT ?x _ = existT ?y _ |- _ => inversion H; subst
   end.
Time
Ltac
 trans_elim P :=
  match goal with
  | H1:P = ?y, H2:P = ?z |- _ => rewrite H1 in  {} H2
  end.
Time
Lemma lock_acquire_writer_inv l0 l1 :
  lock_acquire Writer l0 = Some l1 \226\134\146 l0 = Unlocked \226\136\167 l1 = Locked.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> destruct l0 =>//=; inversion 1; auto).
Time Qed.
Time
Lemma lock_available_reader_fail_inv l :
  lock_available Reader l = None \226\134\146 l = Locked.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> destruct l =>//=).
Time Qed.
Time Import SemanticsHelpers.
Time
Lemma zoom_non_err {A} {C} (proj : A \226\134\146 C) (inj : C \226\134\146 A \226\134\146 A) 
  {T} (r : relation C C T) (s : A) :
  \194\172 r (proj s) Err \226\134\146 \194\172 zoom proj inj r s Err.
Time Proof.
Time clear.
Time firstorder.
Time Qed.
Time
Lemma zoom2_non_err {A} {B} {C} (proj : A \226\134\146 B) (proj2 : B \226\134\146 C)
  (inj2 : C \226\134\146 B \226\134\146 B) (inj : B \226\134\146 A \226\134\146 A) {T} (r : relation C C T) 
  (s : A) :
  \194\172 r (proj2 (proj s)) Err \226\134\146 \194\172 zoom proj inj (zoom proj2 inj2 r) s Err.
Time Proof.
Time clear.
Time firstorder.
Time Qed.
Time
Lemma readSome_Err_inv {A T : Type} (f : A \226\134\146 option T) 
  (s : A) : readSome f s Err \226\134\146 f s = None.
Time Proof.
Time rewrite /readSome.
Time (destruct (f s); auto; congruence).
Time Qed.
Time
Lemma readSome_Some_inv {A T : Type} (f : A \226\134\146 option T) 
  (s : A) s' t : readSome f s (Val s' t) \226\134\146 s = s' \226\136\167 f s = Some t.
Time Proof.
Time rewrite /readSome.
Time (destruct (f s); auto; try inversion 1; subst; split; congruence).
Time Qed.
Time
Ltac
 inv_step1 :=
  inj_pair2;
   match goal with
   | H:unit |- _ => destruct H
   | H:l.(Layer.sem).(Proc.step) ?op _ (Val _ _)
     |- _ =>
         let op := eval compute in op in
         match op with
         | FilesysOp _ => destruct H as (?, ?)
         | LockGlobalOp _ => destruct H as (?, ?)
         | DataOp _ => destruct H as ((?, ?), ?)
         end
   | H:(sem Go.l).(Proc.step) ?op _ Err
     |- _ =>
         let op := eval compute in op in
         match op with
         | FilesysOp _ =>
             let Hhd_err := fresh "Hhd_err" in
             let Hhd := fresh "Hhd" in
             let Htl_err := fresh "Htl_err" in
             inversion H as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; clear H
         | LockGlobalOp _ =>
             let Hhd_err := fresh "Hhd_err" in
             let Hhd := fresh "Hhd" in
             let Htl_err := fresh "Htl_err" in
             inversion H as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; clear H
         | DataOp _ => destruct H as ((?, ?), ?)
         end
   | H:FS.step _ _ Err
     |- _ =>
         let Hhd_err := fresh "Hhd_err" in
         let Hhd := fresh "Hhd" in
         let Htl_err := fresh "Htl_err" in
         inversion H as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; clear H
   | H:Globals.step _ _ Err
     |- _ =>
         let Hhd_err := fresh "Hhd_err" in
         let Hhd := fresh "Hhd" in
         let Htl_err := fresh "Htl_err" in
         inversion H as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; clear H
   | H:Data.step _ _ Err
     |- _ =>
         let Hhd_err := fresh "Hhd_err" in
         let Hhd := fresh "Hhd" in
         let Htl_err := fresh "Htl_err" in
         inversion H as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; clear H
   | |- \194\172 Go.step _ _ Err => let Herr := fresh "Herr" in
                             intros Herr
   | |- \194\172 snd_lift _ _ Err =>
         apply snd_lift_non_err; try apply zoom2_non_err;
          try apply zoom_non_err; (let Herr := fresh "Herr" in
                                   intros Herr)
   | H:and_then _ _ _ Err
     |- _ =>
         let Hhd_err := fresh "Hhd_err" in
         let Hhd := fresh "Hhd" in
         let Htl_err := fresh "Htl_err" in
         inversion H as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; clear H
   | H:such_that _ _ _ |- _ => inversion H; subst; clear H
   | H:pure _ _ _ |- _ => inversion H; subst; clear H
   | H:Data.step _ _ (Val _ _)
     |- _ =>
         let Hhd := fresh "Hhd" in
         let Htl := fresh "Htl" in
         destruct H as (?, (?, (Hhd, Htl)))
   | H:FS.step _ _ (Val _ _)
     |- _ =>
         let Hhd := fresh "Hhd" in
         let Htl := fresh "Htl" in
         destruct H as (?, (?, (Hhd, Htl)))
   | H:Globals.step _ _ (Val _ _)
     |- _ =>
         let Hhd := fresh "Hhd" in
         let Htl := fresh "Htl" in
         destruct H as (?, (?, (Hhd, Htl)))
   | H:and_then _ _ _ (Val _ _)
     |- _ =>
         let Hhd := fresh "Hhd" in
         let Htl := fresh "Htl" in
         destruct H as (?, (?, (Hhd, Htl)))
   | H:lookup _ _ _ _ |- _ => unfold lookup in H
   | H:resolvePath _ _ _ _ |- _ => unfold resolvePath in H
   | H:puts _ _ _ |- _ => inversion H; subst; clear H
   | H:fresh_key _ _ _ |- _ => inversion H; subst; clear H
   | H:readSome _ _ Err |- _ => apply readSome_Err_inv in H
   | H:readSome _ _ (Val _ _)
     |- _ => apply readSome_Some_inv in H as (?, ?); subst
   | H:context [ pull_lock _ ] |- _ => unfold pull_lock in H
   | H:context [ getAlloc ?p ?\207\131 ] |- _ => unfold getAlloc in H
   | H:?x = Some ?y, H':?x = _ |- _ => rewrite H in  {} H'
   | H:?\207\1312 = RecordSet.set heap (\206\187 _ : Data.State, ?\207\1312.(heap)) ?\207\131
     |- _ =>
         let Heq := fresh "Heq" in
         let heapName := fresh "heap" in
         remember \207\1312.(heap) as heapName eqn:Heq ; clear Heq; subst
   | H:?\207\1312 = RecordSet.set fs (\206\187 _ : FS.State, ?\207\1312.(fs)) ?\207\131
     |- _ =>
         let Heq := fresh "Heq" in
         let fsName := fresh "fs" in
         remember \207\1312.(fs) as fsName eqn:Heq ; clear Heq; subst
   | H:?\207\1312 = RecordSet.set maillocks (\206\187 _, ?\207\1312.(maillocks)) ?\207\131
     |- _ =>
         let Heq := fresh "Heq" in
         let fsName := fresh "ml" in
         remember \207\1312.(maillocks) as fsName eqn:Heq ; clear Heq; subst
   | H:context [ let '(s, alloc) := ?x in _ ] |- _ => destruct x
   | H:lock_acquire _ Unlocked = Some _ |- _ => inversion H; subst; clear H
   | H:lock_acquire Writer _ = Some _
     |- _ => apply lock_acquire_writer_inv in H as (?, ?)
   | H:lock_available Reader _ = None
     |- _ => apply lock_available_reader_fail_inv in H
   | H:reads _ _ _ |- _ => unfold reads in H
   | H:delAllocs _ _ (Val _ _) |- _ => inversion H; subst; clear H
   | H:updAllocs _ _ _ (Val _ _) |- _ => inversion H; subst; clear H
   | H:allocPtr _ _ _ _ |- _ => unfold allocPtr in H
   | H:Some _ = Some _ |- _ => apply Some_inj in H; subst
   | H:Cinl _ = Cinl _ |- _ => inversion H; clear H; subst
   | H:ReadLocked _ = ReadLocked _ |- _ => inversion H; clear H; subst
   | H:(?a, ?b) = (?c, ?d) |- _ => apply pair_inj in H as (?, ?); subst
   | H:Go.step _ _ Err |- _ => inversion H; clear H; subst
   | H:Go.step _ _ (Val _ _) |- _ => inversion H; clear H; subst
   | H:context [ match ?\207\131.(heap).(allocs).(SemanticsHelpers.dynMap) ?p with
                 | _ => _
                 end ]
     |- _ =>
         let pfresh := fresh "p" in
         destruct (\207\131.(heap).(allocs).(SemanticsHelpers.dynMap) p)
          as [([], pfresh)| ] eqn:Heq\207\131; inversion H; subst;
          try destruct pfresh
   end.
Time Ltac inv_step := repeat inv_step1; inj_pair2.
Time Import Reg_wp.
Time Section lifting.
Time Context `{@gooseG gmodel Hwf \206\163}.
Time
Lemma thread_reg1 :
  \226\136\128 n \207\131, state_interp (n, \207\131) -\226\136\151 thread_count_interp n \226\136\151 goose_interp \207\131.
Time Proof.
Time auto.
Time Qed.
Time
Lemma thread_reg2 :
  \226\136\128 n \207\131, thread_count_interp n \226\136\151 goose_interp \207\131 -\226\136\151 state_interp (n, \207\131).
Time Proof.
Time auto.
Time Qed.
Time
Lemma wp_spawn {T} s E (e : proc _ T) \206\166 :
  \226\150\183 Registered
  -\226\136\151 \226\150\183 (Registered -\226\136\151 WP (let! _ <- e; Unregister)%proc @ s; \226\138\164 {{ _, True }})
     -\226\136\151 \226\150\183 (Registered -\226\136\151 \206\166 tt) -\226\136\151 WP Spawn e @ s; E {{ \206\166 }}.
Time Proof.
Time (eapply wp_spawn; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_unregister s E :
  {{{ \226\150\183 Registered }}} Unregister @ s; E {{{ RET tt; True}}}.
Time Proof.
Time (eapply wp_unregister; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_wait s E : {{{ \226\150\183 Registered }}} Wait @ s; E {{{ RET tt; AllDone}}}.
Time Proof.
Time (eapply wp_wait; eauto using thread_reg1, thread_reg2).
Time Qed.
Time
Lemma wp_setX (l : slice.t LockRef) s E :
  {{{ global \226\134\166 None }}} Globals.setX l @ s; E {{{ RET tt; 
  global \226\134\166 Some l}}}.
Time Proof.
Time iIntros ( \206\166 ) "Hp H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&?&HG)".
Time
iDestruct (ghost_var_agree (A:=discreteC sliceLockC) with "HG Hp") as % Heq.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; try congruence).
Time (inversion Hhd).
Time subst.
Time rewrite Heq in  {} Htl_err.
Time inv_step.
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (inversion Hhd; subst).
Time rewrite Heq in  {} Htl.
Time inv_step.
Time
iMod (ghost_var_update (A:=discreteC sliceLockC) _ (Some l) with "HG Hp") as
 "(HG&HP)".
Time iFrame.
Time by iApply "H\206\166".
Time Qed.
Time
Lemma wp_getX (l : slice.t LockRef) q s E :
  {{{ global \226\134\166{ q} Some l }}} Globals.getX @ s; E {{{ RET l; 
  global \226\134\166{ q} Some l}}}.
Time Proof.
Time iIntros ( \206\166 ) "Hp H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&?&HG)".
Time
iDestruct (ghost_var_agree (A:=discreteC sliceLockC) with "HG Hp") as % Heq.
Time iModIntro.
