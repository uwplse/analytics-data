Time From iris.algebra Require Import auth gmap frac agree.
Time From iris.algebra Require Export functions csum.
Time From iris.base_logic.lib Require Export invariants.
Time Require CSL.Count_Heap.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.Count_Ghost
  CSL.Count_Typed_Heap CSL.ThreadReg CSL.Count_Double_Heap CSL.Count_GHeap.
Time From iris.proofmode Require Export tactics.
Time From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
Time From Perennial.Goose Require Import Machine.
Time From Perennial.Goose Require Import GoZeroValues.
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
      go_fs_domalg_inG :> ghost_mapG (discreteO (gset string)) \206\163;
      go_fs_dom_name : gname}.
Time
Canonical Structure sliceLockC {m : GoModel} {wf : GoModelWf m} :=
  leibnizO (option (slice.t LockRef)).
Time
Class globalG (m : GoModel) {wf : GoModelWf m} \206\163 :=
 GlobalG {go_global_alg_inG :> ghost_mapG (discreteO sliceLockC) \206\163;
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
                  ghost_mapsto (A:=discreteO (gset string)) go_fs_dom_name n
                    (dom (gset string) s.(dirents)))
               \226\136\151 \226\140\156dom (gset string) s.(dirents) =
                  dom (gset string) s.(dirlocks)\226\140\157)%I.
Time
Definition global_interp {m} {Hwf} {\206\163} (G : @globalG m Hwf \206\163) :
  Globals.State (slice.t LockRef) \226\134\146 iProp \206\163 :=
  \206\187 s, ghost_mapsto_auth (A:=discreteO (@sliceLockC m Hwf)) go_global_name s.
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
                     ghost_mapsto (A:=discreteO (@sliceLockC _ _))
                       go_global_name q v |}.
Time #[program]
Instance rootdir_gen_mapsto  `{gooseG \206\163}:
 (GenericMapsTo ROOTDIR (gset string)) :=
 {|
 generic_mapsto := \206\187 _ q v,
                     ghost_mapsto (A:=discreteO (gset string)) go_fs_dom_name
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
iDestruct (ghost_var_agree (A:=discreteO sliceLockC) with "HG Hp") as % Heq.
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
iMod (ghost_var_update (A:=discreteO sliceLockC) _ (Some l) with "HG Hp") as
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
iDestruct (ghost_var_agree (A:=discreteO sliceLockC) with "HG Hp") as % Heq.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; try congruence).
Time rewrite Heq in  {} Herr.
Time (inversion Herr).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time rewrite Heq in  {} H0.
Time rewrite Heq.
Time (inversion H0; subst).
Time iFrame.
Time by iApply "H\206\166".
Time Qed.
Time
Lemma dom_insert_L_in {K} {A} `{Countable K} (m : gmap K A) 
  (i : K) (x : A) :
  i \226\136\136 dom (gset K) m \226\134\146 dom (gset K) (<[i:=x]> m) = dom (gset K) m.
Time Proof.
Time rewrite dom_insert_L.
Time (intros).
Time set_solver.
Time Qed.
Time
Lemma wp_link_new dir1 name1 dir2 name2 (inode : Inode) 
  S s E :
  {{{ path.mk dir1 name1 \226\134\166 inode \226\136\151 dir2 \226\134\166 S \226\136\151 \226\140\156\194\172 name2 \226\136\136 S\226\140\157 }}} 
  link dir1 name1 dir2 name2 @ s; E {{{ RET true; 
  path.mk dir1 name1 \226\134\166 inode
  \226\136\151 path.mk dir2 name2 \226\134\166 inode \226\136\151 dir2 \226\134\166 (S \226\136\170 {[name2]})}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hp&Hd&%) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
Time iDestruct (gen_heap_valid with "Hents Hd") as % Hset.
Time rewrite lookup_fmap in  {} Hset.
Time (eapply fmap_Some_1 in Hset as (?, (?, ?))).
Time subst.
Time iDestruct (gen_dir_valid with "Hpaths Hp") as % H'.
Time (simpl in H').
Time (destruct H' as (\207\131d, (Hd, Hf))).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time inv_step.
Time (simpl in *; subst; try congruence).
Time rewrite Hf in  {} Hhd_err.
Time (inv_step; inversion Hhd_err).
Time rewrite Hf in  {} Hhd0.
Time (inversion Hhd0; subst).
Time (simpl in *; congruence).
Time rewrite Hf in  {} Hhd0.
Time (inversion Hhd0; subst).
Time (simpl in *).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite not_elem_of_dom in  {} H0 *
 =>Hsome).
Time rewrite Hsome in  {} Htl_err.
Time inv_step.
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time rewrite Hf in  {} Hhd0.
Time (inversion Hhd0).
Time subst.
Time (simpl in *).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite not_elem_of_dom in  {} H0 *
 =>Hsome).
Time rewrite Hsome in  {} Htl.
Time inv_step.
Time (do 2 (inv_step; intuition)).
Time
(iMod (gen_dir_alloc2 _ _ dir2 name2 _ with "Hpaths") as "(Hpaths&Hp2)";
  eauto).
Time
iMod
 (gen_heap_update _ dir2 _ (dom (gset string) (<[name2:=_]> x4))
 with "Hents Hd") as "(?&?)".
Time iFrame.
Time rewrite -fmap_insert.
Time iFrame.
Time (simpl).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite ?(dom_insert_L_in _ dir2) ; last 
 first).
Time {
Time (apply elem_of_dom).
Time (eexists; eauto).
Time }
Time iFrame.
Time (iSplitL ""; auto).
Time iApply "H\206\166".
Time iFrame.
Time by rewrite dom_insert_L comm_L.
Time Qed.
Time
Lemma wp_link_not_new dir1 name1 dir2 name2 (inode : Inode) 
  S s E :
  {{{ path.mk dir1 name1 \226\134\166 inode \226\136\151 dir2 \226\134\166 S \226\136\151 \226\140\156name2 \226\136\136 S\226\140\157 }}} 
  link dir1 name1 dir2 name2 @ s; E {{{ RET false; 
  path.mk dir1 name1 \226\134\166 inode \226\136\151 dir2 \226\134\166 S}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hp&Hd&%) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
Time iDestruct (gen_heap_valid with "Hents Hd") as % Hset.
Time rewrite lookup_fmap in  {} Hset.
Time (eapply fmap_Some_1 in Hset as (?, (?, ?))).
Time subst.
Time iDestruct (gen_dir_valid with "Hpaths Hp") as % H'.
Time (simpl in H').
Time (destruct H' as (\207\131d, (Hd, Hf))).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time inv_step.
Time (simpl in *; subst; try congruence).
Time rewrite Hf in  {} Hhd_err.
Time (inv_step; inversion Hhd_err).
Time rewrite Hf in  {} Hhd0.
Time (inversion Hhd0; subst).
Time (simpl in *; congruence).
Time rewrite Hf in  {} Hhd0.
Time (inversion Hhd0; subst).
Time (simpl in *).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite elem_of_dom in  {} H0 * =>Hsome).
Time (destruct Hsome as (?, Hsome)).
Time rewrite Hsome in  {} Htl_err.
Time (inv_step; inversion Hhd_err; congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time rewrite Hf in  {} Hhd0.
Time (inversion Hhd0).
Time subst.
Time (simpl in *).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite elem_of_dom in  {} H0 * =>Hsome).
Time (destruct Hsome as (?, Hsome)).
Time rewrite Hsome in  {} Htl.
Time inv_step.
Time iFrame.
Time (iSplitL ""; auto).
Time iApply "H\206\166".
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma createSlice_non_err V (data : List.list V) s : \194\172 createSlice data s Err.
Time Proof.
Time (inversion 1 as [Hhd_err| (?, (?, (Hhd, Htl_err)))]; inv_step).
Time Qed.
Time
Lemma lock_available_reader_succ l :
  l \226\137\160 Locked \226\134\146 lock_available Reader l = Some tt.
Time Proof.
Time (destruct l; eauto; try congruence).
Time Qed.
Time
Lemma wp_readAt fh (inode : Inode) (bs : Datatypes.list byte) 
  off len q1 q2 s E :
  {{{ fh \226\134\166{ q1} (inode, Read) \226\136\151 inode \226\134\166{ q2} bs }}} 
  readAt fh off len @ s; E {{{ (s : slice.t byte), RET s; 
  fh \226\134\166{ q1} (inode, Read)
  \226\136\151 inode \226\134\166{ q2} bs
    \226\136\151 s
      \226\134\166 (list.take len (list.drop off bs), list.take len (list.drop off bs))}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hfh&Hi) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&HFS&?)".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
Time iDestruct (gen_heap_valid with "Hfds Hfh") as % Hfd.
Time iDestruct (gen_heap_valid with "Hinodes Hi") as % Hi.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; try unfold readFd in Hhd_err; inv_step).
Time *
Time (simpl in *; subst; try congruence).
Time *
Time (simpl in *; inv_step).
Time congruence.
Time *
Time (eapply createSlice_non_err in Htl_err; eauto).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (red in Htl).
Time (do 2 (inv_step; intuition)).
Time (unfold readFd in Hhd).
Time inv_step.
Time (<ssreflect_plugin::ssrtclseq@0> destruct equal ; last  by congruence).
Time inv_step.
Time (iMod (gen_typed_heap_alloc with "H\207\131") as "(H\207\131&Hp)"; eauto).
Time iFrame.
Time (iSplitL ""; auto).
Time iApply "H\206\166".
Time iFrame.
Time iModIntro.
Time iFrame.
Time iPureIntro.
Time rewrite /getSliceModel sublist_lookup_all //= app_length //=.
Time Qed.
Time
Lemma wp_append fh (inode : Inode) (p' : slice.t byte)
  (bs bs1 bs2 : Datatypes.list byte) q1 q2 s E :
  length bs2 <= MAX_WRITE_LEN
  \226\134\146 {{{ fh \226\134\166{ q1} (inode, Write) \226\136\151 inode \226\134\166 bs \226\136\151 p' \226\134\166{ q2} (bs1, bs2) }}} 
  append fh p' @ s; E {{{ RET tt; fh \226\134\166{ q1} (inode, Write)
                                  \226\136\151 inode \226\134\166 (bs ++ bs2)
                                    \226\136\151 p' \226\134\166{ q2} (bs1, bs2)}}}.
Time Proof.
Time iIntros ( Hlen \206\166 ) "(Hfh&Hi&Hp) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&HFS&?)".
Time iDestruct "Hp" as ( Heq Hnonnull ) "Hp".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
Time iDestruct (gen_heap_valid with "Hfds Hfh") as % Hfd.
Time iDestruct (gen_heap_valid with "Hinodes Hi") as % Hi.
Time
iDestruct (gen_typed_heap_valid (Ptr.Heap byte) with "H\207\131 Hp") as % [s' [? ?]].
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time
(inv_step; try unfold readFd in *; inv_step; try congruence; inv_step;
  try unfold readFd in *; inv_step; try congruence;
  <ssreflect_plugin::ssrtclseq@0> destruct equal ; last  by congruence;
  inv_step; try congruence).
Time *
Time (unfold unwrap in Hhd_err).
Time rewrite Heq in  {} Hhd_err.
Time inv_step.
Time *
Time (unfold unwrap in Hhd0).
Time (rewrite Heq in  {} Hhd0; inv_step).
Time (destruct le_dec; [ inversion Hhd_err | eauto ]).
Time *
Time (unfold unwrap in Hhd_err).
Time (destruct l0; try congruence; inv_step).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (unfold readFd in *).
Time (unfold unwrap in *).
Time inv_step.
Time (<ssreflect_plugin::ssrtclseq@0> destruct equal ; last  by congruence).
Time inv_step.
Time (<ssreflect_plugin::ssrtclseq@0> destruct (le_dec) ; last  by eauto).
Time (inversion Hhd1; subst).
Time rewrite lock_available_reader_succ // in  {} Hhd2.
Time rewrite Heq in  {} Hhd0.
Time inv_step.
Time iMod (gen_heap_update with "Hinodes Hi") as "($&?)".
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; first  by auto).
Time iApply "H\206\166".
Time iFrame.
Time iModIntro.
Time by iFrame.
Time Qed.
Time
Lemma wp_create_new dir fname S s E :
  {{{ dir \226\134\166 S \226\136\151 \226\140\156\194\172 fname \226\136\136 S\226\140\157 }}} create dir fname @ s; E {{{ 
  (i : Inode)(f : File), RET (f, true); f \226\134\166 (i, Write)
                                        \226\136\151 i \226\134\166 []
                                          \226\136\151 dir \226\134\166 (S \226\136\170 {[fname]})
                                            \226\136\151 {|
                                              path.dir := dir;
                                              path.fname := fname |} \226\134\166 i}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hd&%) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?&%)".
Time iDestruct (gen_heap_valid with "Hents Hd") as % H'.
Time rewrite lookup_fmap in  {} H'.
Time (eapply fmap_Some_1 in H' as (?, (?, ?))).
Time subst.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time inv_step.
Time (simpl in *; subst; try congruence).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite not_elem_of_dom in  {} H0 *
 =>Hsome).
Time rewrite Hsome in  {} Htl_err.
Time (inv_step; inversion Hhd_err).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite not_elem_of_dom in  {} H0 *
 =>Hsome).
Time rewrite Hsome in  {} Htl.
Time (do 2 (inv_step; intuition)).
Time
(iMod (gen_dir_alloc2 _ _ dir fname x with "Hpaths") as "(Hpaths&Hp)"; eauto).
Time
iMod
 (gen_heap_update _ dir _ (dom (gset string) (<[fname:=x]> x0))
 with "Hents Hd") as "(?&?)".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (gen_heap_alloc with "Hinodes") as
 "(?&?)" ; first  eauto).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (gen_heap_alloc with "Hfds") as "(?&?)"
 ; first  eauto).
Time iFrame.
Time rewrite -fmap_insert.
Time iFrame.
Time (simpl).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite ?(dom_insert_L_in _ dir) ; last 
 first).
Time {
Time (apply elem_of_dom).
Time (eexists; eauto).
Time }
Time iFrame.
Time (iSplitL ""; auto).
Time iApply "H\206\166".
Time iFrame.
Time by rewrite dom_insert_L comm_L.
Time Qed.
Time
Lemma identity_val_inv {A B : Type} (x x' : A) (b : B) :
  identity x (Val x' b) \226\134\146 x = x'.
Time Proof.
Time (inversion 1; subst).
Time congruence.
Time Qed.
Time
Lemma wp_create_not_new dir fname S s E :
  {{{ dir \226\134\166 S \226\136\151 \226\140\156fname \226\136\136 S\226\140\157 }}} create dir fname @ s; E {{{ 
  (f : File), RET (f, false); dir \226\134\166 S}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hd&%) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?)".
Time iDestruct (gen_heap_valid with "Hents Hd") as % H'.
Time rewrite lookup_fmap in  {} H'.
Time (eapply fmap_Some_1 in H' as (?, (?, ?))).
Time subst.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time inv_step.
Time (simpl in *; subst; try congruence).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite elem_of_dom in  {} H0 * =>Hsome).
Time (destruct Hsome as (?, Hsome)).
Time rewrite Hsome in  {} Htl_err.
Time (inv_step; inversion Hhd_err; congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite elem_of_dom in  {} H0 * =>Hsome).
Time (destruct Hsome as (?, Hsome)).
Time rewrite Hsome in  {} Htl.
Time (do 2 (inv_step; intuition)).
Time (apply identity_val_inv in Hhd; subst).
Time iFrame.
Time by iApply "H\206\166".
Time Qed.
Time
Lemma wp_open dir fname inode q s E :
  {{{ path.mk dir fname \226\134\166{ q} inode }}} open dir fname @ s; E {{{ 
  (f : File), RET f; path.mk dir fname \226\134\166{ q} inode \226\136\151 f \226\134\166 (inode, Read)}}}.
Time Proof.
Time iIntros ( \206\166 ) "Hd H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?)".
Time iDestruct (gen_dir_valid with "Hpaths Hd") as % H'.
Time (simpl in H').
Time (destruct H' as (\207\131d, (Hd, Hf))).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (gen_heap_alloc with "Hfds") as
 "[Hfds Hp]" ; first  by eauto).
Time iFrame.
Time iApply "H\206\166".
Time by iFrame.
Time Qed.
Time
Lemma wp_close fh m s E : {{{ fh \226\134\166 m }}} close fh @ s; E {{{ RET tt; True}}}.
Time Proof.
Time iIntros ( \206\166 ) "Hd H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&?&Hpaths&Hinodes&Hfds&?)".
Time iDestruct (gen_heap_valid with "Hfds Hd") as % H'.
Time (simpl in H').
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iMod (gen_heap_dealloc with "Hfds Hd") as "Hfds".
Time iFrame.
Time iApply "H\206\166".
Time by iFrame.
Time Qed.
Time
Lemma wp_list_start dir q s E :
  {{{ dir \226\134\166{ q} Unlocked }}} list_start dir @ s; E {{{ RET tt; 
  dir \226\134\166{ q} ReadLocked O}}}.
Time Proof.
Time iIntros ( \206\166 ) "Hdl H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&Hdlocks&Hpaths&Hinodes&Hfds&?&Hdom)".
Time iDestruct "Hdom" as % Hdom.
Time
iDestruct (Count_Heap.gen_heap_valid with "Hdlocks Hdl") as %
 [s' [Hlookup Hnl]].
Time (simpl in Hlookup).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time (destruct l0; try congruence; inversion Hhd_err).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time
iMod (Count_Heap.gen_heap_readlock with "Hdlocks Hdl") as ( s'' Heq )
 "(Hdlocks&Hdl)".
Time inv_step.
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "H\206\166 Hdl" ; last  first).
Time {
Time iApply "H\206\166".
Time by iFrame.
Time }
Time (destruct s''; try congruence; inversion Hhd; subst).
Time *
Time iFrame.
Time (simpl).
Time iSplitL.
Time {
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply Count_Heap.gen_heap_ctx_proper ;
 last  auto).
Time (intros k).
Time (simpl).
Time rewrite {+1}/insert /Count_Heap.partial_fn_insert //=.
Time (destruct equal; eauto).
Time subst.
Time by rewrite lookup_insert.
Time rewrite lookup_insert_ne //=.
Time }
Time iPureIntro.
Time rewrite dom_insert_L.
Time rewrite Hdom.
Time (assert (dir \226\136\136 dom (gset string) \207\131.(fs).(dirlocks))).
Time {
Time (apply elem_of_dom).
Time (eexists; eauto).
Time }
Time set_solver.
Time *
Time iFrame.
Time (simpl).
Time iSplitL.
Time {
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply Count_Heap.gen_heap_ctx_proper ;
 last  auto).
Time (intros k).
Time (simpl).
Time rewrite {+1}/insert /Count_Heap.partial_fn_insert //=.
Time (destruct equal; eauto).
Time subst.
Time by rewrite lookup_insert.
Time rewrite lookup_insert_ne //=.
Time }
Time iPureIntro.
Time rewrite dom_insert_L.
Time rewrite Hdom.
Time (assert (dir \226\136\136 dom (gset string) \207\131.(fs).(dirlocks))).
Time {
Time (apply elem_of_dom).
Time (eexists; eauto).
Time }
Time set_solver.
Time Qed.
Time
Lemma map_to_list_dom_perm {K} {V} `{Countable K} 
  (m : gmap K V) : map fst (map_to_list m) \226\137\161\226\130\154 elements (dom (gset K) m).
Time Proof.
Time (apply NoDup_Permutation).
Time -
Time (apply NoDup_fst_map_to_list).
Time -
Time (apply NoDup_elements).
Time -
Time (intros k).
Time rewrite elem_of_elements elem_of_dom.
Time split.
Time *
Time (intros ((?, v), (?, ?%elem_of_map_to_list))%elem_of_list_fmap_2).
Time (simpl in *; subst; eexists; eauto).
Time *
Time (intros (v, ?)).
Time (apply elem_of_list_fmap).
Time (exists (k, v); split; eauto).
Time rewrite elem_of_map_to_list.
Time eauto.
Time Qed.
Time
Lemma wp_delete dir fname (S : gset string) (inode : Inode) 
  s E :
  {{{ dir \226\134\166 S \226\136\151 dir \226\134\166 Unlocked \226\136\151 path.mk dir fname \226\134\166 inode }}} 
  delete dir fname @ s; E {{{ RET tt; dir \226\134\166 (S \226\136\150 {[fname]}) \226\136\151 dir \226\134\166 Unlocked}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hd&Hdl&Hp) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&?&HFS&?)".
Time iDestruct "HFS" as "(Hents&Hdlocks&Hpaths&Hinodes&Hfds&?&Hdom)".
Time iDestruct "Hdom" as % Hdom.
Time iDestruct (Count_Heap.gen_heap_valid1 with "Hdlocks Hdl") as % ?.
Time iDestruct (gen_dir_valid with "Hpaths Hp") as % H'.
Time (simpl in H').
Time (destruct H' as (\207\131d, (Hd, Hf))).
Time iDestruct (gen_heap_valid with "Hents Hd") as % H'.
Time rewrite lookup_fmap in  {} H'.
Time (eapply fmap_Some_1 in H' as (?, (?, ?))).
Time subst.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time inv_step.
Time rewrite Hf in  {} Hhd_err.
Time (inversion Hhd_err).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (unfold unwrap in *).
Time (simpl in *).
Time inv_step.
Time rewrite Hf in  {} Hhd1.
Time inv_step.
Time iFrame.
Time (simpl).
Time (iMod (gen_dir_dealloc with "Hpaths Hp") as "Hpaths"; eauto).
Time (simpl).
Time iFrame.
Time
iMod
 (gen_heap_update _ dir _ (dom (gset string) (map_delete fname _))
 with "Hents Hd") as "(?&?)".
Time rewrite fmap_insert.
Time iFrame.
Time (simpl).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite ?(dom_insert_L_in _ dir) ; last 
 first).
Time {
Time (apply elem_of_dom).
Time (eexists; eauto).
Time }
Time iFrame.
Time (iSplitL ""; auto).
Time iApply "H\206\166".
Time iFrame.
Time rewrite dom_delete_L.
Time by iFrame.
Time Qed.
Time
Lemma wp_list_finish dir (S : gset string) s q1 q2 
  E :
  {{{ dir \226\134\166{ q1} S \226\136\151 dir \226\134\166{ q2} ReadLocked O }}} list_finish dir @ s; E {{{ 
  (s : slice.t string)(l : Datatypes.list string), RET s; 
  \226\140\156Permutation.Permutation l (elements S)\226\140\157
  \226\136\151 s \226\134\166 (l, l) \226\136\151 dir \226\134\166{ q1} S \226\136\151 dir \226\134\166{ q2} Unlocked}}}.
Time Proof.
Time iIntros ( \206\166 ) "(Hd&Hdl) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&HFS&?)".
Time iDestruct "HFS" as "(Hents&Hdlocks&Hpaths&Hinodes&Hfds&?&Hdom)".
Time iDestruct "Hdom" as % Hdom.
Time iDestruct (Count_GHeap.gen_heap_valid with "Hents Hd") as % Hlookup1.
Time rewrite lookup_fmap in  {} Hlookup1.
Time (eapply fmap_Some_1 in Hlookup1 as (?, (?, ?))).
Time subst.
Time
iDestruct (Count_Heap.gen_heap_valid2 with "Hdlocks Hdl") as %
 [s' [Hlookup2 Hl]].
Time (apply Count_Heap.Cinl_included_nat' in Hl as (m, (?, ?)); subst).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; subst; try congruence).
Time -
Time (destruct l0; simpl in *; try congruence).
Time (destruct num; try inversion Hhd_err).
Time (inv_step; lia).
Time -
Time (eapply createSlice_non_err; eauto).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time
iMod (Count_Heap.gen_heap_readunlock with "Hdlocks Hdl") as ( s'' Heq )
 "(Hdlocks&Hdl)".
Time (inversion Hstep; subst).
Time inv_step.
Time (unfold createSlice in Htl).
Time (do 2 (inv_step; intuition)).
Time
(match goal with
 | H:unwrap _ ?x1 (Val ?x2 ?res) |- _ => assert (x1 = x2)
 end).
Time {
Time (destruct s''; inversion Hhd0; subst; eauto).
Time }
Time subst.
Time (iMod (gen_typed_heap_alloc with "H\207\131") as "(H\207\131&Hp)"; eauto).
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR "H\206\166 Hd Hdl Hp" ; last  first).
Time {
Time iApply "H\206\166".
Time iFrame.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitR ; last  first).
Time iModIntro.
Time iFrame.
Time iPureIntro.
Time rewrite /getSliceModel sublist_lookup_all //= app_length //=.
Time iPureIntro.
Time rewrite -map_to_list_dom_perm //.
Time }
Time (simpl).
Time iFrame.
Time iSplitL.
Time {
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclseq@0> iApply Count_Heap.gen_heap_ctx_proper ;
 last  auto).
Time (intros k).
Time (simpl).
Time rewrite {+1}/insert /Count_Heap.partial_fn_insert //=.
Time
(destruct s''; inversion Hhd0; inv_step; destruct equal; eauto; subst;
  rewrite ?lookup_insert ?lookup_insert_ne //=).
Time }
Time iPureIntro.
Time rewrite dom_insert_L.
Time rewrite Hdom.
Time (assert (dir \226\136\136 dom (gset string) \207\131.(fs).(dirlocks))).
Time {
Time (apply elem_of_dom).
Time (eexists; eauto).
Time }
Time set_solver.
Time Qed.
Time
Lemma wp_newAlloc {T} s E (v : T) len :
  {{{ True }}} newAlloc v len @ s; E {{{ (p : ptr T), RET p; 
  p \226\134\166 List.repeat v len}}}.
Time Proof.
Time iIntros ( \206\166 ) "_ H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time inv_step.
Time (simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (destruct H0 as ((?, ?), ?)).
Time (do 2 (inv_step; intuition)).
Time (iMod (gen_typed_heap_alloc with "H\207\131") as "(H\207\131&Hp)"; eauto).
Time iFrame.
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_ptrStore_start {T} s E (p : ptr T) off l 
  v :
  {{{ \226\150\183 Count_Typed_Heap.mapsto p 0 Unlocked l }}} 
  Call (InjectOp.inject (PtrStore p off v SemanticsHelpers.Begin)) @ s; E {{{ RET tt; 
  Count_Typed_Heap.mapsto p 0 Locked l}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct (gen_typed_heap_valid1 (Ptr.Heap T) with "H\207\131 Hi") as % ?.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; simpl in *; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iMod (@gen_typed_heap_update with "H\207\131 Hi") as "[$ Hi]".
Time iFrame.
Time (iApply "H\206\166"; eauto).
Time Qed.
Time
Lemma ptr_mapsto_non_null {T} (p : ptr T) (v : List.list T) :
  (p \226\134\166 v -\226\136\151 \226\140\156p \226\137\160 nullptr _\226\140\157)%I.
Time Proof.
Time (iIntros "(?&?)"; eauto).
Time Qed.
Time
Lemma slice_mapsto_non_null {T} (p : slice.t T) (v : List.list T) :
  (p \226\134\166 v -\226\136\151 \226\140\156p.(slice.ptr) \226\137\160 nullptr _\226\140\157)%I.
Time Proof.
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&(?&?))".
Time eauto.
Time Qed.
Time
Lemma wp_ptrStore_finish {T} s E (p : ptr T) off l 
  l' v :
  list_nth_upd l off v = Some l'
  \226\134\146 {{{ \226\150\183 Count_Typed_Heap.mapsto p 0 Locked l }}} 
  Call (InjectOp.inject (PtrStore p off v (FinishArgs ()))) @ s; E {{{ RET tt; 
  Count_Typed_Heap.mapsto p 0 Unlocked l'}}}.
Time Proof.
Time (intros Hupd).
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct (gen_typed_heap_valid1 (Ptr.Heap T) with "H\207\131 Hi") as % ?.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (subst; simpl in *).
Time iMod (gen_typed_heap_update (Ptr.Heap T) with "H\207\131 Hi") as "[$ Hi]".
Time iFrame.
Time iApply "H\206\166".
Time (inv_step; by iFrame).
Time Qed.
Time
Lemma wp_ptrStore {T} s E (p : ptr T) off l l' v :
  list_nth_upd l off v = Some l'
  \226\134\146 {{{ \226\150\183 p \226\134\166 l }}} ptrStore p off v @ s; E {{{ RET tt; 
  p \226\134\166 l'}}}.
Time Proof.
Time (intros Hupd).
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time rewrite /ptrStore /nonAtomicWriteOp.
Time iDestruct (ptr_mapsto_non_null with "Hi") as % Hnonull.
Time wp_bind.
Time iDestruct "Hi" as ( ? ) "Hi".
Time (iApply (wp_ptrStore_start with "Hi"); eauto).
Time iNext.
Time iIntros "Hi".
Time (iApply (wp_ptrStore_finish with "Hi"); eauto).
Time iIntros "!> ?".
Time iApply "H\206\166".
Time by iFrame.
Time Qed.
Time
Lemma wp_writePtr {T} s E (p : ptr T) v' l v :
  {{{ \226\150\183 p \226\134\166 (v' :: l) }}} writePtr p v @ s; E {{{ RET tt; 
  p \226\134\166 (v :: l)}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time (iApply (wp_ptrStore with "Hi"); eauto).
Time Qed.
Time
Lemma wp_ptrDeref' {T} s E (p : ptr T) q status off 
  l v :
  lock_available Reader status <> None
  \226\134\146 List.nth_error l off = Some v
    \226\134\146 {{{ \226\150\183 Count_Typed_Heap.mapsto p q status l }}} 
    ptrDeref p off @ s; E {{{ RET v; Count_Typed_Heap.mapsto p q status l}}}.
Time Proof.
Time (intros Hstat Hupd).
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time rewrite /ptrDeref.
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 (Ptr.Heap T) with "H\207\131 Hi") as %
 [s' [? Hrlock]].
Time (assert (\226\136\131 m, Count_Heap.to_lock s' = Cinl m) as (m, ?)).
Time {
Time
(destruct status; simpl in Hstat; try congruence;
  apply Count_Heap.Cinl_included_nat' in Hrlock as (m, (?, ?)); subst; eauto).
Time }
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iFrame.
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_ptrDeref {T} s E (p : ptr T) q off l v :
  List.nth_error l off = Some v
  \226\134\146 {{{ \226\150\183 p \226\134\166{ q} l }}} ptrDeref p off @ s; E {{{ RET v; 
  p \226\134\166{ q} l}}}.
Time Proof.
Time (intros Hupd).
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iDestruct "Hi" as ( ? ) "Hi".
Time (iApply (wp_ptrDeref' with "Hi"); eauto).
Time iIntros "!> Hp".
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_readPtr {T} s E (p : ptr T) q v l :
  {{{ \226\150\183 p \226\134\166{ q} (v :: l) }}} readPtr p @ s; E {{{ RET v; 
  p \226\134\166{ q} (v :: l)}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time (iApply (wp_ptrDeref with "Hi"); eauto).
Time Qed.
Time
Lemma nth_error_lookup {A : Type} (l : Datatypes.list A) 
  (i : nat) : nth_error l i = l !! i.
Time Proof.
Time
(revert l; <ssreflect_plugin::ssrtclintros@0> induction i =>l; destruct l;
  eauto).
Time Qed.
Time
Lemma wp_newSlice {T} {GoZero : HasGoZero T} s E len :
  {{{ True }}} newSlice T len @ s; E {{{ s, RET s; 
  s \226\134\166 (List.repeat (zeroValue T) len, List.repeat (zeroValue T) len)}}}.
Time Proof.
Time iIntros ( \206\166 ) "_ H\206\166".
Time wp_bind.
Time (<ssreflect_plugin::ssrtclseq@0> iApply wp_newAlloc ; first  auto).
Time iIntros ( p ) "!> Hpt".
Time wp_ret.
Time (iApply "H\206\166"; iFrame).
Time rewrite /getSliceModel sublist_lookup_all //= repeat_length //.
Time Qed.
Time
Lemma wp_sliceRead {T} s E (p : slice.t T) q off l1 
  l2 v :
  List.nth_error l2 off = Some v
  \226\134\146 {{{ \226\150\183 p \226\134\166{ q} (l1, l2) }}} sliceRead p off @ s; E {{{ RET v; 
  p \226\134\166{ q} (l1, l2)}}}.
Time Proof.
Time iIntros ( Hnth \206\166 ) ">Hp H\206\166".
Time iDestruct "Hp" as ( Heq ) "Hp".
Time rewrite /getSliceModel /sublist_lookup /mguard /option_guard in  {} Heq.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide_rel) ; last  by congruence).
Time (inversion Heq).
Time subst.
Time iApply (wp_ptrDeref with "Hp").
Time rewrite nth_error_lookup in  {} Hnth *.
Time
(assert
  (Hlen : off < length (take p.(slice.length) (drop p.(slice.offset) l1)))).
Time {
Time (eapply lookup_lt_is_Some_1).
Time eauto.
Time }
Time rewrite lookup_take in  {} Hnth.
Time rewrite lookup_drop in  {} Hnth.
Time rewrite nth_error_lookup.
Time eauto.
Time {
Time rewrite take_length in  {} Hlen.
Time lia.
Time }
Time iIntros "!> ?".
Time iApply "H\206\166".
Time iFrame.
Time rewrite /getSliceModel /sublist_lookup /mguard /option_guard.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide_rel) ; last  by congruence).
Time eauto.
Time Qed.
Time
Lemma getSliceModel_len_inv {T} (p : slice.t T) l 
  l' : getSliceModel p l = Some l' \226\134\146 length l' = p.(slice.length).
Time Proof.
Time rewrite /getSliceModel.
Time (apply sublist_lookup_length).
Time Qed.
Time
Lemma wp_sliceAppend {T} s E (p : slice.t T) l1 l2 
  v :
  {{{ \226\150\183 p \226\134\166 (l1, l2) }}} sliceAppend p v @ s; E {{{ 
  (p' : slice.t T), RET p'; p' \226\134\166 (l2 ++ [v], l2 ++ [v])}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hp H\206\166".
Time iDestruct "Hp" as ( Heq ) "Hp".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct "Hp" as ( ? ) "Hp".
Time iDestruct (gen_typed_heap_valid1 (Ptr.Heap T) with "H\207\131 Hp") as % ?.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (simpl in *).
Time intuition.
Time subst.
Time iFrame.
Time iMod (gen_typed_heap_dealloc (Ptr.Heap T) with "H\207\131 Hp") as "H\207\131".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (gen_typed_heap_alloc with "H\207\131") as
 "[H\207\131 Hp]" ; first  by eauto).
Time iFrame.
Time iModIntro.
Time iApply "H\206\166".
Time iFrame.
Time iPureIntro.
Time (simpl in *).
Time inv_step.
Time (apply getSliceModel_len_inv in Heq).
Time rewrite /getSliceModel sublist_lookup_all //= app_length //=.
Time lia.
Time Qed.
Time
Lemma take_1_drop {T} (x : T) n l :
  nth_error l n = Some x \226\134\146 take 1 (drop n l) = [x].
Time Proof.
Time revert l.
Time
(<ssreflect_plugin::ssrtclintros@0> induction n =>l; destruct l; inversion 1;
  eauto).
Time Qed.
Time
Lemma slice_agree {T} (p : slice.t T) v1 v1' v2 v2' 
  q1 q2 : p \226\134\166{ q1} (v1, v1') -\226\136\151 p \226\134\166{ q2} (v2, v2') -\226\136\151 \226\140\156v1 = v2 \226\136\167 v1' = v2'\226\140\157.
Time Proof.
Time iIntros "Hp1 Hp2".
Time iDestruct "Hp1" as ( ? ? ) "Hp1".
Time iDestruct "Hp2" as ( ? ? ) "Hp2".
Time iAssert \226\140\156v1 = v2\226\140\157%I with "[Hp1 Hp2]" as % Heq.
Time {
Time (simpl).
Time
iApply
 (@Count_Typed_Heap.mapsto_agree _ _ _ _ _ go_heap_inG (Ptr.Heap T)
 with "Hp1 Hp2").
Time }
Time subst.
Time iPureIntro.
Time (simpl in *).
Time (split; congruence).
Time Qed.
Time
Lemma slice_agree' {T} (p : slice.t T) v1 v2 q1 q2 :
  p \226\134\166{ q1} v1 -\226\136\151 p \226\134\166{ q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "Hp1 Hp2".
Time iDestruct "Hp1" as ( l1 ) "Hp1".
Time iDestruct "Hp2" as ( l2 ) "Hp2".
Time (iDestruct (slice_agree with "Hp1 Hp2") as "(?&?)"; eauto).
Time Qed.
Time
Lemma wp_sliceAppendSlice_aux {T} s E (p1 p2 : slice.t T) 
  q l2' l1 l2 rem off :
  rem + off <= length l2
  \226\134\146 {{{ \226\150\183 p1 \226\134\166 l1 \226\136\151 \226\150\183 p2 \226\134\166{ q} (l2', l2) }}} sliceAppendSlice_aux p1 p2 rem
                                               off @ s; E {{{ 
  (p' : slice.t T), RET p'; p' \226\134\166 (l1 ++ firstn rem (skipn off l2))
                            \226\136\151 p2 \226\134\166{ q} (l2', l2)}}}.
Time Proof.
Time iIntros ( Hlen \206\166 ) "(>Hp1&>Hp2) H\206\166".
Time iInduction rem as [| rem] "IH" forall ( off Hlen l1 p1 ).
Time -
Time (simpl).
Time rewrite firstn_O app_nil_r -wp_bind_proc_val.
Time (iNext; wp_ret; iApply "H\206\166"; iFrame).
Time -
Time (simpl).
Time
(<ssreflect_plugin::ssrtclseq@0>
 destruct (nth_error l2 off) as [x| ] eqn:Hnth ; last  first).
Time {
Time (apply nth_error_None in Hnth).
Time lia.
Time }
Time wp_bind.
Time (iApply (wp_sliceRead with "Hp2"); eauto).
Time iIntros "!> Hp2".
Time wp_bind.
Time iDestruct "Hp1" as ( ? ) "Hp1".
Time (iApply (wp_sliceAppend with "Hp1"); eauto).
Time iIntros "!>".
Time iIntros ( p1' ) "Hp1".
Time rewrite -Nat.add_1_l -take_take_drop drop_drop assoc Nat.add_1_r.
Time (erewrite take_1_drop; eauto).
Time (iApply ("IH" with "[] [Hp1] Hp2"); eauto).
Time *
Time (iPureIntro; lia).
Time *
Time iExists _.
Time eauto.
Time Qed.
Time
Lemma wp_sliceAppendSlice {T} s E (p1 p2 : slice.t T) 
  q l1 l2' l2 :
  {{{ \226\150\183 p1 \226\134\166 l1 \226\136\151 \226\150\183 p2 \226\134\166{ q} (l2', l2) }}} sliceAppendSlice p1 p2 @ s; E {{{ 
  (p' : slice.t T), RET p'; p' \226\134\166 (l1 ++ l2) \226\136\151 p2 \226\134\166{ q} (l2', l2)}}}.
Time Proof.
Time rewrite /sliceAppendSlice.
Time iIntros ( \206\166 ) "(>Hp1&>Hp2) H\206\166".
Time iAssert \226\140\156p2.(slice.length) = length l2\226\140\157%I with "[-]" as % ->.
Time {
Time iDestruct "Hp2" as ( vs2 Heq2 ) "Hp2".
Time iPureIntro.
Time symmetry.
Time (eapply sublist_lookup_length; eauto).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (wp_sliceAppendSlice_aux with "[$]")
 ; first  by lia).
Time rewrite drop_0 firstn_all.
Time iApply "H\206\166".
Time Qed.
Time
Lemma wp_bytesToString p bs0 bs q s E :
  {{{ \226\150\183 p \226\134\166{ q} (bs0, bs) }}} bytesToString p @ s; E {{{ RET 
  bytes_to_string bs; p \226\134\166{ q} (bs0, bs)}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hp H\206\166".
Time iDestruct "Hp" as ( Heq ) "Hp".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct "Hp" as ( ? ) "Hp".
Time
iDestruct (gen_typed_heap_valid (Ptr.Heap _) with "H\207\131 Hp") as % [s' [? ?]].
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (simpl in *).
Time intuition.
Time subst.
Time iFrame.
Time iModIntro.
Time iApply "H\206\166".
Time iFrame.
Time iPureIntro.
Time (repeat (deex; inv_step)).
Time eauto.
Time Qed.
Time
Lemma wp_bytesToString' p bs q s E :
  {{{ \226\150\183 p \226\134\166{ q} bs }}} bytesToString p @ s; E {{{ RET 
  bytes_to_string bs; p \226\134\166{ q} bs}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hp H\206\166".
Time iDestruct "Hp" as ( vs ) "Hp".
Time iApply (wp_bytesToString with "Hp").
Time iIntros "!> Hp".
Time iApply "H\206\166".
Time (iExists _; eauto).
Time Qed.
Time
Lemma wp_stringToBytes str s E :
  {{{ True }}} stringToBytes str @ s; E {{{ p, RET p; 
  p.(slice.ptr) \226\134\166 string_to_bytes str
  \226\136\151 \226\140\156p.(slice.length) = String.length str \226\136\167 p.(slice.offset) = 0\226\140\157}}}.
Time Proof.
Time iIntros ( \206\166 ) "_ H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time inv_step.
Time (simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (destruct H0 as ((?, ?), ?)).
Time (do 2 (inv_step; intuition)).
Time (iMod (gen_typed_heap_alloc with "H\207\131") as "(H\207\131&Hp)"; eauto).
Time iFrame.
Time iApply "H\206\166".
Time iFrame.
Time (iPureIntro; split; eauto).
Time Qed.
Time
Definition lock_mapsto `{gooseG \206\163} (l : LockRef) q 
  mode : iProp \206\163 := (\226\140\156l \226\137\160 nullptr _\226\140\157 \226\136\151 Count_Typed_Heap.mapsto l q mode tt)%I.
Time
Definition lock_inv (l : LockRef) (P : nat \226\134\146 iProp \206\163) 
  (Q : iProp \206\163) : iProp \206\163 :=
  (\226\136\131 (n : Z) stat,
     lock_mapsto l n stat
     \226\136\151 match stat with
       | Unlocked => \226\140\156n = O\226\140\157 \226\136\151 P O
       | ReadLocked n' => \226\140\156n = S n'\226\140\157 \226\136\151 P (S n')
       | Locked => \226\140\156n = (- 1)%Z\226\140\157
       end)%I.
Time
Definition is_lock (N : namespace) (l : LockRef) (P : nat \226\134\146 iProp \206\163)
  (Q : iProp \206\163) : iProp \206\163 :=
  (\226\150\161 (\226\136\128 n, P n ==\226\136\151 P (S n) \226\136\151 Q)
   \226\136\151 \226\150\161 (\226\136\128 n, Q \226\136\151 P (S n) ==\226\136\151 P n) \226\136\151 inv N (lock_inv l P Q))%I.
Time Definition wlocked (l : LockRef) : iProp \206\163 := lock_mapsto l 1 Locked.
Time
Definition rlocked (l : LockRef) : iProp \206\163 := lock_mapsto l (- 1) Unlocked.
Time #[global]Instance inhabited_LockStatus : (Inhabited LockStatus).
Time Proof.
Time eexists.
Time exact Unlocked.
Time Qed.
Time #[global]Instance inhabited_LockMode : (Inhabited LockMode).
Time Proof.
Time eexists.
Time exact Reader.
Time Qed.
Time Lemma wlocked_wlocked l : wlocked l -\226\136\151 wlocked l -\226\136\151 False.
Time Proof.
Time rewrite /wlocked /lock_mapsto.
Time iIntros "(%&H1) (%&H2)".
Time
(iApply (Count_Typed_Heap.mapsto_valid_generic l 1 1 with "[H1] [H2]");
  try lia; eauto).
Time Qed.
Time
Lemma wp_newLock_raw s E :
  {{{ True }}} newLock @ s; E {{{ (l : LockRef), RET l; 
  lock_mapsto l 0 Unlocked}}}.
Time Proof.
Time iIntros ( \206\166 ) "_ H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (do 2 (inv_step; intuition)).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (gen_typed_heap_alloc with "H\207\131") as
 "(H\207\131&Hl)" ; first  by eauto).
Time iFrame.
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_newLock N s E (P : nat \226\134\146 iProp \206\163) (Q : iProp \206\163) :
  {{{ \226\150\161 (\226\136\128 n, P n ==\226\136\151 P (S n) \226\136\151 Q) \226\136\151 \226\150\161 (\226\136\128 n, Q \226\136\151 P (S n) ==\226\136\151 P n) \226\136\151 P O }}} newLock @ s; E {{{ 
  (l : LockRef), RET l; is_lock N l P Q}}}.
Time Proof.
Time iIntros ( \206\166 ) "(#HPQ1&#HPQ2&HP) H\206\166".
Time rewrite -wp_fupd.
Time (iApply wp_newLock_raw; auto).
Time iIntros ( l ) "!> Hl".
Time (iApply "H\206\166"; eauto).
Time iMod (inv_alloc N _ (lock_inv l P Q) with "[HP Hl]").
Time {
Time iNext.
Time iExists O , Unlocked.
Time by iFrame.
Time }
Time iModIntro.
Time iFrame "# \226\136\151".
Time Qed.
Time
Lemma lock_acquire_Reader_success_inv (l : LockRef) 
  s \207\131 h' :
  match lock_acquire Reader s with
  | Some s' => updAllocs l (s', ())
  | None => none
  end \207\131.(heap) (Val h' ())
  \226\134\146 lock_acquire Reader s = Some (force_read_lock s)
    \226\136\167 h' = {| allocs := updDyn l (force_read_lock s, ()) \207\131.(heap).(allocs) |}.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> destruct s =>//=; inversion 1; subst;
  eauto).
Time Qed.
Time
Lemma wp_lockAcquire_read N l P Q s E :
  \226\134\145N \226\138\134 E
  \226\134\146 {{{ is_lock N l P Q }}} lockAcquire l Reader @ s; E {{{ RET tt; 
  Q \226\136\151 rlocked l}}}.
Time Proof.
Time iIntros ( ? \206\166 ) "(#HPQ1&#HPQ2&#Hinv) H\206\166".
Time iInv N as ( k stat ) "(>(%&H)&Hstat)".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 H") as % [s' [? Hlock]].
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s; eauto).
Time (inv_step; simpl in *; subst; try congruence).
Time (destruct l0; inversion Htl_err).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclseq@0>
 edestruct (lock_acquire_Reader_success_inv) as (?, ?) ; first  by eauto).
Time (destruct stat).
Time {
Time (apply Count_Heap.Cinr_included_excl' in Hlock; subst).
Time (simpl in *; congruence).
Time }
Time {
Time
iMod (gen_typed_heap_readlock' Ptr.Lock with "H\207\131 H") as ( s' Heq ) "(H\207\131&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time iDestruct "Hstat" as "(%&HP)".
Time iMod ("HPQ1" with "HP") as "(HP&HQ)".
Time (do 2 iModIntro).
Time subst.
Time iDestruct (read_split_join2 (T:=Ptr.Lock) with "Hl") as "(Hl&?)".
Time iSplitL "Hl HP".
Time {
Time iNext.
Time iExists (S (S num)) , (ReadLocked (S num)).
Time subst.
Time by iFrame.
Time }
Time (iApply "H\206\166"; by iFrame).
Time }
Time {
Time
iMod (gen_typed_heap_readlock Ptr.Lock with "H\207\131 H") as ( s' Heq ) "(H\207\131&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time iDestruct "Hstat" as "(%&HP)".
Time iMod ("HPQ1" with "HP") as "(HP&HQ)".
Time (do 2 iModIntro).
Time subst.
Time iDestruct (read_split_join2 (T:=Ptr.Lock) with "Hl") as "(Hl&?)".
Time iSplitL "Hl HP".
Time {
Time iNext.
Time iExists (S O) , (ReadLocked O).
Time subst.
Time by iFrame.
Time }
Time (iApply "H\206\166"; by iFrame).
Time }
Time Qed.
Time
Lemma wp_lockRelease_read_raw l q stat stat' s E :
  lock_release Reader stat = Some stat'
  \226\134\146 {{{ lock_mapsto l q stat }}} lockRelease l Reader @ s; E {{{ RET tt; 
  lock_mapsto l q stat'}}}.
Time Proof.
Time iIntros ( Hrel \206\166 ) "(%&H) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 H") as % [s' [? Hlock]].
Time (destruct stat; swap 2 3).
Time {
Time (inversion Hrel).
Time }
Time {
Time (inversion Hrel).
Time }
Time (apply Count_Heap.Cinl_included_nat' in Hlock as (m, (?, ?)); subst).
Time (<ssreflect_plugin::ssrtclseq@0> destruct m ; first  by lia).
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s; eauto).
Time (inv_step; simpl in *; subst; try congruence).
Time
(destruct l0; try destruct num0; try inversion Htl_err; simpl in *;
  try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
iMod (gen_typed_heap_readunlock Ptr.Lock with "H\207\131 H") as ( s' Heq ) "(H\207\131&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time iModIntro.
Time
(destruct num; destruct s'; simpl in *; inv_step; iFrame; by
  iApply "H\206\166"; iFrame).
Time Qed.
Time
Lemma wp_lockRelease_read N l P Q s E :
  \226\134\145N \226\138\134 E
  \226\134\146 {{{ is_lock N l P Q \226\136\151 Q \226\136\151 rlocked l }}} lockRelease l Reader @ s; E {{{ RET tt; True}}}.
Time Proof.
Time iIntros ( ? \206\166 ) "((#HPQ1&#HPQ2&#Hinv)&HQ&(%&Hrlocked)) H\206\166".
Time iInv N as ( k stat ) "(>(%&H)&Hstat)".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 H") as % [s' [? Hlock]].
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 Hrlocked") as %
 [s'' [? Hrlock]].
Time (apply Count_Heap.Cinl_included_nat' in Hrlock as (m, (?, ?)); subst).
Time (destruct stat; swap 2 3).
Time {
Time (apply Count_Heap.Cinr_included_excl' in Hlock; subst).
Time inv_step.
Time (simpl in *).
Time congruence.
Time }
Time {
Time (iDestruct "Hstat" as "(>%&HP)"; subst).
Time iDestruct (mapsto_valid' (T:=Ptr.Lock) with "H Hrlocked") as % [].
Time }
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s; eauto).
Time (inv_step; simpl in *; subst; try congruence).
Time
(destruct l0; try destruct num0; try inversion Htl_err; simpl in *;
  try congruence).
Time (apply Count_Heap.Cinl_included_nat in Hlock).
Time lia.
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (iDestruct "Hstat" as "(%&HP)"; subst).
Time
iMod (gen_typed_heap_readunlock Ptr.Lock with "H\207\131 H") as ( s' Heq ) "(H\207\131&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time iMod ("HPQ2" with "[$]") as "HP".
Time iModIntro.
Time (unfold rlocked).
Time (destruct num).
Time *
Time
iDestruct (Count_Typed_Heap.read_split_join (T:=Ptr.Lock) with "[$]") as "H".
Time iSplitL "H\207\131".
Time {
Time (destruct s'; inversion Htl; subst; iFrame).
Time }
Time iModIntro.
Time iSplitL "H HP".
Time {
Time iNext.
Time iExists O , Unlocked.
Time by iFrame.
Time }
Time by iApply "H\206\166"; iFrame.
Time *
Time
iDestruct (Count_Typed_Heap.read_split_join2 (T:=Ptr.Lock) with "[$]") as "H".
Time iSplitL "H\207\131".
Time {
Time (destruct s'; inversion Htl; subst; iFrame).
Time }
Time iModIntro.
Time iSplitL "H HP".
Time {
Time iNext.
Time iExists (S num) , (ReadLocked num).
Time by iFrame.
Time }
Time by iApply "H\206\166"; iFrame.
Time Qed.
Time
Lemma lock_acquire_Writer_success_inv (l : LockRef) 
  s \207\131 h' :
  match lock_acquire Writer s with
  | Some s' => updAllocs l (s', ())
  | None => none
  end \207\131.(heap) (Val h' ())
  \226\134\146 s = Unlocked
    \226\136\167 lock_acquire Writer s = Some Locked
      \226\136\167 h' = {| allocs := updDyn l (Locked, ()) \207\131.(heap).(allocs) |}.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> destruct s =>//=; inversion 1; subst;
  eauto).
Time Qed.
Time
Lemma wp_lockAcquire_writer N l P Q s0 E :
  \226\134\145N \226\138\134 E
  \226\134\146 {{{ is_lock N l P Q }}} lockAcquire l Writer @ s0; E {{{ RET tt; 
  P O \226\136\151 wlocked l}}}.
Time Proof.
Time iIntros ( ? \206\166 ) "(#HPQ1&#HPQ2&#Hinv) H\206\166".
Time iInv N as ( k stat ) "(>(%&H)&Hstat)".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 H") as % [s' [? Hlock]].
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s0; eauto).
Time (inv_step; simpl in *; subst; try congruence).
Time (destruct l0; inversion Htl_err).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time
(<ssreflect_plugin::ssrtclseq@0>
 edestruct (lock_acquire_Writer_success_inv) as (?, (?, ?)) ; first  by
 eauto; subst).
Time (destruct stat).
Time {
Time (apply Count_Heap.Cinr_included_excl' in Hlock; subst).
Time (simpl in *; congruence).
Time }
Time {
Time subst.
Time (simpl in *).
Time (apply Count_Heap.Cinl_included_nat in Hlock).
Time lia.
Time }
Time (iDestruct "Hstat" as "(%&HP)"; subst).
Time iMod (gen_typed_heap_update Ptr.Lock with "H\207\131 H") as "($&Hl)".
Time (simpl; inv_step).
Time iFrame.
Time (do 2 iModIntro).
Time iDestruct (read_split_join3 (T:=Ptr.Lock) l O with "Hl") as "(?&Hl)".
Time iSplitL "Hl".
Time {
Time iNext.
Time iExists (- 1)%Z , Locked.
Time by iFrame.
Time }
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_lockRelease_writer_raw l stat stat' s E :
  lock_release Writer stat = Some stat'
  \226\134\146 {{{ lock_mapsto l 0 stat }}} lockRelease l Writer @ s; E {{{ RET tt; 
  lock_mapsto l 0 stat'}}}.
Time Proof.
Time iIntros ( Hrel \206\166 ) "(%&H) H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 H") as % [s' [? Hlock]].
Time (destruct stat; swap 1 3).
Time {
Time (inversion Hrel).
Time }
Time {
Time (inversion Hrel).
Time }
Time (apply Count_Heap.Cinr_included_excl' in Hlock; subst).
Time (inversion Hrel).
Time subst.
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s; eauto).
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (simpl in Htl).
Time inv_step.
Time iMod (gen_typed_heap_update Ptr.Lock with "H\207\131 H") as "($&Hl)".
Time iFrame.
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_lockRelease_writer N l P Q s0 E :
  \226\134\145N \226\138\134 E
  \226\134\146 {{{ is_lock N l P Q \226\136\151 P O \226\136\151 wlocked l }}} lockRelease l Writer @ s0; E {{{ RET tt; True}}}.
Time Proof.
Time iIntros ( ? \206\166 ) "((#HPQ1&#HPQ2&#Hinv)&HQ&(%&Hrlocked)) H\206\166".
Time iInv N as ( k stat ) "(>(%&H)&Hstat)".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 H") as % [s' [? Hlock]].
Time
iDestruct (gen_typed_heap_valid2 Ptr.Lock with "H\207\131 Hrlocked") as %
 [s'' [? Hrlock]].
Time (apply Count_Heap.Cinr_included_excl' in Hrlock; subst).
Time iModIntro.
Time iSplit.
Time {
Time iPureIntro.
Time (destruct s0; eauto).
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iFrame.
Time (destruct stat).
Time {
Time (iDestruct "Hstat" as "%"; subst).
Time iDestruct (read_split_join3 (T:=Ptr.Lock) l O with "[$]") as "H".
Time (simpl in Htl).
Time inv_step.
Time iMod (gen_typed_heap_update Ptr.Lock with "H\207\131 H") as "($&Hl)".
Time (do 2 iModIntro).
Time iSplitL "Hl HQ".
Time {
Time iNext.
Time iExists O , Unlocked.
Time by iFrame.
Time }
Time (iApply "H\206\166"; by iFrame).
Time }
Time {
Time (apply Count_Heap.Cinl_included_nat' in Hlock as (?, (?, ?)); subst).
Time (simpl in *; congruence).
Time }
Time {
Time (apply Count_Heap.Cinl_included_nat' in Hlock as (?, (?, ?)); subst).
Time (simpl in *; congruence).
Time }
Time Qed.
Time
Lemma wp_newMap T s E :
  {{{ True }}} newMap T @ s; E {{{ (p : Map T), RET p; 
  p \226\134\166 (\226\136\133 : gmap uint64 T)}}}.
Time Proof.
Time iIntros ( \206\166 ) "_ H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time (do 2 (inv_step; intuition)).
Time (iMod (gen_typed_heap_alloc with "H\207\131") as "(H\207\131&Hp)"; eauto).
Time iFrame.
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_mapAlter_start {T} s E (p : Map T) (m : gmap uint64 T) 
  k f :
  {{{ \226\150\183 p \226\134\166 m }}} Call
                    (InjectOp.inject (MapAlter p k f SemanticsHelpers.Begin)) @ s; E {{{ RET tt; 
  Count_Typed_Heap.mapsto p 0 Locked m}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct "Hi" as ( ? ) "Hi".
Time iDestruct (gen_typed_heap_valid1 (Ptr.Map T) with "H\207\131 Hi") as % ?.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; simpl in *; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iMod (@gen_typed_heap_update with "H\207\131 Hi") as "[$ Hi]".
Time iFrame.
Time (iApply "H\206\166"; eauto).
Time Qed.
Time
Lemma map_mapsto_non_null {T} (p : Map T) (v : gmap uint64 T) :
  (p \226\134\166 v -\226\136\151 \226\140\156p \226\137\160 nullptr _\226\140\157)%I.
Time Proof.
Time (iIntros "(?&?)"; eauto).
Time Qed.
Time
Lemma wp_mapAlter {T} s E (p : Map T) (m : gmap uint64 T) 
  k f :
  {{{ \226\150\183 p \226\134\166 m }}} mapAlter p k f @ s; E {{{ RET tt; 
  p \226\134\166 partial_alter f k m}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time rewrite /mapAlter /nonAtomicWriteOp.
Time iDestruct (map_mapsto_non_null with "Hi") as % Hnonnull.
Time wp_bind.
Time (iApply (wp_mapAlter_start with "Hi"); eauto).
Time iNext.
Time iIntros "Hi".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct (gen_typed_heap_valid1 (Ptr.Map T) with "H\207\131 Hi") as % ?.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (subst; simpl in *).
Time iMod (gen_typed_heap_update (Ptr.Map T) with "H\207\131 Hi") as "[$ Hi]".
Time iFrame.
Time iApply "H\206\166".
Time (inv_step; by iFrame).
Time Qed.
Time
Lemma wp_mapLookup {T} s E (p : Map T) (m : gmap uint64 T) 
  q k : {{{ \226\150\183 p \226\134\166{ q} m }}} mapLookup p k @ s; E {{{ RET 
  m !! k; p \226\134\166{ q} m}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time rewrite /mapLookup.
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct "Hi" as ( ? ) "Hi".
Time
iDestruct (gen_typed_heap_valid (Ptr.Map T) with "H\207\131 Hi") as % [s' [? ?]].
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (inv_step; simpl in *; subst; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time iFrame.
Time (iApply "H\206\166"; by iFrame).
Time Qed.
Time
Lemma wp_MapStartIter {T} s E (p : Map T) (m : gmap uint64 T) 
  q :
  {{{ \226\150\183 p \226\134\166{ q} m }}} (Call (InjectOp.inject (@MapStartIter _ T p)))%proc @ s; E {{{ 
  l, RET l; \226\140\156Permutation.Permutation l (fin_maps.map_to_list m)\226\140\157
            \226\136\151 Count_Typed_Heap.mapsto p q (ReadLocked O) m}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time iDestruct "Hi" as ( Hnonnull ) "Hi".
Time iDestruct (gen_typed_heap_valid (Ptr.Map T) with "H\207\131 Hi") as % ?.
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time (destruct H0 as (?, (?, ?))).
Time (inv_step; simpl in *; subst; try congruence).
Time (destruct l0; eauto; try congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (subst; simpl in *).
Time
iMod (gen_typed_heap_readlock (Ptr.Map T) with "H\207\131 Hi") as ( s' Heq )
 "(H\207\131&Hl)".
Time iFrame.
Time
(destruct l0; simpl in *; try congruence; inv_step; simpl; iFrame; iApply
  "H\206\166"; iFrame; iModIntro; eauto).
Time Qed.
Time
Lemma wp_MapEndIter {T} s E (p : Map T) (m : gmap uint64 T) 
  q :
  p \226\137\160 nullptr _
  \226\134\146 {{{ \226\150\183 Count_Typed_Heap.mapsto p q (ReadLocked O) m }}} 
  (Call (InjectOp.inject (@MapEndIter _ T p)))%proc @ s; E {{{ RET tt; 
  p \226\134\166{ q} m}}}.
Time Proof.
Time iIntros ( Hnonnull \206\166 ) ">Hi H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "(?&H\207\131&?)".
Time
iDestruct (gen_typed_heap_valid2 (Ptr.Map T) with "H\207\131 Hi") as %
 [s' [? Hlock]].
Time (apply Count_Heap.Cinl_included_nat' in Hlock as (?, (?, ?)); subst).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time
(destruct s'; inv_step; simpl in *; inv_step; subst; try congruence; try lia;
  destruct num; congruence).
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (subst; simpl in *).
Time
iMod (gen_typed_heap_readunlock (Ptr.Map T) with "H\207\131 Hi") as ( s' Heq )
 "(H\207\131&Hl)".
Time iFrame.
Time (destruct l0; simpl in *; try congruence; inv_step; simpl; iFrame).
Time (destruct s'; inv_step; iFrame; iApply "H\206\166"; iFrame; iModIntro; eauto).
Time Qed.
Time
Lemma wp_mapIter {T} s E (p : Map T) (m : gmap uint64 T) 
  q body \206\166 :
  p \226\137\160 nullptr _
  \226\134\146 \226\150\183 p \226\134\166{ q} m
    -\226\136\151 \226\150\183 (\226\136\128 l,
            \226\140\156Permutation.Permutation l (fin_maps.map_to_list m)\226\140\157
            -\226\136\151 WP mapIterLoop l body @ s; E {{ \206\166 }})
       -\226\136\151 WP mapIter p body @ s; E {{ v, p \226\134\166{ q} m \226\136\151 \206\166 v }}.
Time Proof.
Time iIntros ( ? ) "Hp Hloop".
Time rewrite /mapIter.
Time wp_bind.
Time iApply (wp_MapStartIter with "Hp").
Time iNext.
Time iIntros ( l ) "(%&Hp)".
Time wp_bind.
Time iApply (wp_wand with "[Hloop]").
Time {
Time (iApply "Hloop"; eauto).
Time }
Time iIntros ( [] ) "H\206\166".
Time (iApply (wp_MapEndIter with "Hp"); eauto).
Time iFrame.
Time eauto.
Time Qed.
Time
Lemma wp_randomUint64 s E :
  {{{ True }}} randomUint64 @ s; E {{{ (x : uint64), RET x; True}}}.
Time Proof.
Time iIntros ( \206\166 ) "_ H\206\166".
Time iApply wp_lift_call_step.
Time iIntros ( (n, \207\131) ) "?".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; auto).
Time iPureIntro.
Time inv_step.
Time (simpl in *; subst; try congruence).
Time inv_step.
Time }
Time iIntros ( e2 (n', \207\1312) Hstep ) "!>".
Time (inversion Hstep; subst).
Time inv_step.
Time (match goal with
      | H:Data.step RandomUint64 _ _ |- _ => inversion H
      end).
Time subst.
Time iFrame.
Time by iApply "H\206\166".
Time Qed.
Time End lifting.
