Time From Coq Require Import List.
Time From stdpp Require Import gmap.
Time From Perennial Require Export Lib.
Time Definition size := 1000.
Time Definition addr := nat.
Time
Definition wf_range (d : gmap addr nat) := \226\136\128 i, is_Some (d !! i) \226\134\148 i < size.
Time
Fixpoint init_zero_aux (n : nat) (s : gmap addr nat) :=
  match n with
  | O => s
  | S n' => <[n':=O]> (init_zero_aux n' s)
  end.
Time Definition init_zero := init_zero_aux size gmap_empty.
Time
Lemma init_zero_insert_zero i : i < size \226\134\146 <[i:=0]> init_zero = init_zero.
Time Proof.
Time rewrite /init_zero.
Time (induction 1).
Time -
Time rewrite //=.
Time rewrite insert_insert //.
Time -
Time rewrite //=.
Time (<ssreflect_plugin::ssrtclseq@0> rewrite insert_commute ; last  by lia).
Time rewrite IHle //=.
Time Qed.
Time Lemma init_zero_lookup_lt_zero i : i < size \226\134\146 init_zero !! i = Some 0.
Time Proof.
Time rewrite /init_zero.
Time (induction 1).
Time -
Time rewrite lookup_insert //=.
Time -
Time rewrite //=.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by lia).
Time eauto.
Time Qed.
Time Lemma init_zero_lookup_ge_None i : \194\172 i < size \226\134\146 init_zero !! i = None.
Time Proof.
Time revert i.
Time rewrite /init_zero.
Time (<ssreflect_plugin::ssrtclintros@0> induction size =>i ?).
Time -
Time rewrite //=.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite lookup_insert_ne ; last  by lia).
Time (rewrite IHn; auto).
Time Qed.
Time Lemma wf_init_zero : wf_range init_zero.
Time Proof.
Time (intros i).
Time split.
Time -
Time (intros Hsome).
Time (apply not_ge).
Time (intros ?).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite init_zero_lookup_ge_None // in 
 {} Hsome ; last  lia).
Time (eapply is_Some_None; eauto).
Time -
Time (intros ?).
Time rewrite init_zero_lookup_lt_zero //.
Time eauto.
Time Qed.
Time
Lemma well_sized_mem_0_init (mem : gmap addr nat) :
  (\226\136\128 i, is_Some (mem !! i) \226\134\148 i < size) \226\134\146 (\206\187 _, 0) <$> mem = init_zero.
Time Proof.
Time (intros).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite -leibniz_equiv_iff =>i).
Time (destruct (nat_lt_dec i size)).
Time *
Time rewrite init_zero_lookup_lt_zero //.
Time rewrite lookup_fmap.
Time (edestruct (H i)).
Time (destruct H1; eauto).
Time rewrite H1 //=.
Time *
Time rewrite lookup_fmap.
Time (edestruct (H i)).
Time (destruct (mem !! i) as [| ] eqn:Heq).
Time **
Time rewrite Heq in  {} H0.
Time exfalso.
Time intuition eauto.
Time **
Time rewrite init_zero_lookup_ge_None //=.
Time Qed.
Time Module TwoDisk.
Time Inductive diskId :=
       | d0 : _
       | d1 : _.
Time Definition disk := gmap addr nat.
Time
Inductive DisksState :=
  | BothDisks : forall (d_0 : disk) (d_1 : disk), _
  | OnlyDisk : forall (id : diskId) (d : disk), _.
Time
Inductive Op : Type -> Type :=
  | Read_Mem : forall i : addr, Op nat
  | Write_Mem : forall (i : addr) (v : nat), Op unit
  | CAS : forall (i : addr) (vold : nat) (vnew : nat), Op nat
  | Read_Disk : forall (id : diskId) (i : addr), Op (option nat)
  | Write_Disk : forall (id : diskId) (i : addr) (v : nat), Op unit.
Time
Record State := mkState {mem_state : gmap addr nat; disks_state : DisksState}.
Time
Definition disk0 ds : option disk :=
  match disks_state ds with
  | BothDisks d_0 _ => Some d_0
  | OnlyDisk d0 d => Some d
  | OnlyDisk d1 _ => None
  end.
Time
Definition disk1 ds : option disk :=
  match disks_state ds with
  | BothDisks _ d_1 => Some d_1
  | OnlyDisk d0 _ => None
  | OnlyDisk d1 d => Some d
  end.
Time
Definition get_disk (i : diskId) (state : State) : 
  option disk := match i with
                 | d0 => disk0 state
                 | d1 => disk1 state
                 end.
Time
Definition wf_disk (md : option disk) :=
  match md with
  | Some d => wf_range d
  | None => True
  end.
Time
Definition state_wf s :=
  wf_range (mem_state s) \226\136\167 wf_disk (disk0 s) \226\136\167 wf_disk (disk1 s).
Time
Definition lookup_default (i : addr) (s : gmap addr nat) : nat :=
  match s !! i with
  | Some n => n
  | None => 0
  end.
Time
Definition upd_default (i : addr) (v : nat) (s : gmap addr nat) :
  gmap addr nat := match s !! i with
                   | Some _ => <[i:=v]> s
                   | None => s
                   end.
Time
Definition lookup_mem (i : addr) : State -> nat :=
  fun s => lookup_default i (mem_state s).
Time
Definition lookup_disk id (i : addr) : State -> option nat :=
  fun s =>
  match get_disk id s with
  | None => None
  | Some d => Some (lookup_default i d)
  end.
Time
Definition set_disk' (i : diskId) (state : DisksState) 
  (d : disk) : DisksState :=
  match i with
  | d0 =>
      match state with
      | BothDisks _ d_1 => BothDisks d d_1
      | OnlyDisk d0 _ => OnlyDisk d0 d
      | OnlyDisk d1 d_1 => BothDisks d d_1
      end
  | d1 =>
      match state with
      | BothDisks d_0 _ => BothDisks d_0 d
      | OnlyDisk d0 d_0 => BothDisks d_0 d
      | OnlyDisk d1 _ => OnlyDisk d1 d
      end
  end.
Time
Definition maybe_fail_disk' (i : diskId) (state : DisksState) : DisksState :=
  match i with
  | d0 =>
      match state with
      | BothDisks _ d_1 => OnlyDisk d1 d_1
      | _ => state
      end
  | d1 =>
      match state with
      | BothDisks d_0 _ => OnlyDisk d0 d_0
      | _ => state
      end
  end.
Time
Definition upd_mem (i : addr) (v : nat) :=
  fun s =>
  {|
  mem_state := upd_default i v (mem_state s);
  disks_state := disks_state s |}.
Time
Definition upd_disk (id : diskId) (i : addr) (v : nat) : 
  State -> State :=
  fun s =>
  {|
  mem_state := mem_state s;
  disks_state := match get_disk id s with
                 | Some d => set_disk' id (disks_state s) (upd_default i v d)
                 | None => disks_state s
                 end |}.
Time
Definition maybe_fail_disk (id : diskId) : State -> State :=
  fun s =>
  {|
  mem_state := mem_state s;
  disks_state := maybe_fail_disk' id (disks_state s) |}.
Time Import RelationNotations.
Time
Definition cas_rel (i : addr) (vold : nat) (vnew : nat) :
  relation State State nat :=
  v <- reads (lookup_mem i);
  if nat_eq_dec v vold then puts (upd_mem i vnew);; pure v else pure v.
Time
Definition init_state :=
  {| mem_state := init_zero; disks_state := BothDisks init_zero init_zero |}.
Time Lemma init_state_wf : state_wf init_state.
Time Proof.
Time (split_and !; apply wf_init_zero).
Time Qed.
Time
Definition crash_fun :=
  fun s => {| mem_state := init_zero; disks_state := disks_state s |}.
Time
Definition disk_fail :=
  rel_or (pure tt)
    (rel_or (puts (maybe_fail_disk d0)) (puts (maybe_fail_disk d1))).
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Read_Mem i => reads (lookup_mem i)
          | Write_Mem i v => puts (upd_mem i v)
          | Read_Disk id i => disk_fail;; reads (lookup_disk id i)
          | Write_Disk id i v => disk_fail;; puts (upd_disk id i v)
          | CAS i vold vnew => cas_rel i vold vnew
          end;
  crash_step := puts crash_fun;
  finish_step := puts crash_fun |}.
Time
Lemma crash_total_ok (s : State) :
  exists s', dynamics.(crash_step) s (Val s' tt).
Time Proof.
Time (eexists; econstructor).
Time Qed.
Time
Lemma crash_non_err_ok (s : State) ret :
  dynamics.(crash_step) s ret -> ret \226\137\160 Err.
Time Proof.
Time (inversion 1; congruence).
Time Qed.
Time
Definition l : Layer Op :=
  {|
  Layer.OpState := State;
  sem := dynamics;
  trace_proj := fun _ => nil;
  crash_preserves_trace := fun _ _ _ => eq_refl;
  crash_total := crash_total_ok;
  finish_total := crash_total_ok;
  crash_non_err := crash_non_err_ok;
  finish_non_err := crash_non_err_ok;
  initP := fun s => s = init_state |}.
Time End TwoDisk.
Time Definition read_mem i := Call (TwoDisk.Read_Mem i).
Time Definition write_mem i v := Call (TwoDisk.Write_Mem i v).
Time Definition read_disk id i := Call (TwoDisk.Read_Disk id i).
Time Definition write_disk id i v := Call (TwoDisk.Write_Disk id i v).
Time Definition cas i vold vnew := Call (TwoDisk.CAS i vold vnew).
Time
Definition lock i : proc TwoDisk.Op unit :=
  Loop
    (fun _ : unit =>
     x <- cas i 0 1;
     Ret (if nat_eq_dec x 0 then DoneWithOutcome tt else ContinueOutcome tt))%proc
    tt.
Time Definition unlock i : proc TwoDisk.Op unit := write_mem i 0.
