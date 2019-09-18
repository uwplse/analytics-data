Time From Coq Require Import List.
Time From Coq Require Import List.
Time From Perennial Require Export Lib.
Time From stdpp Require Import gmap.
Time From Perennial Require Export Lib.
Time Module AtomicPair.
Time
Inductive Op : Type -> Type :=
  | Write : forall p : nat * nat, Op unit
  | Read : Op (nat * nat).
Time Definition State : Set := nat * nat.
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Write p => puts (fun _ => p)
          | Read => reads (fun l => l)
          end;
  crash_step := pure tt;
  finish_step := pure tt |}.
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
  initP := fun s => s = (0, 0) |}.
Time End AtomicPair.
Time Module ExMach.
Time Definition size := 1000.
Time Definition addr := nat.
Time
Inductive Op : Type -> Type :=
  | Read_Mem : forall i : addr, Op nat
  | Write_Mem : forall (i : addr) (v : nat), Op unit
  | CAS : forall (i : addr) (vold : nat) (vnew : nat), Op nat
  | Read_Disk : forall i : addr, Op nat
  | Write_Disk : forall (i : addr) (v : nat), Op unit
  | Fail : Op unit.
Time
Record State :=
 mkState {mem_state : gmap addr nat; disk_state : gmap addr nat}.
Time
Definition state_wf s :=
  (\226\136\128 i, is_Some (mem_state s !! i) \226\134\148 i < size)
  \226\136\167 (\226\136\128 i, is_Some (disk_state s !! i) \226\134\148 i < size).
Time
Definition get_default (i : addr) (s : gmap addr nat) : nat :=
  match s !! i with
  | Some n => n
  | None => 0
  end.
Time
Definition set_default (i : addr) (v : nat) (s : gmap addr nat) :
  gmap addr nat := match s !! i with
                   | Some _ => <[i:=v]> s
                   | None => s
                   end.
Time
Definition get_mem (i : addr) : State -> nat :=
  fun s => get_default i (mem_state s).
Time
Definition get_disk (i : addr) : State -> nat :=
  fun s => get_default i (disk_state s).
Time
Definition set_mem (i : addr) (v : nat) : State -> State :=
  fun s =>
  {|
  mem_state := set_default i v (mem_state s);
  disk_state := disk_state s |}.
Time
Definition set_disk (i : addr) (v : nat) : State -> State :=
  fun s =>
  {|
  mem_state := mem_state s;
  disk_state := set_default i v (disk_state s) |}.
Time Import RelationNotations.
Time
Definition cas_rel (i : addr) (vold : nat) (vnew : nat) :
  relation State State nat :=
  v <- reads (get_mem i);
  if nat_eq_dec v vold then puts (set_mem i vnew);; pure v else pure v.
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
Time
Definition init_state :=
  {| mem_state := init_zero; disk_state := init_zero |}.
Time Lemma init_state_wf : state_wf init_state.
Time Proof.
Time (cut (\226\136\128 i : nat, is_Some (init_state.(mem_state) !! i) \226\134\148 i < size)).
Time {
Time (intros; split; trivial).
Time }
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
Time
Definition crash_fun :=
  fun s => {| mem_state := init_zero; disk_state := disk_state s |}.
Time
Definition dynamics : Dynamics Op State :=
  {|
  step := fun T (op : Op T) =>
          match op with
          | Read_Mem i => reads (get_mem i)
          | Write_Mem i v => puts (set_mem i v)
          | Read_Disk i => reads (get_disk i)
          | Write_Disk i v => puts (set_disk i v)
          | CAS i vold vnew => cas_rel i vold vnew
          | Fail => error
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
Time End ExMach.
Time Definition read_mem i := Call (ExMach.Read_Mem i).
Time Definition write_mem i v := Call (ExMach.Write_Mem i v).
Time Definition read_disk i := Call (ExMach.Read_Disk i).
Time Definition write_disk i v := Call (ExMach.Write_Disk i v).
Time Definition cas i vold vnew := Call (ExMach.CAS i vold vnew).
Time
Definition assert (b : bool) :=
  if b then (_ <- Ret (); Ret ())%proc else Call ExMach.Fail.
Time
Definition lock i : proc ExMach.Op unit :=
  Loop
    (fun _ : unit =>
     x <- cas i 0 1;
     Ret (if nat_eq_dec x 0 then DoneWithOutcome tt else ContinueOutcome tt))%proc
    tt.
Time Definition unlock i : proc ExMach.Op unit := write_mem i 0.
