Require Import POCS.
Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.
Require Import VariablesAPI.
Module RemappedDisk (bd: BadBlockAPI)<: OneDiskAPI.
Import ListNotations.
Definition read (a : addr) : proc block :=
  bs <- bd.getBadBlock;
  (if a == bs
   then len <- bd.size; r <- bd.read (len - 1); Ret r
   else r <- bd.read a; Ret r).
Definition write (a : addr) (b : block) : proc unit :=
  len <- bd.size;
  (if a == len - 1
   then Ret tt
   else
    bs <- bd.getBadBlock;
    (if a == bs
     then _ <- bd.write (len - 1) b; Ret tt
     else _ <- bd.write a b; Ret tt)).
Definition size : proc nat := len <- bd.size; Ret (len - 1).
Definition init' : proc InitResult :=
  len <- bd.size;
  (if len == 0
   then Ret InitFailed
   else
    bs <- bd.getBadBlock;
    (if lt_dec bs len then Ret Initialized else Ret InitFailed)).
Definition init := then_init bd.init init'.
Require Import StatDbAPI.
Module StatDB (v: VarsAPI)<: StatDbAPI.
Import ListNotations.
Definition add (v : nat) : proc unit :=
  sum <- v.read VarSum;
  count <- v.read VarCount;
  _ <- v.write VarSum (sum + v); _ <- v.write VarCount (count + 1); Ret tt.
Definition mean : proc (option nat) :=
  count <- v.read VarCount;
  (if count == 0
   then Ret None
   else sum <- v.read VarSum; Ret (Some (sum / count))).
Definition init' : proc InitResult :=
  _ <- v.write VarCount 0; _ <- v.write VarSum 0; Ret Initialized.
Definition init := then_init v.init init'.
Definition recover : proc unit := v.recover.
Definition statdb_abstraction (vars_state : VariablesAPI.State)
  (statdb_state : StatDbAPI.State) : Prop :=
  StateCount vars_state = length statdb_state /\
  StateSum vars_state = fold_right plus 0 statdb_state.
Definition abstr : Abstraction StatDbAPI.State :=
  abstraction_compose v.abstr {| abstraction := statdb_abstraction |}.
Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 0 0) nil.
Definition recover : proc unit := bd.recover.
Inductive remapped_abstraction (bs_state : BadBlockAPI.State)
(rd_disk : OneDiskAPI.State) : Prop :=
    RemappedAbstraction :
      let bs_disk := stateDisk bs_state in
      let bs_addr := stateBadBlock bs_state in
      forall (Hgoodblocks : True) (Hbadblock : True) 
        (Hbadlast : True)
        (Hgoodsec : forall a,
                    a <> bs_addr /\ a <> diskSize rd_disk ->
                    diskGet bs_disk a = diskGet rd_disk a)
        (Hremap : bs_addr <> diskSize rd_disk ->
                  diskGet bs_disk (diskSize rd_disk) =
                  diskGet rd_disk bs_addr)
        (Hbsok : bs_addr < diskSize bs_disk)
        (Hsize : diskSize bs_disk = diskSize rd_disk + 1),
      remapped_abstraction bs_state rd_disk.
Hint Constructors remapped_abstraction: core.
Definition abstr : Abstraction OneDiskAPI.State :=
  abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.
Example abst_1_ok :
  remapped_abstraction (BadBlockAPI.mkState [block1; block0] 0) [block0].
Proof.
(constructor; auto).
Proof.
(unfold statdb_abstraction; auto).
Qed.
Example abstr_2_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) nil.
Proof.
(unfold statdb_abstraction; simpl).
lia.
-
(simpl).
(intros).
(destruct (lt_dec a 2)).
Qed.
+
intuition lia.
Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 2 3) [1; 2].
Proof.
(unfold statdb_abstraction; simpl).
lia.
+
(rewrite disk_oob_eq; auto).
Qed.
(rewrite disk_oob_eq; auto).
-
(simpl; lia).
Theorem init_ok : init_abstraction init recover abstr inited.
Proof.
(eapply then_init_compose; eauto).
(unfold init').
(step_proc_basic; intros).
exists tt.
(simpl; intuition idtac).
(step_proc_basic; intros).
Qed.
Example abst_2_ok :
  remapped_abstraction (BadBlockAPI.mkState [block1; block0; block0] 0)
    [block0; block0].
Proof.
(constructor; auto).
exists tt.
(simpl; intuition idtac).
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
exists nil.
(unfold statdb_abstraction, inited).
intuition auto.
Qed.
-
(simpl; intros).
(destruct (Nat.eq_dec a 1)).
Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
Proof.
(unfold add).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
(destruct a'; simpl in *; intuition idtac).
+
subst.
(simpl).
reflexivity.
+
(destruct (lt_dec a 3)).
*
intuition lia.
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
*
(rewrite ?disk_oob_eq by auto).
reflexivity.
-
(simpl).
{
(eexists; intuition auto).
lia.
Qed.
Example abst_3_ok :
  remapped_abstraction (BadBlockAPI.mkState [block0; block0] 1) [block0].
Proof.
(constructor; auto).
(unfold statdb_abstraction in *; simpl in *).
intuition lia.
(simpl).
(intros).
-
(destruct (Nat.eq_dec a 1)).
+
(subst; intuition).
+
(destruct a; simpl; intuition).
}
(autounfold in *; intuition).
Qed.
(destruct a; simpl; intuition).
Theorem mean_ok : proc_spec mean_spec mean recover abstr.
Proof.
(unfold mean).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
(destruct a'; simpl in *; intuition idtac).
(exists tt; simpl; intuition idtac).
(destruct (r == 0)).
-
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
2: (autounfold in *; intuition).
(unfold statdb_abstraction in *).
(destruct s; intuition; simpl in *; try congruence).
(rewrite disk_oob_eq; auto).
(exists nil; intuition auto).
-
(step_proc_basic; intros).
(exists tt; simpl; intuition idtac).
(step_proc_basic; intros).
{
eauto.
}
(simpl in *; intuition subst).
2: (autounfold in *; intuition).
(unfold statdb_abstraction in *).
(destruct s; intuition).
(simpl; lia).
(eexists; intuition auto).
Qed.
Example abst_4_nok :
  ~ remapped_abstraction (BadBlockAPI.mkState [block0; block0] 5) [block0].
Proof.
intro.
(inversion H; simpl in *).
subst_var.
lia.
(right; intuition congruence).
Qed.
Example abst_5_nok :
  ~ remapped_abstraction (BadBlockAPI.mkState [block1; block1] 0) [block0].
Proof.
intro.
(inversion H; simpl in *).
subst_var.
(unshelve (especialize Hremap); eauto).
(inversion Hremap).
Qed.
(unshelve (apply block0_block1_differ); eauto).
Qed.
Ltac
 invert_abstraction :=
  match goal with
  | H:remapped_abstraction _ _ |- _ => inversion H; clear H; subst; subst_var
  end.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 0)).
-
step_proc.
-
step_proc.
Theorem recover_wipe : rec_wipe recover abstr no_crash.
Proof.
(unfold rec_wipe).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc_basic; intros).
{
eauto.
}
(destruct a; simpl in *).
(destruct (lt_dec r0 (diskSize (stateDisk state)))).
+
step_proc.
intuition eauto.
(case_eq (diskGet (stateDisk state) (diskSize (stateDisk state) - 1)); intros).
{
exists (diskUpd (diskShrink (stateDisk state)) (stateBadBlock state) b).
(unfold inited_any; split; auto).
(constructor; intuition idtac; autorewrite with upd in *; intuition idtac).
Qed.
End StatDB.
Require Import VariablesImpl.
Module StatDBImpl:=  StatDB Vars.
Print Assumptions StatDBImpl.abstr_2_nok.
Print Assumptions StatDBImpl.abstr_3_ok.
-
(rewrite diskShrink_preserves; auto).
(rewrite diskShrink_size; lia).
-
(rewrite diskUpd_eq; auto).
(rewrite diskShrink_size; lia).
-
lia.
}
{
(exfalso; eapply disk_inbounds_not_none; [  | eauto ]; lia).
}
+
step_proc.
Qed.
Theorem read_ok :
  forall a, proc_spec (OneDiskAPI.read_spec a) (read a) recover abstr.
Proof.
(unfold read).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
(destruct a'; simpl in *; intuition idtac).
{
(subst; eauto).
}
(destruct (a == r)).
-
invert_abstraction.
(step_proc; intuition idtac).
{
(eexists; eauto).
}
(step_proc; intuition idtac).
{
(eexists; eauto).
}
(step_proc; intuition idtac).
{
replace (diskSize (stateDisk state) - 1) with diskSize s in * by lia.
(exists s; repeat split; auto).
(destruct (stateBadBlock state == diskSize s)).
+
(rewrite disk_oob_eq by lia; simpl; auto).
+
(rewrite <- Hremap by eauto; auto).
}
{
(eexists; eauto).
}
-
invert_abstraction.
(step_proc; intuition idtac).
{
(subst; eexists; eauto).
}
(step_proc; intuition idtac).
{
(exists s; split; eauto).
(destruct (a == diskSize s); subst).
+
(rewrite disk_oob_eq by lia; simpl; auto).
+
(rewrite <- Hgoodsec; auto).
}
(subst; eexists; eauto).
Qed.
Theorem remapped_abstraction_diskUpd_remap :
  forall state s v,
  remapped_abstraction state s ->
  remapped_abstraction
    (mkState (diskUpd (stateDisk state) (diskSize (stateDisk state) - 1) v)
       (stateBadBlock state)) (diskUpd s (stateBadBlock state) v).
Proof.
(intros).
invert_abstraction.
(rewrite Hsize).
replace (diskSize s + 1 - 1) with diskSize s by lia.
(constructor; simpl).
all: (autorewrite with upd; intuition idtac).
{
(repeat rewrite diskUpd_neq by lia).
eauto.
}
{
(repeat rewrite diskUpd_eq by lia; auto).
}
Qed.
Theorem remapped_abstraction_diskUpd_noremap :
  forall state s a v,
  remapped_abstraction state s ->
  a <> diskSize (stateDisk state) - 1 ->
  a <> stateBadBlock state ->
  remapped_abstraction
    (mkState (diskUpd (stateDisk state) a v) (stateBadBlock state))
    (diskUpd s a v).
Proof.
(intros).
invert_abstraction.
(constructor; simpl).
all: (autorewrite with upd; intuition idtac).
Print Assumptions StatDBImpl.add_ok.
{
(destruct (lt_dec a (diskSize s))).
-
(destruct (a == a0); subst).
{
(repeat rewrite diskUpd_eq by lia; auto).
}
{
(repeat rewrite diskUpd_neq by lia; auto).
}
-
(repeat rewrite diskUpd_oob_noop by lia).
auto.
}
(repeat rewrite diskUpd_neq by lia).
eauto.
Qed.
Hint Resolve remapped_abstraction_diskUpd_remap: core.
Hint Resolve remapped_abstraction_diskUpd_noremap: core.
Theorem write_ok :
  forall a v, proc_spec (OneDiskAPI.write_spec a v) (write a v) recover abstr.
Proof.
(unfold write).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
(destruct a'; simpl in *; intuition subst; eauto).
Print Assumptions StatDBImpl.mean_ok.
(destruct (a == r - 1); subst).
-
(step_proc; intuition subst).
{
(eexists; split; eauto).
(rewrite diskUpd_oob_noop; auto).
(invert_abstraction; lia).
}
(eexists; split; eauto).
(rewrite diskUpd_oob_noop; auto).
(invert_abstraction; lia).
-
(step_proc; intuition subst; eauto).
(destruct (a == r); subst; eauto).
+
(step_proc; intuition subst; eauto).
(step_proc; intuition subst; eauto).
+
(step_proc; intuition subst; eauto).
(step_proc; intuition subst; eauto).
Qed.
Theorem size_ok : proc_spec OneDiskAPI.size_spec size recover abstr.
Proof.
(unfold diskSize).
(intros).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition subst; eauto).
step_proc.
intuition subst; eauto.
(exists s; split; auto).
(split; auto).
(invert_abstraction; lia).
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
eauto.
(destruct a; simpl in *).
(autounfold in *; intuition eauto).
Qed.
End RemappedDisk.
Require Import BadBlockImpl.
Module x:=  RemappedDisk BadBlockDisk.
Print Assumptions x.write_ok.
