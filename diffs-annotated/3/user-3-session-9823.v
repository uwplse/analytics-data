Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsuQtcv"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 0)).
-
step_proc.
-
step_proc.
(destruct (lt_dec r0 (diskSize (stateDisk state)))).
+
step_proc.
(case_eq (diskGet (stateDisk state) (diskSize (stateDisk state) - 1)); intros).
{
exists (diskUpd (diskShrink (stateDisk state)) (stateBadBlock state) b).
(unfold inited_any; split; auto).
(constructor; intuition; autorewrite with upd in *; intuition).
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
(destruct a'; simpl in *; intuition).
{
(subst; eauto).
}
(destruct (a == r)).
-
invert_abstraction.
(step_proc; intuition).
{
(eexists; eauto).
}
(step_proc; intuition).
{
(eexists; eauto).
}
(step_proc; intuition).
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
(step_proc; intuition).
{
(subst; eexists; eauto).
}
(step_proc; intuition).
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
all: (autorewrite with upd; intuition).
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
all: (autorewrite with upd; intuition).
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqm3RL6F"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqxAjoyG"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
