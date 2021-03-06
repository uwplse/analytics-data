Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCAzC0H"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.
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
(simpl).
(intros).
-
(destruct (lt_dec a 2)).
omega.
(rewrite disk_oob_eq; auto).
(rewrite disk_oob_eq; auto).
-
(simpl; omega).
Qed.
Example abst_2_ok :
  remapped_abstraction (BadBlockAPI.mkState [block1; block0; block0] 0)
    [block0; block0].
Proof.
(constructor; auto).
(simpl).
(intros).
-
(destruct (Nat.eq_dec a 1)).
+
subst.
(simpl).
reflexivity.
+
(destruct (lt_dec a 3)).
omega.
(rewrite disk_oob_eq; auto).
(rewrite disk_oob_eq; auto).
-
(simpl).
omega.
Qed.
Example abst_3_ok :
  remapped_abstraction (BadBlockAPI.mkState [block0; block0] 1) [block0].
Proof.
(constructor; auto).
(simpl).
(intros).
-
(destruct (Nat.eq_dec a 1)).
+
(subst; intuition).
+
(destruct a; simpl; intuition).
(destruct a; simpl; intuition).
(rewrite disk_oob_eq; auto).
(simpl; omega).
-
(simpl).
omega.
Qed.
Example abst_4_nok :
  ~ remapped_abstraction (BadBlockAPI.mkState [block0; block0] 5) [block0].
Proof.
intro.
(inversion H; simpl in *).
subst_var.
omega.
Qed.
Example abst_5_nok :
  ~ remapped_abstraction (BadBlockAPI.mkState [block1; block1] 0) [block0].
Proof.
intro.
(inversion H; simpl in *).
subst_var.
(unshelve (especialize Hremap); eauto).
(inversion Hremap).
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
step_proc.
step_proc.
(destruct (lt_dec r0 (diskSize (stateDisk state)))).
step_proc.
(case_eq (diskGet (stateDisk state) (diskSize (stateDisk state) - 1)); intros).
{
exists (diskUpd (diskShrink (stateDisk state)) (stateBadBlock state) b).
(unfold inited_any; intuition idtac).
(constructor; intuition idtac; autorewrite with upd in *; intuition idtac).
-
(rewrite diskShrink_preserves; auto).
(rewrite diskShrink_size; omega).
-
(rewrite diskUpd_eq; auto).
(rewrite diskShrink_size; omega).
-
omega.
}
{
(exfalso; eapply disk_inbounds_not_none; [  | eauto ]; omega).
}
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
(destruct (a == r)).
-
invert_abstraction.
(step_proc; intuition idtac).
(step_proc; intuition idtac).
(step_proc; intuition idtac).
*
replace (diskSize (stateDisk state) - 1) with diskSize s in * by omega.
(exists s; intuition eauto).
(destruct (stateBadBlock state == diskSize s)).
(rewrite disk_oob_eq by omega; auto).
(rewrite <- Hremap by omega; auto).
*
(subst; eexists; intuition eauto).
*
(subst; eexists; intuition eauto).
*
(subst; eexists; intuition eauto).
-
invert_abstraction.
(step_proc; intuition idtac).
(step_proc; intuition idtac).
(exists s; intuition eauto).
(destruct (a == diskSize s); subst).
(rewrite disk_oob_eq by omega; auto).
(rewrite <- Hgoodsec; auto).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYu56MX"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIfzZVn"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(subst; eexists; intuition eauto).
(subst; eexists; intuition eauto).
-
(subst; eauto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqcdwRuk"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coquze9fg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhOZirj"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
replace (diskSize s + 1 - 1) with diskSize s by omega.
(constructor; simpl).
all: (autorewrite with upd; intuition idtac).
(repeat rewrite diskUpd_neq by omega).
eauto.
(repeat rewrite diskUpd_eq by omega; auto).
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
(destruct (lt_dec a (diskSize s))).
(destruct (a == a0); subst).
(repeat rewrite diskUpd_eq by omega; auto).
(repeat rewrite diskUpd_neq by omega; auto).
(repeat rewrite diskUpd_oob_noop by omega).
auto.
(repeat rewrite diskUpd_neq by omega).
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
(eexists; split; eauto).
(rewrite diskUpd_oob_noop; auto).
(invert_abstraction; omega).
(eexists; split; eauto).
(rewrite diskUpd_oob_noop; auto).
(invert_abstraction; omega).
-
(step_proc; intuition subst; eauto).
(destruct (a == r); subst; eauto).
(step_proc; intuition subst; eauto).
(step_proc; intuition subst; eauto).
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
(invert_abstraction; omega).
Qed.
Theorem recover_noop : rec_noop recover abstr no_wipe.
Proof.
(unfold rec_noop).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
eauto.
(destruct a; simpl in *).
(autounfold in *; intuition eauto).
(subst; eauto).
Qed.
End RemappedDisk.
Require Import BadBlockImpl.
Module x:=  RemappedDisk BadBlockDisk.
Print Assumptions x.write_ok.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq1d4zQy"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqN1v4ta"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(* Auto-generated comment: Succeeded. *)

