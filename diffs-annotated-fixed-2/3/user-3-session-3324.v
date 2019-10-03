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
(constructor; intuition idtac; auto; intros; autorewrite with upd in *;
  intuition idtac).
all: (rewrite ?diskShrink_preserves; auto).
all: (rewrite ?diskShrink_size; try omega).
all: (rewrite ?diskUpd_eq; auto).
all: (rewrite ?diskShrink_size; omega).
(* Auto-generated comment: Succeeded. *)

