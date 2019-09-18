Require Import POCS.
Require Import POCS.
Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.
Require Import OneDiskAPI.
Require Import NbdAPI.
Require Import NbdImpl.
Module nbd:=  NbdImpl.
Module NBDServer (d: OneDiskAPI).
Fixpoint read (off : nat) n : proc (bytes (n * blockbytes)) :=
  match n with
  | 0 => Ret bnull
  | S n => b <- d.read off; rest <- read (off + 1) n; Ret (bappend b rest)
  end.
Fixpoint write (off : nat) (bl : list (bytes blockbytes)) : 
proc unit :=
  match bl with
  | nil => Ret tt
  | b :: bl' => _ <- d.write off b; write (off + 1) bl'
  end.
Require Import TwoDiskAPI.
Require Import Common.OneDiskAPI.
Module ReplicatedDisk (td: TwoDiskAPI)<: OneDiskAPI.
Definition read (a : addr) : proc block :=
  mv0 <- td.read d0 a;
  match mv0 with
  | Working v => Ret v
  | Failed =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v => Ret v
      | Failed => Ret block0
      end
  end.
Definition read_stub (a : addr) : proc block := Ret block0.
Definition write (a : addr) (b : block) : proc unit :=
  _ <- td.write d0 a b; _ <- td.write d1 a b; Ret tt.
Definition size : proc nat :=
  msz <- td.size d0;
  match msz with
  | Working sz => Ret sz
  | Failed =>
      msz <- td.size d1;
      match msz with
      | Working sz => Ret sz
      | Failed => Ret 0
      end
  end.
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
Theorem read_ok :
  forall n off,
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ read_match state off n r;
     recovered := fun _ state' => state' = state |}) 
    (read off n) d.recover d.abstr.
Proof.
(induction n; intros).
-
(simpl).
step_proc.
-
(simpl read).
Definition sizeInit : proc (option nat) :=
  sz1 <- td.size d0;
  sz2 <- td.size d1;
  match sz1 with
  | Working sz1 =>
      match sz2 with
      | Working sz2 => if sz1 == sz2 then Ret (Some sz1) else Ret None
      | Failed => Ret (Some sz1)
      end
  | Failed =>
      match sz2 with
      | Working sz2 => Ret (Some sz2)
      | Failed => Ret None
      end
  end.
Fixpoint init_at (a : nat) : proc unit :=
  match a with
  | 0 => Ret tt
  | S a => _ <- td.write d0 a block0; _ <- td.write d1 a block0; init_at a
  end.
Definition init' : proc InitResult :=
  size <- sizeInit;
  match size with
  | Some sz => _ <- init_at sz; Ret Initialized
  | None => Ret InitFailed
  end.
Definition init := then_init td.init init'.
Theorem exists_tuple2 :
  forall A B (P : A * B -> Prop), (exists a b, P (a, b)) -> exists p, P p.
Proof.
(intros).
(repeat deex; eauto).
Hint Constructors remapped_abstraction: core.
Definition abstr : Abstraction OneDiskAPI.State :=
  abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.
Example abst_1_ok :
  remapped_abstraction (BadBlockAPI.mkState [block1; block0] 0) [block0].
Proof.
(constructor; auto).
Qed.
Tactic Notation "eexist_tuple" ident(a) ident(b) :=
 (match goal with
  | |- exists _ : ?aT * ?bT, _ =>
        let a := fresh a in
        let b := fresh b in
        evar ( a : aT ); evar ( b : bT ); exists (a, b); subst a; subst b
  end).
Ltac
 simplify :=
  repeat
   match goal with
   | |- forall _, _ => intros
   | _ => deex
   | _ =>
       destruct_tuple
   | u:unit |- _ => destruct u
   | |- _ /\ _ => split; [ solve [ auto ] |  ]
   | |- _ /\ _ => split; [  | solve [ auto ] ]
   | |- exists _ : disk * (disk -> Prop), _ => eexist_tuple d F
   | |- exists _ : disk * disk, _ => eexist_tuple d_0 d_1
   | |- exists _ : disk * _, _ => apply exists_tuple2
   | _ => progress simpl in *
   | _ => progress safe_intuition
   | _ => progress subst
   | _ => progress autorewrite with upd in *
   end.
Ltac
 finish :=
  repeat
   match goal with
   | _ => solve_false
   | _ => congruence
   | _ => solve [ intuition eauto; try congruence ]
   | _ =>
       descend; intuition eauto;
        lazymatch goal with
        | |- proc_spec _ _ _ _ => idtac
        | _ => fail
        end
   end.
Ltac step := step_proc; simplify; finish.
Theorem both_disks_not_missing :
  forall state : TwoDiskBaseAPI.State,
  disk0 state ?|= missing -> disk1 state ?|= missing -> False.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Qed.
Hint Resolve both_disks_not_missing: false.
-
(simpl).
(intros).
(destruct (lt_dec a 2)).
+
intuition lia.
Theorem missing0_implies_any :
  forall (state : TwoDiskBaseAPI.State) P,
  disk0 state ?|= missing -> disk0 state ?|= P.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Qed.
Theorem missing1_implies_any :
  forall (state : TwoDiskBaseAPI.State) P,
  disk1 state ?|= missing -> disk1 state ?|= P.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Qed.
Hint Resolve missing0_implies_any: core.
Hint Resolve missing1_implies_any: core.
Theorem read_int_ok :
  forall a,
  proc_spec
    (fun d state =>
     {|
     pre := disk0 state ?|= eq d /\ disk1 state ?|= eq d;
     post := fun r state' =>
             diskGet d a =?= r /\
             disk0 state' ?|= eq d /\ disk1 state' ?|= eq d;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |}) 
    (read a) td.recover td.abstr.
Proof.
(unfold read).
step.
+
(rewrite disk_oob_eq; auto).
(rewrite disk_oob_eq; auto).
-
(simpl; lia).
Qed.
Example abst_2_ok :
  remapped_abstraction (BadBlockAPI.mkState [block1; block0; block0] 0)
    [block0; block0].
Proof.
(constructor; auto).
-
(simpl; intros).
(destruct (Nat.eq_dec a 1)).
+
subst.
(simpl).
reflexivity.
+
(destruct (lt_dec a 3)).
*
intuition lia.
*
(rewrite ?disk_oob_eq by auto).
reflexivity.
-
(simpl).
lia.
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
step_proc.
(destruct a; simpl; intuition).
(rewrite disk_oob_eq; auto).
(destruct r; step).
step_proc.
(simpl; lia).
Qed.
Example abst_4_nok :
  ~ remapped_abstraction (BadBlockAPI.mkState [block0; block0] 5) [block0].
Proof.
intro.
(inversion H; simpl in *).
subst_var.
lia.
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
(constructor; intuition idtac; autorewrite with upd in *; intuition idtac).
step_proc.
(rewrite bsplit_bappend).
intuition subst; eauto.
(destruct r; step).
+
(destruct (diskGet state off); simpl in *; intuition subst; eauto).
+
(replace (S off) with off + 1 by lia; auto).
Qed.
Qed.
Hint Resolve read_int_ok: core.
Theorem write_int_ok :
  forall a b,
  proc_spec
    (fun d state =>
     {|
     pre := disk0 state ?|= eq d /\ disk1 state ?|= eq d;
     post := fun r state' =>
             r = tt /\
             disk0 state' ?|= eq (diskUpd d a b) /\
             disk1 state' ?|= eq (diskUpd d a b);
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                  a < diskSize d /\
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq d \/
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b) |}) 
    (write a b) td.recover td.abstr.
Proof.
(unfold write).
step.
(destruct r; step).
Theorem write_ok :
  forall blocks off,
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => r = tt /\ state' = write_upd state off blocks;
     recovered := fun _ state' =>
                  exists nwritten,
                    state' = write_upd state off (firstn nwritten blocks) |})
    (write off blocks) d.recover d.abstr.
Proof.
(induction blocks; intros).
-
(simpl).
step_proc.
intuition eauto.
(exists 0; simpl; eauto).
-
(simpl write).
step_proc.
intuition eauto.
{
(exists 0; simpl; auto).
}
{
(exists 1; simpl; auto).
}
specialize (IHblocks (off + 1)).
step_proc.
intuition subst; eauto.
+
(f_equal; lia).
+
(repeat deex).
(exists (S nwritten); simpl).
(f_equal; lia).
Qed.
CoFixpoint handle  : proc unit :=
  req <- nbd.getRequest;
  match req with
  | Read h off blocks =>
      data <- read off blocks;
      _ <-
      nbd.sendResponse {| rhandle := h; error := ESuccess; data := data |};
      handle
  | Write h off _ dat =>
      _ <- write off (bsplit_list dat);
      _ <-
      nbd.sendResponse {| rhandle := h; error := ESuccess; data := bnull |};
      handle
  | Flush h =>
      _ <-
      nbd.sendResponse {| rhandle := h; error := ESuccess; data := bnull |};
      handle
  | UnknownOp h =>
      _ <-
      nbd.sendResponse {| rhandle := h; error := EInvalid; data := bnull |};
      handle
  | Disconnect => Ret tt
  end.
Definition serverLoop : proc unit := _ <- nbd.recover; _ <- d.recover; handle.
Definition size : proc nat := d.size.
Definition init := then_init nbd.init d.init.
End NBDServer.
{
(descend; intuition eauto).
{
step.
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
(destruct (a == r)).
