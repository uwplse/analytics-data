Require Import POCS.
Require Import POCS.
Require Import OneDiskAPI.
Require Import NbdAPI.
Require Import NbdImpl.
Module nbd:=  NbdImpl.
Require Import TwoDiskAPI.
Require Import TwoDiskBaseAPI.
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
Module TwoDisk (b: TwoDiskBaseAPI)<: TwoDiskAPI.
Definition init := b.init.
Definition read := b.read.
Definition write := b.write.
Definition size := b.size.
Definition recover := b.recover.
Definition abstr := b.abstr.
Ltac
 inv_step :=
  match goal with
  | H:op_step _ _ _ _
    |- _ => inversion H; subst; clear H; repeat sigT_eq; safe_intuition
  end.
Ltac
 inv_bg :=
  match goal with
  | H:bg_failure _ _ |- _ => inversion H; subst; clear H
  end.
Theorem maybe_holds_stable :
  forall state state' F0 F1 i,
  get_disk (other i) state ?|= F0 ->
  get_disk i state ?|= F1 ->
  bg_failure state state' ->
  get_disk (other i) state' ?|= F0 /\ get_disk i state' ?|= F1.
Proof.
(intros).
(destruct i; inv_bg; simpl in *; eauto).
step_proc.
-
(simpl read).
Qed.
Ltac
 cleanup :=
  repeat
   match goal with
   | |- forall _, _ => intros
   | |- _ /\ _ => split; [ solve [ eauto || congruence ] |  ]
   | |- _ /\ _ => split; [  | solve [ eauto || congruence ] ]
   | H:Working _ = Working _ |- _ => inversion H; subst; clear H
   | H:bg_failure _ _
     |- _ =>
         eapply maybe_holds_stable in H;
          [  | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
   | H:_ ?|= eq _, H':_ = Some _
     |- _ => pose proof (holds_some_inv_eq _ H' H); clear H
   | H:?A * ?B |- _ => destruct H
   | H:DiskResult _ |- _ => destruct H
   | _ => deex
   | _ => destruct_tuple
   | _ => progress unfold pre_step in *
   | _ => progress autounfold in *
   | _ => progress simpl in *
   | _ => progress subst
   | _ => progress safe_intuition
   | _ => solve [ eauto ]
   | _ => congruence
   | _ =>
       inv_step
   | H:context [ match ?expr with
                 | _ => _
                 end ]
     |- _ => destruct expr eqn:?; [  | solve [ repeat cleanup ] ]
   | H:context [ match ?expr with
                 | _ => _
                 end ]
     |- _ => destruct expr eqn:?; [ solve [ repeat cleanup ] |  ]
   end.
Ltac
 prim :=
  intros; eapply proc_spec_weaken; [ eauto | unfold spec_impl ]; eexists;
   intuition eauto; cleanup; intuition eauto; cleanup.
Hint Resolve holds_in_some_eq: core.
Hint Resolve holds_in_none_eq: core.
Hint Resolve pred_missing: core.
Hint Unfold combined_step: core.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
eauto.
Qed.
Theorem read_ok :
  forall i a, proc_spec (read_spec i a) (read i a) recover abstr.
Proof.
(unshelve prim; eauto).
step_proc.
step_proc.
step_proc.
(rewrite bsplit_bappend).
intuition subst; eauto.
+
(destruct (diskGet state off); simpl in *; intuition subst; eauto).
+
(replace (S off) with off + 1 by lia; auto).
Qed.
Qed.
Ltac
 destruct_all :=
  repeat
   match goal with
   | _ => solve
   [ auto ]
   | i:diskId |- _ => destruct i
   | |-
     context [ match ?s with
               | BothDisks _ _ => _
               | OnlyDisk0 _ => _
               | OnlyDisk1 _ => _
               end ] => destruct s
   | _ => simpl in *
   end.
Theorem write_ok :
  forall i a v, proc_spec (write_spec i a v) (write i a v) recover abstr.
Proof.
(unshelve prim; eauto; try (solve [ destruct_all ])).
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
+
specialize (IHblocks (off + 1)).
step_proc.
intuition subst; eauto.
*
(f_equal; lia).
*
(repeat deex).
(exists (S nwritten); simpl).
(f_equal; lia).
+
(exists 0; simpl; auto).
+
(exists 1; simpl; auto).
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
(destruct (le_dec (S a) (diskSize d0))).
destruct_all.
