Require Import POCS.
Require Import POCS.
Require Import TwoDiskAPI.
Require Import Common.OneDiskAPI.
Module ReplicatedDisk (td: TwoDiskAPI)<: OneDiskAPI.
Require Import TwoDiskAPI.
Require Import TwoDiskBaseAPI.
Module TwoDisk (b: TwoDiskBaseAPI)<: TwoDiskAPI.
Definition init := b.init.
Definition read := b.read.
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
Theorem missing0_implies_any :
  forall (state : TwoDiskBaseAPI.State) P,
  disk0 state ?|= missing -> disk0 state ?|= P.
Proof.
(destruct state; unfold missing; simpl; intuition auto).
Qed.
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
(destruct r; step).
(destruct r; step).
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
-
(descend; intuition eauto).
{
(destruct (lt_dec a (diskSize a'))).
-
eauto.
-
simplify.
}
step.
(destruct r; intuition eauto; simplify).
-
(destruct r; step).
Qed.
Hint Resolve write_int_ok: core.
Theorem size_int_ok :
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\
            disk1 state ?|= eq d_1 /\ diskSize d_0 = diskSize d_1;
     post := fun r state' =>
             r = diskSize d_0 /\
             r = diskSize d_1 /\
             disk0 state' ?|= eq d_0 /\ disk1 state' ?|= eq d_1;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d_0 /\ disk1 state' ?|= eq d_1 |}) size
    td.recover td.abstr.
Proof.
(unfold size).
step.
(destruct r; step).
(destruct r; step).
Qed.
Hint Resolve size_int_ok: core.
Definition equal_after a (d_0 d_1 : disk) :=
  diskSize d_0 = diskSize d_1 /\
  (forall a', a <= a' -> diskGet d_0 a' = diskGet d_1 a').
Theorem le_eq_or_S_le : forall n m, n <= m -> n = m \/ S n <= m /\ n <> m.
Proof.
(intros).
lia.
Qed.
Theorem equal_after_diskUpd :
  forall a d_0 d_1 b,
  equal_after (S a) d_0 d_1 ->
  equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
Proof.
(unfold equal_after; intuition).
-
(autorewrite with upd; eauto).
-
(apply le_eq_or_S_le in H1; intuition subst).
{
(destruct (lt_dec a' (diskSize d_0)); autorewrite with upd).
+
(assert (a' < diskSize d_1) by congruence; autorewrite with upd; auto).
+
(assert (~ a' < diskSize d_1) by congruence; autorewrite with upd; auto).
}
(autorewrite with upd; eauto).
Qed.
Hint Resolve equal_after_diskUpd: core.
Theorem init_at_ok :
  forall a,
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\
            disk1 state ?|= eq d_1 /\ equal_after a d_0 d_1;
     post := fun _ state' =>
             exists d_0' d_1' : disk,
               disk0 state' ?|= eq d_0' /\
               disk1 state' ?|= eq d_1' /\ equal_after 0 d_0' d_1';
     recovered := fun _ state' => True |}) (init_at a) td.recover td.abstr.
Proof.
(induction a; simpl; intros).
-
step.
-
step.
step.
(destruct r; finish).
+
step.
(destruct r; simplify; finish).
+
step.
(destruct r; finish).
Qed.
Hint Resolve init_at_ok: core.
Theorem sizeInit_ok :
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\ disk1 state ?|= eq d_1;
     post := fun r state' =>
             exists d_0' d_1',
               disk0 state' ?|= eq d_0' /\
               disk1 state' ?|= eq d_1' /\
               match r with
               | Some sz => diskSize d_0' = sz /\ diskSize d_1' = sz
               | None => True
               end;
     recovered := fun _ state' => True |}) sizeInit td.recover td.abstr.
Proof.
(unfold sizeInit).
step.
(destruct r).
-
step.
(destruct r).
+
(destruct (diskSize d_0 == v)).
*
step.
*
step.
+
step.
-
step.
(destruct r).
+
step.
+
step.
Qed.
Hint Resolve sizeInit_ok: core.
Theorem equal_after_0_to_eq :
  forall d_0 d_1, equal_after 0 d_0 d_1 -> d_0 = d_1.
Proof.
(unfold equal_after; intuition).
(eapply disk_ext_eq; intros).
(eapply H0; lia).
Qed.
Theorem equal_after_size :
  forall d_0 d_1,
  diskSize d_0 = diskSize d_1 -> equal_after (diskSize d_0) d_0 d_1.
Proof.
(unfold equal_after; intuition).
(assert (~ a' < diskSize d_0) by lia).
(assert (~ a' < diskSize d_1) by congruence).
(autorewrite with upd; eauto).
Qed.
Hint Resolve equal_after_size: core.
Hint Resolve equal_after_0_to_eq: core.
Theorem init'_ok :
  proc_spec
    (fun '(d_0, d_1) state =>
     {|
     pre := disk0 state ?|= eq d_0 /\ disk1 state ?|= eq d_1;
     post := fun r state' =>
             match r with
             | Initialized =>
                 exists d_0' d_1',
                   disk0 state' ?|= eq d_0' /\
                   disk1 state' ?|= eq d_1' /\ d_0' = d_1'
             | InitFailed => True
             end;
     recovered := fun _ state' => True |}) init' td.recover td.abstr.
Proof.
(unfold init).
step.
(descend; intuition eauto).
(destruct r; step).
step.
Qed.
Hint Resolve init'_ok: core.
Inductive RecStatus :=
  | Continue : _
  | RepairDoneOrFailed : _.
Definition fixup (a : addr) : proc RecStatus :=
  mv0 <- td.read d0 a;
  match mv0 with
  | Working v =>
      mv2 <- td.read d1 a;
      match mv2 with
      | Working v' =>
          if v == v'
          then Ret Continue
          else mu <- td.write d1 a v; Ret RepairDoneOrFailed
      | Failed => Ret RepairDoneOrFailed
      end
  | Failed => Ret RepairDoneOrFailed
  end.
Definition fixup_stub (a : addr) : proc RecStatus := Ret Continue.
Fixpoint recover_at (a : addr) : proc unit :=
  match a with
  | 0 => Ret tt
  | S n =>
      s <- fixup n;
      match s with
      | Continue => recover_at n
      | RepairDoneOrFailed => Ret tt
      end
  end.
Definition Recover : proc unit := sz <- size; _ <- recover_at sz; Ret tt.
Theorem if_lt_dec :
  forall A n m (a a' : A), n < m -> (if lt_dec n m then a else a') = a.
Proof.
(intros).
(destruct (lt_dec n m); auto).
Qed.
Theorem disks_eq_inbounds :
  forall (d : disk) a v v',
  a < diskSize d -> diskGet d a =?= v -> diskGet d a =?= v' -> v = v'.
Proof.
(intros).
(case_eq (diskGet d a); intros).
-
(rewrite H2 in *).
(simpl in *).
congruence.
-
exfalso.
(eapply disk_inbounds_not_none; eauto).
Qed.
Inductive DiskStatus :=
  | FullySynced : _
  | OutOfSync : forall (a : addr) (b : block), _.
Theorem diskUpd_maybe_same :
  forall (d : disk) a b, diskGet d a =?= b -> diskUpd d a b = d.
Proof.
(intros).
(destruct (diskGet d a) eqn:?; simpl in *; subst; autorewrite with upd; auto).
Qed.
Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : upd.
Hint Resolve PeanoNat.Nat.lt_neq: core.
Hint Resolve disks_eq_inbounds: core.
Theorem fixup_equal_ok :
  forall a,
  proc_spec
    (fun d state =>
     {|
     pre := a < diskSize d /\ disk0 state ?|= eq d /\ disk1 state ?|= eq d;
     post := fun r state' => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |})
    (fixup a) td.recover td.abstr.
Proof.
(unfold fixup).
step.
(destruct r; step).
(destruct r; try step).
(destruct (v == v0); subst; try step).
Unshelve.
{
auto.
}
exact (fun _ => True).
Qed.
Theorem fixup_correct_addr_ok :
  forall a,
  proc_spec
    (fun '(d, b) state =>
     {|
     pre := a < diskSize d /\
            disk0 state ?|= eq (diskUpd d a b) /\ disk1 state ?|= eq d;
     post := fun r state' =>
             match r with
             | Continue =>
                 disk0 state' ?|= eq (diskUpd d a b) /\
                 disk1 state' ?|= eq (diskUpd d a b)
             | RepairDoneOrFailed =>
                 disk0 state' ?|= eq (diskUpd d a b) /\
                 disk1 state' ?|= eq (diskUpd d a b) \/
                 disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
             end;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq (diskUpd d a b) \/
                  disk0 state' ?|= eq (diskUpd d a b) /\
                  disk1 state' ?|= eq d \/
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |})
    (fixup a) td.recover td.abstr.
Proof.
(unfold fixup; intros).
step.
(destruct r; try step).
(destruct r; try step).
(destruct (b == v); subst; try step).
step.
(destruct r; simplify; finish).
Qed.
Theorem fixup_wrong_addr_ok :
  forall a,
  proc_spec
    (fun '(d, b, a') state =>
     {|
     pre := a < diskSize d /\
            a' < a /\
            disk0 state ?|= eq (diskUpd d a' b) /\ disk1 state ?|= eq d;
     post := fun r state' =>
             match r with
             | Continue =>
                 disk0 state' ?|= eq (diskUpd d a' b) /\
                 disk1 state' ?|= eq d
             | RepairDoneOrFailed =>
                 disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                 disk0 state' ?|= eq (diskUpd d a' b) /\
                 disk1 state' ?|= eq (diskUpd d a' b)
             end;
     recovered := fun _ state' =>
                  disk0 state' ?|= eq (diskUpd d a' b) /\
                  disk1 state' ?|= eq d \/
                  disk0 state' ?|= eq d /\ disk1 state' ?|= eq d |})
    (fixup a) td.recover td.abstr.
Proof.
(unfold fixup; intros).
step.
(destruct r; try step).
(destruct r; try step).
(destruct (v == v0); subst).
-
step.
-
step.
Unshelve.
{
auto.
}
exact (fun _ => True).
Qed.
Theorem fixup_ok :
  forall a,
  proc_spec
    (fun '(d, s) state =>
     {|
     pre := a < diskSize d /\
            match s with
            | FullySynced => disk0 state ?|= eq d /\ disk1 state ?|= eq d
            | OutOfSync a' b =>
                a' <= a /\
                disk0 state ?|= eq (diskUpd d a' b) /\ disk1 state ?|= eq d
            end;
     post := fun r state' =>
             match s with
             | FullySynced => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
             | OutOfSync a' b =>
                 match r with
                 | Continue =>
                     a' < a /\
                     disk0 state' ?|= eq (diskUpd d a' b) /\
                     disk1 state' ?|= eq d \/
                     disk0 state' ?|= eq (diskUpd d a' b) /\
                     disk1 state' ?|= eq (diskUpd d a' b)
                 | RepairDoneOrFailed =>
                     disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                     disk0 state' ?|= eq (diskUpd d a' b) /\
                     disk1 state' ?|= eq (diskUpd d a' b)
                 end
             end;
     recovered := fun _ state' =>
                  match s with
                  | FullySynced =>
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
                  | OutOfSync a' b =>
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b) \/
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq d \/
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
                  end |}) (fixup a) td.recover td.abstr.
Proof.
(spec_intros; simplify).
(destruct s; intuition eauto).
-
(spec_case fixup_equal_ok; simplify; finish).
-
(apply PeanoNat.Nat.lt_eq_cases in H0; intuition).
+
(spec_case fixup_wrong_addr_ok; simplify; finish).
(repeat apply exists_tuple2; simpl).
exists d,b,a0.
(simplify; finish).
(destruct v; finish).
+
(spec_case fixup_correct_addr_ok; simplify; finish).
exists d,b.
(simplify; finish).
(destruct v; finish).
Restart.
(intros).
step_proc.
(destruct a'; simpl in *).
(destruct d0; intuition idtac).
-
(simplify; finish).
(destruct r; try step).
(destruct r; try step).
(destruct (v == v0); try step).
-
(simplify; finish).
(destruct r; try step).
(destruct r; try step).
(destruct (v == v0); try step).
+
(assert (a0 < a \/ a0 = a) by lia; intuition auto; simplify).
+
intuition eauto.
{
(destruct (a == a0); simplify; finish).
}
step.
(destruct r; try step).
*
(destruct (a == a0); simplify; finish).
*
(destruct (a == a0); simplify; finish).
Unshelve.
{
auto.
}
exact (fun _ => True).
Qed.
Theorem fixup_stub_ok :
  forall a,
  proc_spec
    (fun '(d, s) state =>
     {|
     pre := a < diskSize d /\
            match s with
            | FullySynced => True
            | OutOfSync a' b => True
            end;
     post := fun r state' =>
             match s with
             | FullySynced => True
             | OutOfSync a' b => True
             end;
     recovered := fun _ state' =>
                  match s with
                  | FullySynced => True
                  | OutOfSync a' b => True
                  end |}) (fixup a) td.recover td.abstr.
Proof.
Admitted.
Hint Resolve fixup_ok: core.
Theorem recover_at_ok :
  forall a,
  proc_spec
    (fun '(d, s) state =>
     {|
     pre := a <= diskSize d /\
            match s with
            | FullySynced => disk0 state ?|= eq d /\ disk1 state ?|= eq d
            | OutOfSync a' b =>
                a' < a /\
                disk0 state ?|= eq (diskUpd d a' b) /\ disk1 state ?|= eq d
            end;
     post := fun r state' =>
             match s with
             | FullySynced => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
             | OutOfSync a' b =>
                 disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                 disk0 state' ?|= eq (diskUpd d a' b) /\
                 disk1 state' ?|= eq (diskUpd d a' b)
             end;
     recovered := fun _ state' =>
                  match s with
                  | FullySynced =>
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
                  | OutOfSync a' b =>
                      disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq d \/
                      disk0 state' ?|= eq (diskUpd d a' b) /\
                      disk1 state' ?|= eq (diskUpd d a' b)
                  end |}) (recover_at a) td.recover td.abstr.
Proof.
(induction a; simpl; intros).
-
step.
(destruct s; simplify).
-
step.
(destruct s; simplify).
+
(exists d,FullySynced; simplify; finish).
(destruct r; step).
(exists d,FullySynced; simplify; finish).
lia.
+
(exists d,(OutOfSync a0 b); simplify; finish).
intuition eauto.
{
lia.
}
{
(destruct r; step).
intuition.
*
(exists d,(OutOfSync a0 b); simplify; finish).
lia.
*
(exists (diskUpd d a0 b),FullySynced; simplify; finish).
lia.
}
Qed.
Theorem recover_stub_at_ok :
  forall a,
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => True;
     recovered := fun _ state' => True |}) (recover_at a) td.recover td.abstr.
Proof.
Admitted.
Hint Resolve recover_at_ok: core.
Definition Recover_spec : Specification _ unit unit TwoDiskBaseAPI.State :=
  fun '(d, s) state =>
  {|
  pre := match s with
         | FullySynced => disk0 state ?|= eq d /\ disk1 state ?|= eq d
         | OutOfSync a b =>
             a < diskSize d /\
             disk0 state ?|= eq (diskUpd d a b) /\ disk1 state ?|= eq d
         end;
  post := fun (_ : unit) state' =>
          match s with
          | FullySynced => disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
          | OutOfSync a b =>
              disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
              disk0 state' ?|= eq (diskUpd d a b) /\
              disk1 state' ?|= eq (diskUpd d a b)
          end;
  recovered := fun (_ : unit) state' =>
               match s with
               | FullySynced =>
                   disk0 state' ?|= eq d /\ disk1 state' ?|= eq d
               | OutOfSync a b =>
                   disk0 state' ?|= eq d /\ disk1 state' ?|= eq d \/
                   disk0 state' ?|= eq (diskUpd d a b) /\
                   disk1 state' ?|= eq d \/
                   disk0 state' ?|= eq (diskUpd d a b) /\
                   disk1 state' ?|= eq (diskUpd d a b)
               end |}.
Definition Recover_spec_stub :
  Specification _ unit unit TwoDiskBaseAPI.State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun _ state' => True;
  recovered := fun _ state' => True |}.
Theorem Recover_rok : proc_spec Recover_spec Recover td.recover td.abstr.
Proof.
(unfold Recover, Recover_spec; intros).
(spec_intros; simplify).
(destruct s; simplify).
+
step.
step.
(exists d,FullySynced; simplify; finish).
step.
+
step.
intuition eauto.
{
simplify.
}
step.
(exists d,(OutOfSync a b); simplify; finish).
step.
Qed.
(destruct (le_dec (S a) (diskSize d0))).
Theorem Recover_spec_idempotent : idempotent Recover_spec.
Proof.
(unfold idempotent).
(destruct a as [d st]).
(intuition; simplify).
(destruct st; intuition eauto).
-
destruct_all.
-
(exists d,FullySynced; finish).
-
(exists d,FullySynced; finish).
-
(exists d,(OutOfSync a b); finish).
-
(exists (diskUpd d a b),FullySynced; finish).
-
(rewrite diskUpd_oob_noop by lia).
Qed.
Theorem Recover_ok : proc_loopspec Recover_spec Recover td.recover td.abstr.
Proof.
(eapply idempotent_loopspec; simpl).
-
(apply Recover_rok).
-
(apply Recover_spec_idempotent).
Qed.
destruct_all.
Hint Resolve Recover_ok: core.
Definition recover : proc unit := _ <- td.recover; Recover.
Definition rd_abstraction (state : TwoDiskBaseAPI.State)
  (d : OneDiskAPI.State) : Prop :=
  disk0 state ?|= eq d /\ disk1 state ?|= eq d.
Definition abstr : Abstraction OneDiskAPI.State :=
  abstraction_compose td.abstr {| abstraction := rd_abstraction |}.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(intros).
(eapply then_init_compose; eauto).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct state; simpl in *).
-
(exists (d_0, d_1); simpl; intuition eauto).
(unfold rd_abstraction).
(destruct v; repeat deex; eauto).
-
(exists (d_0, d_0); simpl; intuition eauto).
(unfold rd_abstraction).
(destruct v; repeat deex; eauto).
-
(exists (d_1, d_1); simpl; intuition eauto).
Qed.
(unfold rd_abstraction).
(destruct v; repeat deex; eauto).
Qed.
Theorem read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
Proof.
(intros).
(apply spec_abstraction_compose; simpl).
(eapply compose_recovery; eauto; simplify).
(unfold rd_abstraction in *; descend; intuition eauto).
Theorem size_ok : forall i, proc_spec (size_spec i) (size i) recover abstr.
Proof.
unshelve prim.
(exists (state2, FullySynced); simplify; finish).
Qed.
Theorem write_ok :
  forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
Proof.
(intros).
(apply spec_abstraction_compose; simpl).
(eapply compose_recovery; eauto; simplify).
rename state2 into d.
(unfold rd_abstraction in *; descend; intuition eauto).
-
(exists (d, FullySynced); simplify; intuition eauto).
-
(exists (d, OutOfSync a v); simplify; intuition eauto).
-
(exists (diskUpd d a v, FullySynced); simplify; intuition eauto).
eauto.
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
eauto.
Qed.
End TwoDisk.
Qed.
Theorem size_ok : proc_spec size_spec size recover abstr.
Proof.
(intros).
(apply spec_abstraction_compose; simpl).
(eapply compose_recovery; eauto).
(intros; apply exists_tuple2).
(destruct a; simpl in *).
rename s into d.
(unfold rd_abstraction in *; simplify).
(exists d,d; intuition eauto).
simplify.
(exists d,FullySynced; simplify; finish).
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(eapply rec_wipe_compose; eauto; simpl).
(autounfold; unfold rd_abstraction, Recover_spec; simplify).
(exists state0',FullySynced; intuition eauto).
Qed.
End ReplicatedDisk.
