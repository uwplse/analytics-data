Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqW16E8f"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
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
{
(destruct r; step).
-
(destruct r; step).
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
*
(* Auto-generated comment: Succeeded. *)

