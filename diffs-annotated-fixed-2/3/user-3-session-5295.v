Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOg5tsD"
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
(descend; intuition eauto).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq37NBx4"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqPfNu2C"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
{
step.
(destruct r; intuition eauto; simplify).
}
(destruct (lt_dec a (diskSize a'))).
-
eauto.
-
simplify.
}
(destruct r; step).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqY8UEJO"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtSHWPa"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
step.
(* Auto-generated comment: Succeeded. *)

