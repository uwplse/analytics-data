Require Import POCS.
Require Import POCS.
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
Require Import AtomicPairAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.
Module AtomicPair (d: OneDiskAPI)<: AtomicPairAPI.
Definition ptr_a : addr := 0.
Definition data0a : addr := 1.
Definition data1a : addr := 2.
Definition data0b : addr := 3.
Definition data1b : addr := 4.
Ltac addr_lia := progress unfold ptr_a, data0a, data1a, data0b, data1b; lia.
Hint Extern 2 (_ <> _ :> addr) => addr_lia: core.
Hint Extern 2 (_ < _) => addr_lia: core.
Definition get : proc (block * block) :=
  ptr <- d.read ptr_a;
  (if ptr == block0
   then b0 <- d.read data0a; b1 <- d.read data1a; Ret (b0, b1)
   else b0 <- d.read data0b; b1 <- d.read data1b; Ret (b0, b1)).
Definition put (p : block * block) : proc unit :=
  ptr <- d.read ptr_a;
  (if ptr == block0
   then
    _ <- d.write data0b (fst p);
    _ <- d.write data1b (snd p); _ <- d.write ptr_a block1; Ret tt
   else
    _ <- d.write data0a (fst p);
    _ <- d.write data1a (snd p); _ <- d.write ptr_a block0; Ret tt).
Require Import TwoDiskAPI.
Require Import TwoDiskBaseAPI.
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
Definition init' : proc InitResult :=
  len <- d.size;
  (if len == 5
   then
    _ <- d.write ptr_a block0;
    _ <- d.write data0a block0; _ <- d.write data1a block0; Ret Initialized
   else Ret InitFailed).
Definition init := then_init d.init init'.
Definition recover : proc unit := d.recover.
Definition atomic_pair_abstraction (ds : OneDiskAPI.State)
  (ps : AtomicPairAPI.State) : Prop :=
  diskSize ds = 5 /\
  (diskGet ds ptr_a ?|= eq block0 ->
   diskGet ds data0a = Some (fst ps) /\ diskGet ds data1a = Some (snd ps)) /\
  (forall b,
   diskGet ds ptr_a ?|= eq b ->
   b <> block0 ->
   diskGet ds data0b = Some (fst ps) /\ diskGet ds data1b = Some (snd ps)).
Example abstraction_ok_ptr0 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block0; b1; b2; b3; b4] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; intuition auto).
Proof.
(intros).
(destruct i; inv_bg; simpl in *; eauto).
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
Example abstraction_ok_ptr1 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block1; b1; b2; b3; b4] (b3, b4).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
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
Qed.
Example abstraction_ok_ptr_same :
  forall b b1 b2, atomic_pair_abstraction [b; b1; b2; b1; b2] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
Qed.
Qed.
Example abstraction_nok_size :
  forall b1 b2, ~ atomic_pair_abstraction [] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
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
lia.
Qed.
Example abstraction_nok_size2 :
  forall b1 b2, ~ atomic_pair_abstraction [block0; block1] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
lia.
Qed.
Example abstraction_nok_size3 :
  forall b1 b2,
  ~ atomic_pair_abstraction [block0; block1; block0; block1] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
lia.
Qed.
Example abstraction_ptr0_invert :
  forall b1 b2 b3 b4 v1 v2,
  atomic_pair_abstraction [block0; b1; b2; b3; b4] (v1, v2) ->
  (v1, v2) = (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition).
congruence.
Qed.
Definition abstr : Abstraction AtomicPairAPI.State :=
  abstraction_compose d.abstr {| abstraction := atomic_pair_abstraction |}.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Opaque diskGet.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 5)).
-
step_proc.
step_proc.
step_proc.
step_proc.
(destruct r; step).
exists (block0, block0).
(unfold atomic_pair_abstraction).
(autorewrite with upd; intuition auto).
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
-
step_proc.
Qed.
(destruct r; step).
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
(unfold get).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition; subst; eauto).
(destruct (r == block0)).
-
(step_proc; intuition eauto).
(step_proc; intuition eauto).
Qed.
(step_proc; intuition eauto).
(unfold atomic_pair_abstraction in *; intuition).
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
exists s.
(destruct s; intuition).
replace (diskGet state data0a) in *.
replace (diskGet state data1a) in *.
(simpl in *; subst; auto).
-
(step_proc; intuition eauto).
(step_proc; intuition eauto).
(step_proc; intuition eauto).
(unfold atomic_pair_abstraction in *; intuition).
exists s.
(destruct s; intuition).
(specialize (H4 r); intuition).
replace (diskGet state data0b) in *.
replace (diskGet state data1b) in *.
(simpl in *; subst; auto).
Qed.
Lemma abstraction_update_b :
  forall state p0 p,
  atomic_pair_abstraction state p0 ->
  diskGet state ptr_a ?|= eq block0 ->
  atomic_pair_abstraction
    state [data0b |-> fst p] [data1b |-> snd p] [ptr_a |-> block1] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition).
(descend; intuition eauto).
Qed.
Lemma abstraction_update_a :
  forall state p0 b p,
  atomic_pair_abstraction state p0 ->
  diskGet state ptr_a ?|= eq b ->
  b <> block0 ->
  atomic_pair_abstraction
    state [data0a |-> fst p] [data1a |-> snd p] [ptr_a |-> block0] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition).
Qed.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a ?|= eq b -> diskGet d a ?|= eq b' -> a < diskSize d -> b = b'.
Proof.
(intros).
(destruct (diskGet d a) eqn:?; simpl in *).
-
congruence.
-
exfalso.
(apply disk_inbounds_not_none in Heqo; eauto).
Qed.
Ltac
 eq_values :=
  match goal with
  | H:diskGet ?d ?a ?|= eq ?b, H':diskGet ?d ?a ?|= eq ?b'
    |- _ =>
        assert (b = b') by (apply (@diskGet_eq_values d a b b'); auto); subst
  end.
Lemma abstraction_partial_update_a :
  forall state p v v',
  atomic_pair_abstraction state p ->
  diskGet state ptr_a ?|= eq block0 ->
  atomic_pair_abstraction state [data0b |-> v] [data1b |-> v'] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition; eq_values; exfalso; eauto).
Qed.
Lemma abstraction_partial_update1_a :
  forall state p v,
  atomic_pair_abstraction state p ->
  diskGet state ptr_a ?|= eq block0 ->
  atomic_pair_abstraction state [data0b |-> v] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition; eq_values; exfalso; eauto).
Qed.
Lemma abstraction_partial_update_b :
  forall state p b v v',
  atomic_pair_abstraction state p ->
  diskGet state ptr_a ?|= eq b ->
  b <> block0 ->
  atomic_pair_abstraction state [data0a |-> v] [data1a |-> v'] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition; eq_values; auto).
-
(specialize (H3 _ _); intuition).
-
(specialize (H3 _ _); intuition).
Qed.
Lemma abstraction_partial_update1_b :
  forall state p b v,
  atomic_pair_abstraction state p ->
  diskGet state ptr_a ?|= eq b ->
  b <> block0 -> atomic_pair_abstraction state [data0a |-> v] p.
Proof.
(unfold atomic_pair_abstraction).
(intros).
(autorewrite with upd; intuition; eq_values; auto).
-
(specialize (H3 _ _); intuition).
-
(specialize (H3 _ _); intuition).
Qed.
Hint Resolve abstraction_update_a abstraction_update_b: core.
Hint Resolve abstraction_partial_update_a abstraction_partial_update_b
  abstraction_partial_update1_a abstraction_partial_update1_b: core.
Theorem put_ok : forall v, proc_spec (put_spec v) (put v) recover abstr.
Proof.
(unfold put; intros).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition; subst; eauto).
(destruct (r == block0)).
-
(step_proc; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
-
(step_proc; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
eauto.
(destruct a; simpl in *).
(autounfold in *; intuition; subst; eauto).
Qed.
End AtomicPair.
(destruct (le_dec (S a) (diskSize d0))).
destruct_all.
