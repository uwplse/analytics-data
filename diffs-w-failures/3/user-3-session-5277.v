Require Import POCS.
Require Import POCS.
Require Import TwoDiskAPI.
Require Import Common.OneDiskAPI.
Module ReplicatedDisk (td: TwoDiskAPI)<: OneDiskAPI.
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
Definition put (p : block * block) : proc unit :=
  ptr <- d.read ptr_a;
  (if ptr == block0
   then
    _ <- d.write data0b (fst p);
    _ <- d.write data1b (snd p); _ <- d.write ptr_a block1; Ret tt
   else
    _ <- d.write data0a (fst p);
    _ <- d.write data1a (snd p); _ <- d.write ptr_a block0; Ret tt).
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
Example abstraction_ok_ptr0 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block0; b1; b2; b3; b4] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; intuition auto).
Qed.
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
Example abstraction_ok_ptr1 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block1; b1; b2; b3; b4] (b3, b4).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
Qed.
Example abstraction_ok_ptr_same :
  forall b b1 b2, atomic_pair_abstraction [b; b1; b2; b1; b2] (b1, b2).
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
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
Qed.
Example abstraction_nok_size :
  forall b1 b2, ~ atomic_pair_abstraction [] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
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
exists (block0, block0).
(unfold atomic_pair_abstraction).
(autorewrite with upd; intuition auto).
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
(step_proc; intuition eauto).
(unfold atomic_pair_abstraction in *; intuition).
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
congruence.
