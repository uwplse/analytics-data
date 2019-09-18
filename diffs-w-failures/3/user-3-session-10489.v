Require Import POCS.
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
Qed.
Example abstraction_ok_ptr1 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block1; b1; b2; b3; b4] (b3, b4).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
Qed.
Example abstraction_ok_ptr_same :
  forall b b1 b2, atomic_pair_abstraction [b; b1; b2; b1; b2] (b1, b2).
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
-
