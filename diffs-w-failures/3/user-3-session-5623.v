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
step_proc.
Qed.
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
