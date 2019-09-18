Require Import POCS.
Require Import POCS.
Require Import POCS.
Require Import POCS.
Require Import VariablesAPI.
Require Import StatDbAPI.
Module StatDB (v: VarsAPI)<: StatDbAPI.
Import ListNotations.
Definition add (v : nat) : proc unit :=
  sum <- v.read VarSum;
  count <- v.read VarCount;
  _ <- v.write VarSum (sum + v); _ <- v.write VarCount (count + 1); Ret tt.
Require Import OneDiskAPI.
Require Import NbdAPI.
Require Import NbdImpl.
Module nbd:=  NbdImpl.
Module NBDServer (d: OneDiskAPI).
Require Import AtomicPairAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.
Module AtomicPair (d: OneDiskAPI)<: AtomicPairAPI.
Definition ptr_a : addr := 0.
Definition data0a : addr := 1.
Definition data1a : addr := 2.
Definition data0b : addr := 3.
Require Import OneDiskAPI.
Require Import BadBlockAPI.
Module RemappedDisk (bd: BadBlockAPI)<: OneDiskAPI.
Import ListNotations.
Definition mean : proc (option nat) :=
  count <- v.read VarCount;
  (if count == 0
   then Ret None
   else sum <- v.read VarSum; Ret (Some (sum / count))).
Definition init' : proc InitResult :=
  _ <- v.write VarCount 0; _ <- v.write VarSum 0; Ret Initialized.
Definition init := then_init v.init init'.
Definition recover : proc unit := v.recover.
Definition statdb_abstraction (vars_state : VariablesAPI.State)
  (statdb_state : StatDbAPI.State) : Prop :=
  StateCount vars_state = length statdb_state /\
  StateSum vars_state = fold_right plus 0 statdb_state.
Definition abstr : Abstraction StatDbAPI.State :=
  abstraction_compose v.abstr {| abstraction := statdb_abstraction |}.
Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 0 0) nil.
Proof.
(unfold statdb_abstraction; auto).
Qed.
Example abstr_2_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) nil.
Proof.
(unfold statdb_abstraction; simpl).
lia.
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
step_proc.
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
-
(simpl read).
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
Hint Constructors remapped_abstraction: core.
Definition abstr : Abstraction OneDiskAPI.State :=
  abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.
Example abst_1_ok :
  remapped_abstraction (BadBlockAPI.mkState [block1; block0] 0) [block0].
Proof.
(constructor; auto).
Qed.
Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 2 3) [1; 2].
Proof.
(unfold statdb_abstraction; simpl).
Qed.
Example abstraction_ok_ptr1 :
  forall b1 b2 b3 b4,
  atomic_pair_abstraction [block1; b1; b2; b3; b4] (b3, b4).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
-
(simpl).
(intros).
(destruct (lt_dec a 2)).
+
intuition lia.
lia.
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
Qed.
Theorem init_ok : init_abstraction init recover abstr inited.
Proof.
(eapply then_init_compose; eauto).
+
(rewrite disk_oob_eq; auto).
(unfold init').
(step_proc_basic; intros).
exists tt.
(simpl; intuition idtac).
(step_proc_basic; intros).
exists tt.
lia.
(rewrite disk_oob_eq; auto).
-
(simpl; lia).
(simpl; intuition idtac).
(step_proc_basic; intros).
eauto.
Qed.
Qed.
Example abst_2_ok :
  remapped_abstraction (BadBlockAPI.mkState [block1; block0; block0] 0)
    [block0; block0].
Proof.
(constructor; auto).
Example abstraction_nok_size2 :
  forall b1 b2, ~ atomic_pair_abstraction [block0; block1] (b1, b2).
-
(simpl; intros).
(destruct (Nat.eq_dec a 1)).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
lia.
+
subst.
(simpl).
reflexivity.
+
(destruct (lt_dec a 3)).
*
intuition lia.
Qed.
Example abstraction_nok_size3 :
  forall b1 b2,
  ~ atomic_pair_abstraction [block0; block1; block0; block1] (b1, b2).
Proof.
(unfold atomic_pair_abstraction; simpl; intuition auto).
*
(rewrite ?disk_oob_eq by auto).
reflexivity.
-
(simpl).
lia.
Qed.
lia.
Example abst_3_ok :
  remapped_abstraction (BadBlockAPI.mkState [block0; block0] 1) [block0].
Proof.
(constructor; auto).
step_proc.
Qed.
Example abstraction_ptr0_invert :
  forall b1 b2 b3 b4 v1 v2,
  atomic_pair_abstraction [block0; b1; b2; b3; b4] (v1, v2) ->
  (v1, v2) = (b1, b2).
(simpl).
(intros).
-
(destruct (Nat.eq_dec a 1)).
+
(subst; intuition).
+
(destruct a; simpl; intuition).
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
(destruct a; simpl; intuition).
step_proc.
step_proc.
exists (block0, block0).
(unfold atomic_pair_abstraction).
(autorewrite with upd; intuition auto).
(rewrite disk_oob_eq; auto).
(simpl; lia).
step_proc.
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
(destruct (diskGet state off); simpl in *; intuition subst; eauto).
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
-
(rewrite diskShrink_preserves; auto).
(rewrite diskShrink_size; lia).
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
-
invert_abstraction.
(step_proc; intuition idtac).
{
(step_proc; intuition idtac).
{
(step_proc; intuition idtac).
+
replace (diskSize (stateDisk state) - 1) with diskSize s in * by lia.
(exists s; repeat split; auto).
(destruct (stateBadBlock state == diskSize s)).
*
(rewrite disk_oob_eq by lia; simpl; auto).
*
(rewrite <- Hremap by eauto; auto).
+
(eexists; eauto).
}
(eexists; eauto).
}
(eexists; eauto).
-
invert_abstraction.
(step_proc; intuition idtac).
{
(step_proc; intuition idtac).
+
(exists s; split; eauto).
(destruct (a == diskSize s); subst).
*
(rewrite disk_oob_eq by lia; simpl; auto).
*
(rewrite <- Hgoodsec; auto).
+
(subst; eexists; eauto).
}
(subst; eexists; eauto).
}
(subst; eauto).
Qed.
Theorem remapped_abstraction_diskUpd_remap :
  forall state s v,
  remapped_abstraction state s ->
  remapped_abstraction
    (mkState (diskUpd (stateDisk state) (diskSize (stateDisk state) - 1) v)
       (stateBadBlock state)) (diskUpd s (stateBadBlock state) v).
Proof.
(intros).
invert_abstraction.
(rewrite Hsize).
replace (diskSize s + 1 - 1) with diskSize s by lia.
(constructor; simpl).
all: (autorewrite with upd; intuition idtac).
{
(repeat rewrite diskUpd_neq by lia).
eauto.
}
{
(repeat rewrite diskUpd_eq by lia; auto).
}
Qed.
Theorem remapped_abstraction_diskUpd_noremap :
  forall state s a v,
  remapped_abstraction state s ->
  a <> diskSize (stateDisk state) - 1 ->
  a <> stateBadBlock state ->
  remapped_abstraction
    (mkState (diskUpd (stateDisk state) a v) (stateBadBlock state))
    (diskUpd s a v).
Proof.
(intros).
invert_abstraction.
(constructor; simpl).
all: (autorewrite with upd; intuition idtac).
Qed.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a ?|= eq b -> diskGet d a ?|= eq b' -> a < diskSize d -> b = b'.
Proof.
(intros).
(destruct (diskGet d a) eqn:?; simpl in *).
congruence.
{
(destruct (lt_dec a (diskSize s))).
-
(destruct (a == a0); subst).
{
(repeat rewrite diskUpd_eq by lia; auto).
}
{
(repeat rewrite diskUpd_neq by lia; auto).
}
-
(repeat rewrite diskUpd_oob_noop by lia).
auto.
}
(repeat rewrite diskUpd_neq by lia).
eauto.
Qed.
Hint Resolve remapped_abstraction_diskUpd_remap: core.
Hint Resolve remapped_abstraction_diskUpd_noremap: core.
Theorem write_ok :
  forall a v, proc_spec (OneDiskAPI.write_spec a v) (write a v) recover abstr.
Proof.
(unfold write).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
(destruct a'; simpl in *; intuition subst; eauto).
(destruct (a == r - 1); subst).
-
(step_proc; intuition subst).
{
(eexists; split; eauto).
(rewrite diskUpd_oob_noop; auto).
(invert_abstraction; lia).
}
(eexists; split; eauto).
(rewrite diskUpd_oob_noop; auto).
(invert_abstraction; lia).
-
(step_proc; intuition subst; eauto).
(destruct (a == r); subst; eauto).
+
(step_proc; intuition subst; eauto).
(step_proc; intuition subst; eauto).
+
(step_proc; intuition subst; eauto).
(step_proc; intuition subst; eauto).
Qed.
Theorem size_ok : proc_spec OneDiskAPI.size_spec size recover abstr.
Proof.
(unfold diskSize).
(intros).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition subst; eauto).
step_proc.
intuition subst; eauto.
(exists s; split; auto).
(split; auto).
(invert_abstraction; lia).
Qed.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe).
(intros).
(apply spec_abstraction_compose; simpl).
(step_proc; intros).
eauto.
(destruct a; simpl in *).
(autounfold in *; intuition eauto).
Qed.
End RemappedDisk.
Require Import BadBlockImpl.
Module x:=  RemappedDisk BadBlockDisk.
Print Assumptions x.write_ok.
