#[global]Set Implicit Arguments.
#[global]Generalizable Variables all.
Axiom (baseOpT : Type -> Type).
CoInductive proc (T : Type) : Type :=
  | BaseOp : forall op : baseOpT T, _
  | Ret : forall v : T, _
  | Bind : forall (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), _.
Require Extraction.
Require Import Arith.
Extraction Language Haskell.
Extract Inductive proc =>  "Proc" [
  "error 'accessing BaseOp'"  "return"  "(>>=)" ]
 "(\fprim fret fbind -> error 'pattern match on proc')".
Axiom (world : Type).
Inductive Result T :=
  | Finished : forall (v : T) (w : world), _
  | Crashed : forall w : world, _.
Arguments Crashed {T} w.
Axiom (base_step : forall T, baseOpT T -> world -> T -> world -> Prop).
Inductive exec : forall T, proc T -> world -> Result T -> Prop :=
  | ExecRet : forall T (v : T) w, exec (Ret v) w (Finished v w)
  | ExecBindFinished :
      forall T T' (p : proc T) (p' : T -> proc T') w v w' r,
      exec p w (Finished v w') -> exec (p' v) w' r -> exec (Bind p p') w r
  | ExecOp :
      forall T (op : baseOpT T) w v w',
      base_step op w v w' -> exec (BaseOp op) w (Finished v w')
  | ExecCrashBegin : forall T (p : proc T) w, exec p w (Crashed w)
  | ExecCrashEnd :
      forall T (p : proc T) w v w',
      exec p w (Finished v w') -> exec p w (Crashed w')
  | ExecBindCrashed :
      forall T T' (p : proc T) (p' : T -> proc T') w w',
      exec p w (Crashed w') -> exec (Bind p p') w (Crashed w').
Axiom (world_crash : world -> world).
Inductive exec_recover R (rec : proc R) (w : world) : R -> world -> Prop :=
  | ExecRecoverExec :
      forall v w', exec rec w (Finished v w') -> exec_recover rec w v w'
  | ExecRecoverCrashDuringRecovery :
      forall w' v w'',
      exec rec w (Crashed w') ->
      exec_recover rec (world_crash w') v w'' -> exec_recover rec w v w''.
Inductive RResult T R :=
  | RFinished : forall (v : T) (w : world), _
  | Recovered : forall (v : R) (w : world), _.
Arguments RFinished {T} {R} v w.
Arguments Recovered {T} {R} v w.
Inductive rexec T R : proc T -> proc R -> world -> RResult T R -> Prop :=
  | RExec :
      forall (p : proc T) (rec : proc R) w v w',
      exec p w (Finished v w') -> rexec p rec w (RFinished v w')
  | RExecCrash :
      forall (p : proc T) (rec : proc R) w w' rv w'',
      exec p w (Crashed w') ->
      exec_recover rec (world_crash w') rv w'' ->
      rexec p rec w (Recovered rv w'').
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
  (at level 60, right associativity).
Arguments Ret {T} v.
Require Import RelationClasses.
Require Import List.
Require Import Helpers.
Set Implicit Arguments.
Axiom (bytes : nat -> Type).
Axiom (bytes_dec : forall n, EqualDec (bytes n)).
Existing Instance bytes_dec.
Axiom (bytes0 : forall n, bytes n).
Axiom (bytes1 : forall n, bytes n).
Axiom (bytes_differ : forall n, n > 0 -> bytes0 n <> bytes1 n).
Definition bnull : bytes 0 := bytes0 0.
Axiom (bappend : forall n1 n2, bytes n1 -> bytes n2 -> bytes (n1 + n2)).
Axiom (bsplit : forall n1 n2, bytes (n1 + n2) -> bytes n1 * bytes n2).
Arguments bsplit {n1} {n2} bs.
Axiom
  (bsplit_bappend :
     forall n1 n2 (b1 : bytes n1) (b2 : bytes n2),
     bsplit (bappend b1 b2) = (b1, b2)).
Fixpoint bsplit_list {n} {m} : bytes (n * m) -> list (bytes m) :=
  match n with
  | O => fun _ => nil
  | S n' =>
      fun bs : bytes (S n' * m) =>
      let (this, rest) := bsplit bs in this :: bsplit_list rest
  end.
Extraction Language Haskell.
Extract Constant bytes =>  "Data.ByteString.ByteString".
Extract Constant bytes_dec =>  "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => 
 "(\n -> Data.ByteString.replicate (Prelude.fromIntegral n) 0)".
Extract Constant bappend => 
 "(\_ _ bs1 bs2 -> Data.ByteString.append bs1 bs2)".
Extract Constant bsplit => 
 "(\n1 _ bs -> Data.ByteString.splitAt (Prelude.fromIntegral n1) bs)".
Definition blockbytes := 1024.
Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Definition block1 : block := bytes1 _.
Theorem block0_block1_differ : block0 <> block1.
Proof.
(apply bytes_differ).
(unfold blockbytes).
lia.
Qed.
Hint Resolve block0_block1_differ: core.
Opaque blockbytes.
Definition disk := list block.
Definition empty_disk : disk := nil.
Definition addr := nat.
Definition diskGet (d : disk) (a : addr) : option block := nth_error d a.
Definition diskSize (d : disk) : nat := length d.
Fixpoint diskUpd d (a : addr) b : disk :=
  match d with
  | nil => nil
  | db :: drest =>
      match a with
      | O => b :: drest
      | S a' => db :: diskUpd drest a' b
      end
  end.
Definition diskShrink (d : disk) : disk := firstn (length d - 1) d.
Fixpoint diskGets (d : disk) (a : addr) (count : nat) : 
list (option block) :=
  match count with
  | O => nil
  | S count' => diskGet d a :: diskGets d (a + 1) count'
  end.
Fixpoint diskUpds (d : disk) (a : addr) (blocks : list block) : disk :=
  match blocks with
  | nil => d
  | b :: blocks' => diskUpd (diskUpds d (a + 1) blocks') a b
  end.
Theorem disk_inbounds_exists :
  forall a d, a < diskSize d -> exists b, diskGet d a = Some b.
Proof.
(unfold diskSize).
(intros).
(case_eq (diskGet d a); intros; eauto).
(apply nth_error_None in H0).
lia.
Qed.
Theorem disk_inbounds_not_none :
  forall a d, a < diskSize d -> diskGet d a = None -> False.
Proof.
(unfold diskSize).
(intros).
(apply nth_error_None in H0).
lia.
Qed.
Theorem disk_none_oob : forall a d, diskGet d a = None -> ~ a < diskSize d.
Proof.
(intros).
(destruct (lt_dec a (diskSize d)); eauto).
(exfalso; eapply disk_inbounds_not_none; eauto).
Qed.
Theorem disk_oob_eq : forall d a, ~ a < diskSize d -> diskGet d a = None.
Proof.
(unfold diskSize).
(induction d; simpl; intros).
-
(induction a; eauto).
-
(destruct a0; simpl).
+
lia.
+
(eapply IHd).
lia.
Qed.
Theorem disk_ext_eq :
  forall d d', (forall a, diskGet d a = diskGet d' a) -> d = d'.
Proof.
(induction d; simpl; intros).
-
(destruct d'; simpl; intros; eauto).
(specialize (H 0); simpl in *).
congruence.
-
(destruct d'; simpl; intros).
+
(specialize (H 0); simpl in *).
congruence.
+
(specialize (H 0) as H'; simpl in H').
(f_equal; try congruence).
(eapply IHd; intros).
(specialize (H (S a0)); simpl in H).
eauto.
Qed.
Theorem disk_ext_inbounds_eq :
  forall d d',
  diskSize d = diskSize d' ->
  (forall a, a < diskSize d -> diskGet d a = diskGet d' a) -> d = d'.
Proof.
(intros).
(apply disk_ext_eq; intros).
(destruct (lt_dec a (diskSize d)); eauto).
(rewrite ?disk_oob_eq by congruence; auto).
Qed.
Theorem diskUpd_eq_some :
  forall d a b0 b,
  diskGet d a = Some b0 -> diskGet (diskUpd d a b) a = Some b.
Proof.
(induction d; simpl; eauto).
-
(destruct a; simpl; intros; congruence).
-
(destruct a0; simpl; intros; eauto).
Qed.
Theorem diskUpd_eq :
  forall d a b, a < diskSize d -> diskGet (diskUpd d a b) a = Some b.
Proof.
(intros).
(apply disk_inbounds_exists in H; deex).
eauto using diskUpd_eq_some.
Qed.
Theorem diskUpd_size : forall d a b, diskSize (diskUpd d a b) = diskSize d.
Proof.
(induction d; simpl; eauto).
(destruct a0; simpl; intros; eauto).
Qed.
Theorem diskUpd_oob_eq :
  forall d a b, ~ a < diskSize d -> diskGet (diskUpd d a b) a = None.
Proof.
(intros).
(apply disk_oob_eq).
(rewrite diskUpd_size; auto).
Qed.
Theorem diskUpd_neq :
  forall d a b a', a <> a' -> diskGet (diskUpd d a b) a' = diskGet d a'.
Proof.
(induction d; simpl; intros; auto).
(destruct a0; simpl).
-
(destruct a'; simpl; try lia; auto).
-
(destruct a'; simpl; auto).
Qed.
Theorem diskUpd_none : forall d a b, diskGet d a = None -> diskUpd d a b = d.
Proof.
(induction d; simpl; intros; auto).
(destruct a0; simpl in *; try congruence).
(rewrite IHd; eauto).
Qed.
Theorem diskUpd_same :
  forall d a b, diskGet d a = Some b -> diskUpd d a b = d.
Proof.
(induction d; simpl; intros; auto).
(destruct a0; simpl in *).
-
congruence.
-
(rewrite IHd; eauto).
Qed.
Theorem diskUpd_twice :
  forall d a b b', diskUpd (diskUpd d a b) a b' = diskUpd d a b'.
Proof.
(induction d; simpl; intros; auto).
(destruct a0; simpl in *).
-
congruence.
-
(rewrite IHd; eauto).
Qed.
Theorem diskUpd_comm :
  forall d a a' b b',
  a <> a' -> diskUpd (diskUpd d a b) a' b' = diskUpd (diskUpd d a' b') a b.
Proof.
(induction d; simpl; intros; auto).
(destruct a0; destruct a'; simpl in *).
-
lia.
-
congruence.
-
congruence.
-
(rewrite IHd; eauto).
Qed.
Theorem diskUpd_comm_lt :
  forall d a a' b b',
  a < a' -> diskUpd (diskUpd d a b) a' b' = diskUpd (diskUpd d a' b') a b.
Proof.
(intros).
(apply diskUpd_comm).
lia.
Qed.
Theorem diskUpd_oob_noop :
  forall d a b, ~ a < diskSize d -> diskUpd d a b = d.
Proof.
(induction d; simpl; intros; auto).
(destruct a0; simpl in *).
-
lia.
-
(rewrite IHd; auto; lia).
Qed.
Theorem diskShrink_size :
  forall d, diskSize d <> 0 -> diskSize (diskShrink d) = diskSize d - 1.
Proof.
(unfold diskSize, diskShrink; intros).
(rewrite firstn_length).
(rewrite min_l; lia).
Qed.
Theorem diskShrink_preserves :
  forall d a,
  a <> diskSize (diskShrink d) -> diskGet (diskShrink d) a = diskGet d a.
Proof.
(unfold diskShrink).
(induction d; simpl; intros; auto).
(destruct d; simpl in *).
-
(destruct a0; try lia; simpl).
(destruct a0; auto).
-
(destruct a0; simpl; auto).
replace (length d - 0) with length d in * by lia.
(rewrite <- IHd; auto).
Qed.
Theorem diskShrink_diskUpd_last :
  forall d a b,
  a >= diskSize d - 1 -> diskShrink (diskUpd d a b) = diskShrink d.
Proof.
(unfold diskShrink; intros).
(destruct (eq_nat_dec a (diskSize d - 1)); subst).
-
clear H.
(rewrite diskUpd_size; unfold diskSize).
(induction d; simpl; auto).
(destruct d; simpl in *; auto).
replace (length d - 0) with length d in * by lia.
(f_equal; auto).
-
(rewrite diskUpd_oob_noop by lia; auto).
Qed.
Theorem diskShrink_diskUpd_notlast :
  forall d a b,
  a < diskSize d - 1 ->
  diskShrink (diskUpd d a b) = diskUpd (diskShrink d) a b.
Proof.
(unfold diskShrink).
(induction d; simpl; auto; intros).
(destruct a0; simpl; auto).
-
(destruct d; simpl; auto).
-
(destruct d; simpl in *; auto).
replace (length d - 0) with length d in * by lia.
(rewrite <- IHd by lia).
(destruct a0; simpl; try rewrite diskUpd_size; unfold diskSize; replace
  (length d - 0) with length d by lia; auto).
Qed.
Hint Rewrite diskUpd_size : disk_size.
Hint Rewrite diskShrink_size using (solve [ auto || lia ]) : disk_size.
Theorem diskUpds_neq :
  forall blocks d a a',
  a' < a \/ a' >= a + length blocks ->
  diskGet (diskUpds d a blocks) a' = diskGet d a'.
Proof.
(induction blocks; simpl; auto; intros).
(rewrite diskUpd_neq by lia).
(rewrite IHblocks; auto).
lia.
Qed.
Theorem diskUpds_size :
  forall blocks d a, diskSize (diskUpds d a blocks) = diskSize d.
Proof.
(induction blocks; simpl; eauto; intros).
(rewrite diskUpd_size; auto).
Qed.
Theorem diskUpds_diskUpd_comm :
  forall blocks d a a' b,
  a' < a \/ a' >= a + length blocks ->
  diskUpd (diskUpds d a blocks) a' b = diskUpds (diskUpd d a' b) a blocks.
Proof.
(induction blocks; simpl; auto; intros).
(rewrite diskUpd_comm by lia).
(rewrite IHblocks; auto).
lia.
Qed.
Theorem diskUpds_diskUpd_after :
  forall blocks d a b,
  diskUpd (diskUpds d a blocks) (a + length blocks) b =
  diskUpds d a (blocks ++ b :: nil).
Proof.
(induction blocks; simpl; auto; intros).
-
(replace (a + 0) with a; auto).
-
(rewrite diskUpd_comm by lia).
(rewrite <- IHblocks).
replace (a0 + S (length blocks)) with a0 + 1 + length blocks by lia.
reflexivity.
Qed.
Theorem diskUpds_diskUpd_before :
  forall blocks d a b,
  diskUpd (diskUpds d (a + 1) blocks) a b = diskUpds d a (b :: blocks).
Proof.
reflexivity.
Qed.
Theorem diskGets_first :
  forall count d a,
  diskGets d a (count + 1) = diskGet d a :: diskGets d (a + 1) count.
Proof.
(intros).
replace (count + 1) with S count by lia.
reflexivity.
Qed.
Theorem diskGets_last :
  forall count d a,
  diskGets d a (count + 1) =
  diskGets d a count ++ diskGet d (a + count) :: nil.
Proof.
(induction count; simpl; intros).
-
(replace (a + 0) with a by lia; auto).
-
(rewrite IHcount).
(replace (a + 1 + count) with a + S count by lia; auto).
Qed.
Theorem diskGets_app :
  forall count0 count1 d a,
  diskGets d a (count0 + count1) =
  diskGets d a count0 ++ diskGets d (a + count0) count1.
Proof.
(induction count0; simpl; auto; intros).
(rewrite IHcount0).
replace (a + 1 + count0) with a + S count0 by lia.
auto.
Qed.
Theorem diskUpd_diskGets_neq :
  forall count d a a0 v0,
  a0 < a \/ a0 > a + count ->
  diskGets (diskUpd d a0 v0) a count = diskGets d a count.
Proof.
(induction count; simpl; intros; auto).
(rewrite diskUpd_neq by lia).
(rewrite IHcount by lia).
auto.
Qed.
Theorem diskUpds_diskGets_neq :
  forall count d a a0 vs,
  a0 + length vs < a \/ a0 >= a + count ->
  diskGets (diskUpds d a0 vs) a count = diskGets d a count.
Proof.
(induction count; simpl; intros; auto).
(rewrite diskUpds_neq by lia).
(rewrite IHcount by lia).
auto.
Qed.
Theorem diskUpds_diskGets_eq :
  forall vs d a,
  a + length vs <= diskSize d ->
  diskGets (diskUpds d a vs) a (length vs) = map Some vs.
Proof.
(induction vs; simpl; intros; auto).
(rewrite diskUpd_eq).
-
(rewrite diskUpd_diskGets_neq by lia).
(rewrite IHvs by lia).
auto.
-
(rewrite diskUpds_size).
lia.
Qed.
#[local]
Ltac solve_disk_size := solve [ autorewrite with disk_size; auto || lia ].
Hint Rewrite diskUpd_eq using solve_disk_size : upd.
Hint Rewrite disk_oob_eq using solve_disk_size : upd.
Hint Rewrite diskUpd_oob_eq using solve_disk_size : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_comm_lt using solve_disk_size : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_same using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_noop using solve_disk_size : upd.
Hint Rewrite diskUpd_twice : upd.
Hint Rewrite diskUpds_neq using solve_disk_size : upd.
Hint Rewrite diskUpds_diskUpd_comm using solve_disk_size : upd.
Hint Rewrite diskUpds_size : upd.
Hint Rewrite diskUpd_diskGets_neq using solve_disk_size : upd.
Hint Rewrite diskUpds_diskGets_neq using solve_disk_size : upd.
Hint Rewrite diskUpds_diskGets_eq using solve_disk_size : upd.
Hint Rewrite diskShrink_size using solve_disk_size : upd.
Hint Rewrite diskShrink_preserves using solve_disk_size : upd.
Hint Rewrite diskShrink_diskUpd_last using solve_disk_size : upd.
Hint Rewrite diskShrink_diskUpd_notlast using solve_disk_size : upd.
