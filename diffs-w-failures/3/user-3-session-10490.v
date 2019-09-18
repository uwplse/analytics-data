Require Import POCS.
Require Import POCS.
Require Import LogAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.
Axiom (addr_to_block : addr -> proc block).
Require Import LogAPI.
Require Import Common.OneDiskAPI.
Axiom (block_to_addr : block -> addr).
Definition addr_to_block_spec State a :
  Specification unit block unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ block_to_addr r = a;
  recovered := fun _ state' => state' = state |}.
Axiom
  (addr_to_block_ok :
     forall State a recover abstr,
     proc_spec (@addr_to_block_spec State a) (addr_to_block a) recover abstr).
Hint Resolve addr_to_block_ok: core.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 12, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 12, left associativity).
Opaque diskGet.
Module Log (d: OneDiskAPI)<: LogAPI.
Definition len_addr : addr := 0.
Definition log_addr a : addr := S a.
Definition init' : proc InitResult :=
  size <- d.size;
  (if lt_dec size 1
   then Ret InitFailed
   else len0 <- addr_to_block 0; _ <- d.write len_addr len0; Ret Initialized).
Definition init := then_init d.init init'.
Definition get_len : proc addr := b <- d.read len_addr; Ret (block_to_addr b).
Definition get_at (a : addr) : proc block := d.read (log_addr a).
Import ListNotations.
Axiom (addr_to_block : addr -> proc block).
Axiom (block_to_addr : block -> addr).
Definition addr_to_block_spec State a :
  Specification unit block unit State :=
  fun (_ : unit) state =>
  {|
  pre := True;
  post := fun r state' => state' = state /\ block_to_addr r = a;
  recovered := fun _ state' => state' = state |}.
Axiom
  (addr_to_block_ok :
     forall State a recover abstr,
     proc_spec (@addr_to_block_spec State a) (addr_to_block a) recover abstr).
Hint Resolve addr_to_block_ok: core.
Module Log (d: OneDiskAPI)<: LogAPI.
Fixpoint get_helper (start : addr) (count : addr) : 
proc (list block) :=
  match count with
  | O => Ret nil
  | S count' =>
      b <- d.read start; l <- get_helper (start + 1) count'; Ret ([b] ++ l)
  end.
Fixpoint get_upto (a : addr) : proc (list block) :=
  match a with
  | 0 => Ret nil
  | S a => b <- get_at a; bs <- get_upto a; Ret (bs ++ [b])
  end.
Definition get : proc (list block) := len <- get_len; get_upto len.
Fixpoint append_at (a : addr) (bs : list block) : 
proc unit :=
  match bs with
  | [] => Ret tt
  | b :: bs => _ <- d.write (log_addr a) b; append_at (S a) bs
  end.
Definition append (bs : list block) : proc bool :=
  size <- d.size;
  len <- get_len;
  (if le_dec (1 + len + length bs) size
   then
    _ <- append_at len bs;
    len_b <- addr_to_block (len + length bs);
    _ <- d.write len_addr len_b; Ret true
   else Ret false).
Definition reset : proc unit :=
  len0 <- addr_to_block 0; d.write len_addr len0.
Definition recover : proc unit := d.recover.
Definition log_length_ok (d : disk) (log : list block) :=
  forall b, diskGet d len_addr =?= b -> block_to_addr b = length log.
Definition log_size_ok (d : disk) (log : list block) :=
  diskSize d >= 1 + length log.
Definition log_contents_ok (d : disk) (log : list block) :=
  forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\ log_size_ok d log /\ log_contents_ok d log.
Definition get : proc (list block) :=
  len <- d.read 0; r <- get_helper 1 (block_to_addr len); Ret r.
Fixpoint append_helper (start : addr) (l : list block) : 
proc unit :=
  match l with
  | nil => Ret tt
  | b :: l' =>
      _ <- d.write start b; _ <- append_helper (start + 1) l'; Ret tt
  end.
Definition append (l : list block) : proc bool :=
  maxlen <- d.size;
  curlenb <- d.read 0;
  (let curlen := block_to_addr curlenb in
   let newlen := curlen + length l in
   if gt_dec (newlen + 1) maxlen
   then Ret false
   else
    _ <- append_helper (curlen + 1) l;
    newlenb <- addr_to_block newlen; _ <- d.write 0 newlenb; Ret true).
Definition reset : proc unit :=
  newlenb <- addr_to_block 0; _ <- d.write 0 newlenb; Ret tt.
Definition init' : proc InitResult :=
  len <- d.size;
  (if len == 0
   then Ret InitFailed
   else newlenb <- addr_to_block 0; _ <- d.write 0 newlenb; Ret Initialized).
Definition init := then_init d.init init'.
Definition recover : proc unit := d.recover.
Definition disk_matches_list (ds : OneDiskAPI.State) 
  (start : addr) (l : list block) : Prop :=
  diskGets ds start (length l) =??= l.
Definition log_abstraction (ds : OneDiskAPI.State) 
  (ls : LogAPI.State) : Prop :=
  diskSize ds > length ls /\
  (exists lblk, diskGet ds 0 =?= lblk /\ block_to_addr lblk = length ls) /\
  disk_matches_list ds 1 ls.
Theorem abstr_length_proj d log :
  log_abstraction d log -> log_length_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Theorem abstr_size_proj d log : log_abstraction d log -> log_size_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Theorem abstr_contents_proj d log :
  log_abstraction d log -> log_contents_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Hint Resolve abstr_length_proj abstr_size_proj abstr_contents_proj: core.
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a =?= b -> diskGet d a =?= b' -> a < diskSize d -> b = b'.
Definition abstr : Abstraction LogAPI.State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 8, left associativity).
Opaque diskGet.
Theorem log_abstraction_nonempty :
  forall disk l, log_abstraction disk l -> diskSize disk <> 0.
Proof.
firstorder.
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
  | H:diskGet ?d ?a =?= ?b, H':diskGet ?d ?a =?= ?b'
    |- _ =>
        assert (b = b') by
         (apply (@diskGet_eq_values d a b b'); try lia; auto); subst
  end.
Ltac step := step_proc.
Theorem log_length_ok_nil d b :
  diskGet d len_addr = Some b -> block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H in *; simpl in *; subst).
auto.
Qed.
Theorem log_abstraction_nil d b :
  diskGet d len_addr = Some b -> block_to_addr b = 0 -> log_abstraction d nil.
Proof.
(unfold log_abstraction; intros).
intuition.
-
eauto using log_length_ok_nil.
-
(unfold log_size_ok).
(destruct d; simpl in *; [  | lia ]).
(assert (diskGet nil len_addr = None)).
{
(apply disk_oob_eq).
(simpl; lia).
}
congruence.
-
(unfold log_contents_ok; simpl in *; intuition).
(exfalso; lia).
Qed.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step.
(destruct (lt_dec r 1)).
-
step.
-
step.
step.
step.
(exists nil; simpl).
(split; auto).
(apply log_abstraction_nil with (b := r0); eauto).
(unfold len_addr).
(autorewrite with upd; auto).
Qed.
Hint Resolve log_abstraction_nonempty: core.
Theorem log_abstraction_init :
  forall disk b,
  block_to_addr b = 0 ->
  diskSize disk <> 0 -> log_abstraction disk [0 |-> b] nil.
Proof.
(unfold log_abstraction; intros).
(autorewrite with upd; simpl; intuition).
Qed.
-
lia.
-
(exists b; intuition).
-
(unfold disk_matches_list; simpl; auto).
Qed.
Hint Resolve log_abstraction_init: core.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
(eapply then_init_compose; eauto).
step_proc.
(destruct (r == 0)).
-
step_proc.
-
step_proc.
step_proc.
step_proc.
(exists nil; intuition).
Qed.
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
(unfold reset).
(apply spec_abstraction_compose; simpl).
step_proc.
(destruct a'; simpl in *; intuition; subst; eauto).
(step_proc; intuition; subst; eauto).
{
(exists nil; intuition).
eauto.
}
(step_proc; intuition; subst; eauto).
{
(exists nil; intuition).
eauto.
}
{
(exists nil; intuition).
eauto.
}
Qed.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a =?= b -> diskGet d a =?= b' -> a < diskSize d -> b = b'.
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
  | H:diskGet ?d ?a =?= ?b, H':diskGet ?d ?a =?= ?b'
    |- _ =>
        assert (b = b') by
         (apply (@diskGet_eq_values d a b b'); try lia; auto); subst
  end.
Lemma disk_matches_state_next :
  forall disk start b blocks,
  disk_matches_list disk start (b :: blocks) ->
  disk_matches_list disk (start + 1) blocks.
Proof.
(unfold disk_matches_list; simpl; intuition).
Qed.
Hint Resolve disk_matches_state_next: core.
Lemma disk_matches_list_first :
  forall disk start b blocks,
  disk_matches_list disk start (b :: blocks) -> diskGet disk start =?= b.
Proof.
(unfold disk_matches_list; simpl; intuition).
Qed.
Definition get_helper_spec start count :
  Specification (list block) (list block) unit State :=
  fun (blocks : list block) state =>
  {|
  pre := disk_matches_list state start blocks /\
         start + count <= diskSize state /\ length blocks = count;
  post := fun r state' => r = blocks /\ state' = state;
  recovered := fun _ state' => state' = state |}.
Theorem get_helper_ok :
  forall count start,
  proc_spec (get_helper_spec start count) (get_helper start count) d.recover
    d.abstr.
Proof.
(induction count; simpl; intros).
-
step_proc.
(simpl in *; intuition).
(destruct a; simpl in *; auto; lia).
-
step_proc.
step_proc.
(simpl in *; intuition).
(destruct a'; simpl in *; try lia).
exists a'.
intuition eauto.
{
lia.
}
step_proc.
(apply disk_matches_list_first in H).
eq_values.
auto.
Qed.
