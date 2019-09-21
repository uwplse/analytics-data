Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIz2qfk"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
Require Import POCS.
Require Import LogAPI.
Require Import Common.OneDiskAPI.
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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Byte.x12.
Timeout 1 Check @Byte.x12.
Set Printing Width 78.
Set Silent.
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 12, left associativity).
Unset Silent.
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 12, left associativity).
Set Silent.
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
  forall b, diskGet d 0 =?= b -> block_to_addr b = length log.
Definition log_size_ok (d : disk) (log : list block) :=
  diskSize d >= 1 + length log.
Definition log_contents_ok (d : disk) (log : list block) :=
  forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\ log_size_ok d log /\ log_contents_ok d log.
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
Theorem log_length_ok_nil d b :
  diskGet d 0 = Some b -> block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H in *; simpl in *; subst).
auto.
Qed.
Theorem log_abstraction_nil d b :
  diskGet d 0 = Some b -> block_to_addr b = 0 -> log_abstraction d nil.
Proof.
(unfold log_abstraction; intros).
intuition.
-
eauto using log_length_ok_nil.
-
(unfold log_size_ok).
(destruct d; simpl in *; [  | lia ]).
(assert (diskGet nil 0 = None)).
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
step_proc.
(destruct (lt_dec r 1)).
-
step_proc.
-
step_proc.
step_proc.
step_proc.
(exists nil; simpl).
(split; auto).
(eapply log_abstraction_nil; eauto).
(autorewrite with upd; auto).
Qed.
Theorem log_abstraction_length d bs :
  log_abstraction d bs -> log_length_ok d bs.
Proof.
(unfold log_abstraction; intuition).
Qed.
Hint Resolve log_abstraction_length: core.
Lemma abstr_get_len :
  forall (bs : list block) (state : State),
  log_length_ok state bs ->
  forall r : block,
  diskGet state len_addr =?= r -> block_to_addr r = length bs.
Proof.
(intros).
(unfold log_length_ok in H).
auto.
Qed.
Hint Resolve abstr_get_len: core.
Theorem get_len_ok :
  proc_spec
    (fun bs state =>
     {|
     pre := log_length_ok state bs /\ log_size_ok state bs;
     post := fun r state' => state' = state /\ r = length bs;
     recovered := fun _ state' => state' = state |}) get_len recover d.abstr.
Proof.
(unfold get_len; intros).
step_proc.
step_proc.
eauto.
Qed.
Hint Resolve get_len_ok: core.
Theorem get_len_abstr_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ r = length state;
     recovered := fun _ state' => state' = state |}) get_len recover abstr.
Proof.
(apply spec_abstraction_compose).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a as [[] bs]; simpl in *; intuition eauto).
(descend; intuition eauto).
Qed.
Hint Resolve get_len_abstr_ok: core.
Theorem log_size_bound d bs a :
  log_size_ok d bs -> a < length bs -> log_addr a < diskSize d.
Proof.
(unfold log_size_ok, log_addr; intros; lia).
Qed.
Hint Resolve log_size_bound: core.
Theorem get_at_ok a :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := a < length state;
     post := fun r state' => state' = state /\ nth a state block0 = r;
     recovered := fun _ state' => state' = state |}) 
    (get_at a) recover abstr.
Proof.
(unfold get_at; intros).
(apply spec_abstraction_compose).
(simpl).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a0 as [_ bs]; simpl in *; intuition eauto).
(descend; intuition eauto).
(descend; intuition eauto).
(unfold log_abstraction in H0; intuition).
(pose proof (H3 a); intuition).
(assert (v = nth a bs block0)).
(eapply diskGet_eq_values; eauto).
auto.
Qed.
Hint Resolve get_at_ok: core.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe; simpl; intros).
(apply spec_abstraction_compose).
step_proc.
(destruct a as [_ bs]; simpl in *; intuition eauto).
Qed.
Hint Resolve recover_wipe: core.
Lemma firstn_one_more :
  forall (a : nat) (d : list block),
  S a <= length d -> firstn a d ++ [nth a d block0] = firstn (S a) d.
Proof.
(intros).
generalize dependent a.
(induction d; simpl; intros).
-
(exfalso; lia).
-
(destruct a0; simpl in *; auto).
(rewrite IHd by lia; auto).
Qed.
Opaque firstn.
Theorem get_upto_ok a :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := a <= length state;
     post := fun r state' => state' = state /\ r = firstn a state;
     recovered := fun _ state' => state' = state |}) 
    (get_upto a) recover abstr.
Proof.
(induction a; simpl).
-
step_proc.
-
step_proc.
step_proc.
intuition eauto.
{
lia.
}
step_proc.
auto using firstn_one_more.
Qed.
Hint Resolve get_upto_ok: core.
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
(unfold get, get_spec; intros).
step_proc.
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; simpl; intuition).
(descend; intuition eauto).
(rewrite firstn_all; auto).
Qed.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @log_contents_ok.
Timeout 1 Check @log_contents_ok.
Timeout 1 Check @log_contents_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Theorem log_contents_ok_unchanged d bs a0 b :
  log_size_ok d bs ->
  log_contents_ok d bs ->
  a0 >= length bs -> log_contents_ok (diskUpd d (log_addr a0) b) bs.
Proof.
(unfold log_size_ok, log_contents_ok; intros).
(destruct (log_addr a == a0); subst; autorewrite with upd; auto).
