Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqpufcub"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
     proc_spec (@addr_to_block_spec State a) 
       (addr_to_block a) recover abstr).
Hint Resolve addr_to_block_ok: core.
Notation "d [ a |-> b ]" := (diskUpd d a b)
  (at level 12, left associativity).
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
   else
    len0 <- addr_to_block 0;
    _ <- d.write len_addr len0; Ret Initialized).
Definition init := then_init d.init init'.
Definition get_len : proc addr :=
  b <- d.read len_addr; Ret (block_to_addr b).
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
  forall b,
  diskGet d len_addr =?= b -> block_to_addr b = length log.
Definition log_size_ok (d : disk) (log : list block) :=
  diskSize d >= 1 + length log.
Definition log_contents_ok (d : disk) (log : list block) :=
  forall a,
  a < length log -> diskGet d (log_addr a) =?= nth a log block0.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\ log_size_ok d log /\ log_contents_ok d log.
Theorem abstr_length_proj d log :
  log_abstraction d log -> log_length_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Theorem abstr_size_proj d log :
  log_abstraction d log -> log_size_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Theorem abstr_contents_proj d log :
  log_abstraction d log -> log_contents_ok d log.
Proof.
(unfold log_abstraction; intuition).
Qed.
Hint Resolve abstr_length_proj abstr_size_proj abstr_contents_proj:
  core.
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Lemma diskGet_eq_values :
  forall d a b b',
  diskGet d a =?= b ->
  diskGet d a =?= b' -> a < diskSize d -> b = b'.
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
         (apply (@diskGet_eq_values d a b b'); try lia; auto);
         subst
  end.
Ltac step := step_proc.
Theorem log_length_ok_nil d b :
  diskGet d len_addr = Some b ->
  block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H in *; simpl in *; subst).
auto.
Qed.
Theorem log_abstraction_nil d b :
  diskGet d len_addr = Some b ->
  block_to_addr b = 0 -> log_abstraction d nil.
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
(eapply log_abstraction_nil; eauto).
(unfold len_addr).
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
     recovered := fun _ state' => state' = state |}) get_len
    recover d.abstr.
Proof.
(unfold get_len; intros).
step.
step.
eauto.
Qed.
Hint Resolve get_len_ok: core.
Theorem get_len_abstr_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ r = length state;
     recovered := fun _ state' => state' = state |}) get_len
    recover abstr.
Proof.
(apply spec_abstraction_compose).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a as [[] bs]; simpl in *; intuition eauto).
(exists bs; intuition eauto).
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
     post := fun r state' =>
             state' = state /\ nth a state block0 = r;
     recovered := fun _ state' => state' = state |}) 
    (get_at a) recover abstr.
Proof.
(unfold get_at; intros).
(apply spec_abstraction_compose).
(simpl).
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; intros).
(destruct a0 as [_ bs]; simpl in *; intuition eauto).
(simplify; intuition eauto).
(exists bs; intuition eauto).
(unfold log_abstraction in H0; intuition).
(pose proof (H3 a); intuition).
(eapply diskGet_eq_values; eauto).
Qed.
Hint Resolve get_at_ok: core.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe; simpl; intros).
(apply spec_abstraction_compose).
step.
(destruct a as [_ bs]; simpl in *; intuition eauto).
Qed.
Hint Resolve recover_wipe: core.
Lemma firstn_one_more :
  forall (a : nat) (d : list block),
  S a <= length d ->
  firstn a d ++ [nth a d block0] = firstn (S a) d.
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
step.
-
step.
step.
intuition eauto.
{
lia.
}
step.
auto using firstn_one_more.
Qed.
Hint Resolve get_upto_ok: core.
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
(unfold get, get_spec; intros).
step.
step.
(rewrite firstn_all; auto).
Qed.
Theorem log_contents_ok_unchanged d bs a0 b :
  log_size_ok d bs ->
  log_contents_ok d bs ->
  a0 >= length bs -> log_contents_ok (diskUpd d (log_addr a0) b) bs.
Proof.
(unfold log_size_ok, log_contents_ok; intros).
(destruct (a == a0); subst; autorewrite with upd; auto).
(simpl; auto).
Qed.
Theorem log_size_ok_shrink d bs bs' :
  log_size_ok d (bs ++ bs') -> log_size_ok d bs.
Proof.
(unfold log_size_ok; simpl).
(rewrite app_length; intros).
lia.
Qed.
Hint Resolve log_size_ok_shrink: core.
Hint Rewrite app_length : list.
Theorem log_contents_ok_prefix d bs bs' :
  log_contents_ok d (bs ++ bs') -> log_contents_ok d bs.
Proof.
(unfold log_contents_ok; intros).
specialize (H a).
(rewrite app_nth1 in H by lia).
(apply H).
(rewrite app_length; lia).
Qed.
Hint Resolve log_contents_ok_prefix: core.
Theorem log_contents_ok_append d bs b bs' :
  log_size_ok d (bs ++ b :: bs') ->
  log_contents_ok d bs ->
  log_contents_ok (diskUpd d (log_addr (length bs)) b) (bs ++ [b]).
Proof.
(unfold log_contents_ok; intros).
(assert (log_addr (length bs) < diskSize d)).
{
(unfold log_size_ok, log_addr, diskSize in *).
(rewrite app_length in *; simpl in *).
lia.
}
(destruct (a == length bs); subst; autorewrite with upd).
-
(simpl).
(rewrite app_nth2 by lia).
replace (length bs - length bs) with 0 by lia.
reflexivity.
-
(assert (a < length bs)).
{
(rewrite app_length in *; simpl in *; lia).
}
(rewrite app_nth1 by lia).
auto.
Qed.
Hint Resolve log_contents_ok_append: core.
Theorem append_at_ok a bs' :
  proc_spec
    (fun (bs : list block) state =>
     {|
     pre := a = length bs /\
            log_size_ok state (bs ++ bs') /\
            log_contents_ok state bs;
     post := fun r state' =>
             diskGet state' len_addr = diskGet state len_addr /\
             diskSize state' = diskSize state /\
             log_size_ok state' (bs ++ bs') /\
             log_contents_ok state' (bs ++ bs');
     recovered := fun _ state' =>
                  diskGet state' len_addr = diskGet state len_addr /\
                  diskSize state' = diskSize state /\
                  log_contents_ok state' bs |}) 
    (append_at a bs') recover d.abstr.
Proof.
generalize dependent a.
(induction bs'; simpl; intros).
-
step.
intuition eauto.
(rewrite app_nil_r; auto).
-
step.
(intuition eauto; autorewrite with upd; auto).
step.
(exists (a' ++ [a]); intuition eauto; autorewrite with upd list
  in *; eauto).
+
(simpl; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(simpl in *; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(simpl in *; lia).
+
(rewrite <- app_assoc in *; simpl in *; auto).
Qed.
Hint Resolve append_at_ok: core.
Theorem log_abstraction_preserved d bs d' :
  log_abstraction d bs ->
  diskGet d' len_addr = diskGet d len_addr ->
  diskSize d' = diskSize d ->
  log_contents_ok d' bs -> log_abstraction d' bs.
Proof.
(unfold log_abstraction, log_length_ok, log_size_ok; intuition).
-
replace (diskGet d' len_addr) in *.
auto.
-
congruence.
Qed.
Theorem abstr_length_sz_bound d bs :
  log_size_ok d bs -> len_addr < diskSize d.
Proof.
(unfold log_size_ok, len_addr, diskSize).
(intros; lia).
Qed.
Hint Resolve abstr_length_sz_bound: core.
Theorem log_contents_ok_len_change d bs b :
  log_size_ok d bs ->
  log_contents_ok d bs -> log_contents_ok (diskUpd d len_addr b) bs.
Proof.
(unfold log_size_ok, log_contents_ok, len_addr; intros).
(destruct (0 == log_addr a); autorewrite with upd).
-
(exfalso; unfold log_addr in *; lia).
-
auto.
Qed.
Lemma log_abstraction_commit :
  forall bs bs' : list block,
  forall d' : State,
  log_size_ok d' (bs ++ bs') ->
  log_contents_ok d' (bs ++ bs') ->
  forall len_b : block,
  block_to_addr len_b = length bs + length bs' ->
  log_abstraction (diskUpd d' len_addr len_b) (bs ++ bs').
Proof.
(intros).
(assert (len_addr < diskSize d') by eauto).
(unfold log_abstraction; intuition).
-
(unfold log_length_ok in *; intros; autorewrite with upd list in *).
(simpl in *; intuition).
-
(unfold log_size_ok in *; autorewrite with upd list in *).
lia.
-
(apply log_contents_ok_len_change; auto).
Qed.
Hint Resolve log_abstraction_commit: core.
Theorem log_length_ok_unchanged d bs d' :
  log_length_ok d bs ->
  diskGet d' len_addr = diskGet d len_addr -> log_length_ok d' bs.
Proof.
(unfold log_length_ok; intros).
(rewrite H0 in *).
destruct matches.
-
step.
(exists bs; intuition eauto).
{
(unfold log_size_ok; autorewrite with list; auto).
}
{
(exists bs; intuition eauto using log_abstraction_preserved).
}
step.
intuition.
{
(exists bs; eauto using log_abstraction_preserved).
}
step.
intuition.
{
(exists bs; intuition eauto).
(unfold log_abstraction; intuition eauto).
}
{
(exists (bs ++ v); intuition).
}
step.
intuition.
{
(exists (bs ++ v); intuition eauto).
}
{
(exists bs; intuition eauto).
}
