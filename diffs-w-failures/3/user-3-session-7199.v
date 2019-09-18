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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @firstn_length.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Set Printing Width 78.
Definition log_length_ok (d : disk) (log : list block) :=
  forall b, diskGet d len_addr =?= b -> block_to_addr b = length log.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqI1IV5W"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqfLWLGq"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @block.
Timeout 1 Check @firstn_length.
Timeout 1 Check @firstn_length.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Set Printing Width 78.
Theorem log_length_ok_nil d b :
  diskGet d len_addr = Some b -> block_to_addr b = 0 -> log_length_ok d nil.
Proof.
(unfold log_length_ok; intros).
(rewrite H in *; simpl in *; subst).
auto.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqH0Mv0e"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @firstn_length.
Timeout 1 Check @firstn_length.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Set Printing Width 78.
Set Silent.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @firstn_length.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Set Printing Width 78.
Show.
(assert (diskGet nil len_addr = None)).
{
Set Silent.
(apply disk_oob_eq).
Unset Silent.
(simpl; lia).
}
congruence.
-
(unfold log_contents_ok; simpl in *; intuition).
(exfalso; lia).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqRmv5ZP"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
Set Silent.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Unset Silent.
Proof.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @firstn_length.
Timeout 1 Check @firstn_length.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Set Printing Width 78.
Show.
(unfold len_addr).
(autorewrite with upd; auto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqGXgs2S"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
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
Theorem append_at_ok a bs' :
  proc_spec
    (fun (bs : list block) state =>
     {|
     pre := a = length bs /\
            log_size_ok state (bs ++ bs') /\ log_contents_ok state bs;
     post := fun r state' =>
             diskGet state' len_addr = diskGet state len_addr /\
             diskSize state' = diskSize state /\
             log_size_ok state' (bs ++ bs') /\
             log_contents_ok state' (bs ++ bs');
     recovered := fun _ state' =>
                  diskGet state' len_addr = diskGet state len_addr /\
                  diskSize state' = diskSize state /\
                  log_contents_ok state' bs |}) (append_at a bs') recover
    d.abstr.
Proof.
generalize dependent a.
(induction bs'; simpl; intros).
-
step_proc.
intuition eauto.
(rewrite app_nil_r; auto).
-
step_proc.
(intuition eauto; autorewrite with upd; auto).
{
(apply log_contents_ok_unchanged; eauto).
}
(eapply proc_spec_weaken; eauto).
(unfold spec_impl; simpl; intuition).
(exists (a' ++ [a]); intuition eauto; autorewrite with upd list in *; eauto).
+
(simpl; lia).
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(simpl in *; lia).
Unset Silent.
+
admit.
+
(unfold log_size_ok in *; simpl in *).
autorewrite with upd list in *.
(simpl in *; lia).
+
(rewrite <- app_assoc in *; simpl in *; auto).
Admitted.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqF2EXhR"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Unset Silent.
Unset Silent.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @spec_abstraction_compose.
Set Printing Width 78.
Set Silent.
Unset Silent.
Theorem log_abstraction_preserved d bs d' :
  log_abstraction d bs ->
  diskGet d' len_addr = diskGet d len_addr ->
  diskSize d' = diskSize d -> log_contents_ok d' bs -> log_abstraction d' bs.
Proof.
(unfold log_abstraction, log_length_ok, log_size_ok; intuition).
-
replace (diskGet d' len_addr) in *.
auto.
-
congruence.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQxkvg1"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem append_ok :
  forall v, proc_spec (append_spec v) (append v) recover abstr.
Proof.
(unfold append; intros).
(apply spec_abstraction_compose).
step_proc.
(destruct a' as [[] bs]; simpl in *).
intuition eauto.
step_proc.
(descend; intuition eauto).
Set Silent.
Set Silent.
Set Silent.
destruct matches.
-
step_proc.
(descend; intuition eauto).
Unset Silent.
{
(unfold log_size_ok; autorewrite with list; auto).
}
{
Timeout 1 Check @plus_n_O.
Timeout 1 Check @log_contents_ok.
Timeout 1 Check @log_contents_ok.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction_nil.
(exists bs; intuition eauto using log_abstraction_preserved).
}
step_proc.
intuition.
{
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(exists bs; eauto using log_abstraction_preserved).
}
Timeout 1 Check @spec_abstraction_compose.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
Set Silent.
step_proc.
Unset Silent.
intuition.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
{
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
(exists (bs ++ v); intuition).
Timeout 1 Check @addr.
Set Silent.
admit.
Unset Silent.
}
Timeout 1 Check @eq_existT_curried.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @addr.
Set Silent.
{
(exists (bs ++ v); intuition).
admit.
Unset Silent.
}
Timeout 1 Check @spec_abstraction_compose.
step_proc.
Timeout 1 Check @Ascii.nat_ascii_embedding.
intuition.
Timeout 1 Check @eq_existT_curried.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Set Silent.
{
(descend; intuition eauto).
Unset Silent.
Timeout 1 Check @addr.
Set Silent.
admit.
}
{
(descend; intuition eauto).
admit.
Unset Silent.
}
-
Timeout 1 Check @spec_abstraction_compose.
step_proc.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @repeat_length.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Timeout 1 Check @Byte.x10.
Set Printing Width 78.
Show.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Set Printing Width 78.
Show.
intuition eauto.
Admitted.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq6X1HOm"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqB5pbtF"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @rec_wipe_compose.
Timeout 1 Check @reset.
Timeout 1 Check @reset.
Timeout 1 Check @Ascii.nat_ascii_embedding.
(unfold reset; intros).
Timeout 1 Check @app.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
(apply spec_abstraction_compose).
Timeout 1 Check @spec_abstraction_compose.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
step_proc.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @spec_abstraction_compose.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @log_size_ok.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
(destruct a' as [[] bs]; simpl in *).
intuition.
Timeout 1 Check @eq_existT_curried.
Timeout 1 Check @eq_existT_curried.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @div_eucl_th.
Timeout 1 Check @repeat_length.
Set Silent.
{
Unset Silent.
(descend; intuition eauto).
}
Timeout 1 Check @spec_abstraction_compose.
step_proc.
