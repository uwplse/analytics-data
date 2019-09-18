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
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs)
  (at level 8, left associativity).
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
   then _ <- append_at len bs; Ret true
   else Ret false).
Definition reset : proc unit :=
  len0 <- addr_to_block 0; d.write len_addr len0.
Unset Silent.
Definition recover : proc unit := d.recover.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq1a4Cth"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqntNJJ6"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
Definition log_length_ok (d : disk) (log : list block) :=
  forall b, diskGet d 0 =?= b -> block_to_addr b = length log.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @disk.
Timeout 1 Check @split.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @disk.
Timeout 1 Check @diskSize.
Timeout 1 Check @diskSize.
Timeout 1 Check @diskSize.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @block.
Set Printing Width 78.
Definition log_size_ok (d : disk) (log : list block) :=
  diskSize d >= 1 + length log.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZIyDu2"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqFam0Pk"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @disk.
Timeout 1 Check @block.
Timeout 1 Check @split.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Definition log_contents_ok (d : disk) (log : list block) :=
  forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCfEuGO"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtTL5Ao"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\ log_size_ok d log /\ log_contents_ok d log.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq6dWtdM"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqP8jZBW"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @BoolTheory.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @log_length_ok.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Theorem abstr_length_proj d log :
  log_abstraction d log -> log_length_ok d log.
Proof.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @log_abstraction.
Timeout 1 Check @Ascii.nat_ascii_embedding.
(unfold log_abstraction; intuition).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqAKvZc6"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
Qed.
Unset Silent.
Theorem abstr_size_proj d log : log_abstraction d log -> log_size_ok d log.
Proof.
(unfold log_abstraction; intuition).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlD3ueZ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
Qed.
Theorem abstr_contents_proj d log :
  log_abstraction d log -> log_contents_ok d log.
Proof.
Unset Silent.
(unfold log_abstraction; intuition).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsf4cme"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Timeout 1 Check @RExec.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @abstr_length_proj.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @abstr_size_proj.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Hint Resolve abstr_length_proj abstr_size_proj abstr_contents_proj: core.
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqzdr0VX"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqg1GM8y"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
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
Set Silent.
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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
intuition.
-
eauto using log_length_ok_nil.
-
Timeout 1 Check @sig.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Set Printing Width 78.
Show.
(unfold log_size_ok).
Timeout 1 Check @split.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @disk.
Timeout 1 Check @diskSize.
Timeout 1 Check @diskSize.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @sig.
Timeout 1 Check @Tauto.A.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @split.
Set Printing Width 78.
Show.
(destruct d; simpl in *; [  | lia ]).
Timeout 1 Check @app.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @disk.
Timeout 1 Check @diskGet.
Timeout 1 Check @diskGet.
Timeout 1 Check @diskGet.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @diskGet.
Timeout 1 Check @diskGet.
Timeout 1 Check @diskGet.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @diskSize.
Timeout 1 Check @diskSize.
Timeout 1 Check @diskSize.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(assert (diskGet nil 0 = None)).
Set Silent.
{
(apply disk_oob_eq).
Unset Silent.
(simpl; lia).
}
congruence.
-
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(unfold log_contents_ok; simpl in *; intuition).
(exfalso; lia).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqevmimY"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
Set Silent.
(eapply then_init_compose; eauto).
Unset Silent.
step_proc.
(destruct (lt_dec r 1)).
-
Set Silent.
step_proc.
-
step_proc.
step_proc.
step_proc.
(exists nil; simpl).
(split; auto).
(eapply log_abstraction_nil; eauto).
(autorewrite with upd; auto).
Unset Silent.
Qed.
Theorem log_abstraction_length d bs :
  log_abstraction d bs -> log_length_ok d bs.
Proof.
(unfold log_abstraction; intuition).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqxccwXu"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
Set Silent.
Hint Resolve log_abstraction_length: core.
Unset Silent.
Lemma abstr_get_len :
  forall (bs : list block) (state : State),
  log_length_ok state bs ->
  forall r : block,
  diskGet state len_addr =?= r -> block_to_addr r = length bs.
Proof.
(intros).
(unfold log_length_ok in H).
auto.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqux8HOE"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Set Silent.
Hint Resolve abstr_get_len: core.
Unset Silent.
Set Silent.
Theorem get_len_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' => state' = state /\ r = length state;
     recovered := fun _ state' => state' = state |}) get_len recover abstr.
Proof.
(unfold get_len; intros).
(apply spec_abstraction_compose).
step_proc.
(destruct a' as [_ bs]; simpl in *; intuition eauto).
step_proc.
intuition eauto.
(eexists; intuition eauto).
Qed.
Unset Silent.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Timeout 1 Check @forallb.
Timeout 1 Check @forallb.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Theorem log_size_bound d bs a :
  log_size_ok d bs -> a < length bs -> log_addr a < diskSize d.
Proof.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @split.
(unfold log_size_ok, log_addr; intros; lia).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWKTqVB"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Timeout 1 Check @Ret.
Timeout 1 Check @block.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @log_size_ok.
Timeout 1 Check @spec_abstraction_compose.
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
Set Silent.
Set Silent.
(unfold spec_impl; intros).
Unset Silent.
(destruct a0 as [_ bs]; simpl in *; intuition eauto).
Set Silent.
(descend; intuition eauto).
Unset Silent.
(descend; intuition eauto).
(unfold log_abstraction in H0; intuition).
(pose proof (H3 a); intuition).
(assert (v = nth a bs block0)).
(eapply diskGet_eq_values; eauto).
Timeout 1 Check @Tauto.A.
auto.
Add Search Blacklist "Raw" "Proofs".
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ret.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @get_at.
Timeout 1 Check @get_at_ok.
Timeout 1 Check @get_at_ok.
Timeout 1 Check @spec_abstraction_compose.
Set Printing Width 78.
Hint Resolve get_at_ok: core.
Set Silent.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
(unfold rec_wipe; simpl; intros).
(apply spec_abstraction_compose).
step_proc.
(destruct a as [_ bs]; simpl in *; intuition eauto).
Qed.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @find.
Timeout 1 Check @firstn.
Timeout 1 Check @firstn.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Lemma firstn_one_more :
  forall (a : nat) (d : list block),
  S a <= length d -> firstn a d ++ [nth a d block0] = firstn (S a) d.
Proof.
Timeout 1 Check @Ascii.nat_ascii_embedding.
(intros).
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @find.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Nat.induction.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Nat.induction.
Timeout 1 Check @Nat.induction.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(induction d; simpl in *).
-
Timeout 1 Check @split.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(exfalso; lia).
-
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @sig.
Timeout 1 Check @Ascii.nat_ascii_embedding.
(destruct d; simpl in *).
Timeout 1 Check @split.
Timeout 1 Check @Ascii.nat_ascii_embedding.
(inversion H).
