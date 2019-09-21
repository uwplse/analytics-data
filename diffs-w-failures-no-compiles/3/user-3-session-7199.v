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
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\
  (forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0).
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
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
split.
-
eauto using log_length_ok_nil.
-
(simpl; intuition).
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
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
Set Silent.
step_proc.
intuition eauto.
(eexists; intuition eauto).
Unset Silent.
Qed.
Hint Resolve get_len_ok: core.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @BoolTheory.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @get_upto.
Timeout 1 Check @get_upto.
Timeout 1 Check @proc.
Timeout 1 Check @proc.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @Zdiv.Zmod_eq_full.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @unit.
Timeout 1 Check @unit.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @proc_spec.
Timeout 1 Check @True.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @Zdiv.Zmod_eq_full.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @find.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @recover.
Timeout 1 Check @recovered.
Timeout 1 Check @Zdiv.Zmod_eq_full.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Set Printing Width 78.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @get_upto.
Timeout 1 Check @get_upto.
Timeout 1 Check @get_upto.
Timeout 1 Check @recover.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @nth.
Timeout 1 Check @nth.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block0.
Set Printing Width 78.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @get.
Timeout 1 Check @get_at.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Choice.
Timeout 1 Check @d.recover_wipe.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read_ok.
Timeout 1 Check @d.read_ok.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Theorem get_at_ok a :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := a < length state;
     post := fun r state' => state' = state /\ r = nth a state block0;
     recovered := fun _ state' => state' = state |}) 
    (get_at a) recover abstr.
Proof.
(unfold get_at; intros).
(apply spec_abstraction_compose).
(simpl).
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @rec_wipe_compose.
Timeout 1 Check @d.recover_wipe.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @rec_wipe_compose.
Timeout 1 Check @d.recover_wipe.
Timeout 1 Check @d.recover_wipe.
Timeout 1 Check @d.recover_wipe.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Check proc_spec_weaken.
Timeout 1 Check @app.
Timeout 1 Check @app.
Timeout 1 Check @incl_appl.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec_rx.
Timeout 1 Check @proc_spec_weaken.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Set Printing Width 78.
Show.
(eapply proc_spec_weaken; eauto).
Timeout 1 Check @sig.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @spec_abstraction_compose.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_impl.
Timeout 1 Check @spec_impl.
Timeout 1 Check @spec_impl.
Timeout 1 Check @sig.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
(unfold spec_impl; intros).
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
(destruct a0 as [_ bs]; simpl in *; intuition eauto).
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @repeat_length.
(descend; intuition eauto).
Timeout 1 Check @eq_existT_curried.
Timeout 1 Check @eq_existT_curried.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @repeat_length.
(descend; intuition eauto).
Timeout 1 Check @rec_wipe_compose.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @disk.
Timeout 1 Check @nodup.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
autorewrite with upd in *.
