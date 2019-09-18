Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqC9Uqvm"
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
Unset Silent.
Import ListNotations.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqB5MAsu"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXvoZpF"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Module Log (d: OneDiskAPI)<: LogAPI.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Set Printing Width 78.
Definition len_addr : addr := 0.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqvP75sv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqdw5bof"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @block.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Definition log_addr a : addr := S a.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqt5ZCBD"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq7wi6k6"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @repeat_length.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @Ret.
Timeout 1 Check @In.
Timeout 1 Check @Initialized.
Timeout 1 Check @Initialized.
Timeout 1 Check @Initialized.
Timeout 1 Check @Initialized.
Timeout 1 Check @Initialized.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @addr_to_block.
Timeout 1 Check @repeat_length.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Timeout 1 Check @sig.
Timeout 1 Check @d.size.
Timeout 1 Check @d.size.
Timeout 1 Check @d.size.
Timeout 1 Check @d.size.
Timeout 1 Check @sig.
Timeout 1 Check @d.size.
Timeout 1 Check @repeat_length.
Timeout 1 Check @Ret.
Timeout 1 Check @In.
Timeout 1 Check @Init.Nat.t.
Timeout 1 Check @InitFailed.
Timeout 1 Check @InitFailed.
Timeout 1 Check @InitFailed.
Timeout 1 Check @InitFailed.
Timeout 1 Check @InitFailed.
Timeout 1 Check @lel.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @repeat_length.
Timeout 1 Check @then_init.
Timeout 1 Check @then_init.
Timeout 1 Check @then_init.
Timeout 1 Check @d.init.
Timeout 1 Check @d.init.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Set Silent.
Definition init' : proc InitResult :=
  size <- d.size;
  (if lt_dec size 1
   then Ret InitFailed
   else len0 <- addr_to_block 0; _ <- d.write len_addr len0; Ret Initialized).
Unset Silent.
Definition init := then_init d.init init'.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtkWpeF"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmcAxwe"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
Definition get_len : proc addr := b <- d.read len_addr; Ret (block_to_addr b).
Definition get_at (a : addr) : proc block := d.read (log_addr a).
Fixpoint get_upto (a : addr) : proc (list block) :=
  match a with
  | 0 => Ret []
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
Definition recover : proc unit := Ret tt.
Unset Silent.
Definition log_length_ok (d : disk) (log : list block) :=
  exists b, diskGet d 0 =?= b /\ block_to_addr b = length log.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXJUfGc"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqNDEPxh"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition log_abstraction (d : disk) (log : list block) : Prop :=
  log_length_ok d log /\
  (forall a, a < length log -> diskGet d (log_addr a) =?= nth a log block0).
Set Silent.
Definition abstr : Abstraction State :=
  abstraction_compose d.abstr {| abstraction := log_abstraction |}.
Unset Silent.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqw8jR4M"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlIIL2F"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Theorem log_length_ok_nil d b :
  diskGet d 0 = Some b -> block_to_addr b = 0 -> log_length_ok d [].
Proof.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Wf.F_unfold.
Timeout 1 Check @Wf.F_unfold.
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
Timeout 1 Check @Ascii.nat_ascii_embedding.
(unfold log_length_ok; intros).
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Set Printing Width 78.
Show.
(rewrite H; simpl).
Timeout 1 Check @repeat_length.
(eexists; eauto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8SRjHv"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
