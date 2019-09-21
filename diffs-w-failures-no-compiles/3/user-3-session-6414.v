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
Definition init : proc InitResult :=
  len0 <- addr_to_block 0; _ <- d.write len_addr len0; Ret Initialized.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbVHk3U"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqGWjpqP"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @ge.
Timeout 1 Check @get_spec.
Timeout 1 Check @get_spec.
Timeout 1 Check @get_spec.
Timeout 1 Check @proc.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @ge.
Timeout 1 Check @get_spec.
Timeout 1 Check @get_spec.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @len_addr.
Timeout 1 Check @Ret.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Timeout 1 Check @block_to_addr.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Definition get_len : proc addr := b <- d.read len_addr; Ret (block_to_addr b).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqoiO4w3"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCbe4Od"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Definition get_at (a : addr) : proc block := d.read (log_addr a).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqaylAHt"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSCzANV"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @Fix.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @Fix.
Timeout 1 Check @no_wipe.
Timeout 1 Check @split.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @d.read.
Timeout 1 Check @bnull.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @bnull.
Timeout 1 Check @bnull.
Timeout 1 Check @Ret.
Timeout 1 Check @bnull.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @get_at.
Timeout 1 Check @bnull.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @get_at.
Timeout 1 Check @Ret.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @repeat_length.
Fixpoint get_upto (a : addr) : proc (list block) :=
  match a with
  | 0 => Ret []
  | S a => b <- get_at a; bs <- get_upto a; Ret (bs ++ [b])
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQAqVu1"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmIHFZM"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @repeat_length.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @get_len.
Timeout 1 Check @get_len.
Timeout 1 Check @ge.
Timeout 1 Check @get_upto.
Timeout 1 Check @get_upto.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Definition get : proc (list block) := len <- get_len; get_upto len.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8aT6YT"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2gZaVH"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @max_l.
Timeout 1 Check @max_l.
Timeout 1 Check @max_l.
Timeout 1 Check @sig.
Timeout 1 Check @d.size.
Timeout 1 Check @d.size.
Timeout 1 Check @repeat_length.
Timeout 1 Check @ge.
Timeout 1 Check @get_at.
Timeout 1 Check @get_len.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @sig.
Timeout 1 Check @d.size.
Timeout 1 Check @repeat_length.
Timeout 1 Check @lel.
Timeout 1 Check @Ret.
Timeout 1 Check @false.
Timeout 1 Check @false.
Timeout 1 Check @false.
Timeout 1 Check @app.
Timeout 1 Check @bappend.
Timeout 1 Check @bappend.
Timeout 1 Check @append_spec.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @addr.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @split.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @block.
Timeout 1 Check @proc.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @no_wipe.
Timeout 1 Check @nil.
Timeout 1 Check @nil.
Timeout 1 Check @nil.
Timeout 1 Check @Ret.
Timeout 1 Check @tt.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @d.write.
Timeout 1 Check @d.write.
Timeout 1 Check @d.write.
Timeout 1 Check @d.write.
Timeout 1 Check @block.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @log_addr.
Timeout 1 Check @d.write.
Timeout 1 Check @d.write.
Timeout 1 Check @d.write.
Timeout 1 Check @d.write.
Timeout 1 Check @app.
Timeout 1 Check @bappend.
Timeout 1 Check @bappend.
Timeout 1 Check @bappend.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @repeat_length.
Timeout 1 Check @Fix.
Timeout 1 Check @Fix.
Fixpoint append_at (a : addr) (bs : list block) : 
proc unit :=
  match bs with
  | [] => Ret tt
  | b :: bs => _ <- d.write (log_addr a) b; append_at (S a) bs
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOIPjdR"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmw0vc8"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @app.
Timeout 1 Check @app.
Timeout 1 Check @append_at.
Timeout 1 Check @append_at.
Timeout 1 Check @repeat_length.
Timeout 1 Check @repeat_length.
Timeout 1 Check @spec_abstraction_compose.
Definition append (bs : list block) : proc bool :=
  size <- d.size;
  len <- get_len;
  (if le_dec (1 + len + length bs) size then append_at len bs else Ret false).
