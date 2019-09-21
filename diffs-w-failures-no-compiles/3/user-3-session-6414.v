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
Definition init : proc InitResult :=
  size <- d.size;
  (if lt_dec size 1
   then Ret InitFailed
   else len0 <- addr_to_block 0; _ <- d.write len_addr len0; Ret Initialized).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsUb5xv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqK4sBjD"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
