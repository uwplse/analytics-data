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
Unset Silent.
Set Diffs "off".
Set Printing Width 68.
Unset Silent.
Set Diffs "off".
Set Printing Width 68.
Set Silent.
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
Unset Silent.
Definition get_len : proc addr :=
  b <- d.read len_addr; Ret (block_to_addr b).
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKp7l6v"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVnvw58"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition get_at (a : addr) : proc block := d.read (log_addr a).
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqHtNpYl"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBlEp9H"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
