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
Set Silent.
Module Log (d: OneDiskAPI)<: LogAPI.
Definition init : proc InitResult.
Admitted.
Definition get : proc (list block).
Admitted.
Definition append : list block -> proc bool.
Admitted.
Definition reset : proc unit.
Admitted.
Definition recover : proc unit.
Admitted.
Definition abstr : Abstraction State := {| abstraction := fun _ _ => True |}.
Theorem init_ok : init_abstraction init recover abstr inited_any.
Proof.
Admitted.
Theorem get_ok : proc_spec get_spec get recover abstr.
Proof.
Admitted.
Theorem append_ok :
  forall v, proc_spec (append_spec v) (append v) recover abstr.
Proof.
Admitted.
Theorem reset_ok : proc_spec reset_spec reset recover abstr.
Proof.
Admitted.
Theorem recover_wipe : rec_wipe recover abstr no_wipe.
Proof.
Admitted.
Unset Silent.
End Log.
