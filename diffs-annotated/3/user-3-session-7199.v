Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIz2qfk"
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
     proc_spec (@addr_to_block_spec State a) (addr_to_block a) recover abstr).
Hint Resolve addr_to_block_ok: core.
(simpl; auto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqqkicQk"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
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
(induction bs'; simpl).
-
step_proc.
intuition eauto.
(rewrite app_nil_r; auto).
-
step_proc.
(intuition eauto; autorewrite with upd; auto).
(apply log_contents_ok_unchanged).
