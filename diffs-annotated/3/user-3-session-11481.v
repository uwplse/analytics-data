Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqHmbRVM"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import POCS.
Require Import ThreeVariablesAPI.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqzFGxqr"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhJIZ3A"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Module Exercises (vars: VarsAPI).
Check vars.read.
Check vars.write.
Definition incX : proc unit :=
  x <- vars.read VarX; _ <- vars.write VarX (x + 1); Ret tt.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqammdPf"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqRwctHg"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem incX_test :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := state = mkState 1 2 3;
     post := fun r state' => state' = mkState 2 2 3;
     recovered := fun _ state' => False |}) incX vars.recover vars.abstr.
Proof.
(unfold incX).
step_proc.
