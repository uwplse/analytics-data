Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqHmbRVM"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 51.
Set Silent.
Require Import POCS.
Require Import ThreeVariablesAPI.
Unset Silent.
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
Set Printing Width 78.
Module Exercises (vars: VarsAPI).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
step_proc.
(simpl).
step_proc.
(simpl).
step_proc.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqFEFCca"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Theorem incX_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (StateX state + 1) (StateY state) (StateZ state);
     recovered := fun _ state' => False |}) incX vars.recover vars.abstr.
Proof.
(unfold incX).
(repeat step_proc).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqJPf9xF"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Hint Resolve incX_ok: core.
Opaque incX.
Theorem incX_ok_seems_good :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := state = mkState 5 5 5;
     post := fun r state' => state' = mkState 6 5 5;
     recovered := fun _ state' => False |}) incX vars.recover vars.abstr.
Proof.
Set Silent.
Set Silent.
Set Silent.
Unset Silent.
(repeat step_proc).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlGaLOM"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Definition swapXY : proc unit :=
  x <- vars.read VarX;
  y <- vars.read VarY; _ <- vars.write VarX y; _ <- vars.write VarY x; Ret tt.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqEL7D1S"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqohJAHb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem swapXY_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' = mkState (StateY state) (StateX state) (StateZ state);
     recovered := fun _ state' => False |}) swapXY vars.recover vars.abstr.
Set Silent.
Proof.
(repeat step_proc).
Qed.
Hint Resolve swapXY_ok: core.
Unset Silent.
Opaque swapXY.
Theorem swapXY_ok_seems_good :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := state = mkState 2 3 4;
     post := fun r state' => state' = mkState 3 2 4;
     recovered := fun _ state' => False |}) swapXY vars.recover vars.abstr.
Proof.
step_proc.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYuTOmp"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Definition inc1 (v1 : var) : proc unit :=
  v <- vars.read v1; _ <- vars.write v1 (1 + v); Ret tt.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqx7Png1"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSEfhnW"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition inc1X_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' =
             mkState (1 + StateX state) (StateY state) (StateZ state);
     recovered := fun _ state' => True |}) (inc1 VarX) vars.recover
    vars.abstr.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @inc1.
