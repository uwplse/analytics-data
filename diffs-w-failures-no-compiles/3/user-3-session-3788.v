Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtUxvQR"
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
Require Import Lab0.HeapVariablesAPI.
Module HeapExamples (vars: VarsAPI).
Unset Silent.
Definition swapXY : proc unit :=
  x <- vars.read VarX;
  y <- vars.read VarY; _ <- vars.write VarX y; _ <- vars.write VarY x; Ret tt.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqMe8vtG"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqLQslKK"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @In.
Timeout 1 Check @proc.
Timeout 1 Check @CompSpec2Type.
Timeout 1 Check @DeclConstant.GT_APP1.
Timeout 1 Check @DeclConstant.GT_APP1.
Set Printing Width 78.
Inductive ProcMarker {T} (p : proc T) : Type :=
    AProc : _.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0qu6fL"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqoPhort"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @BoolTheory.
Timeout 1 Check @BoolTheory.
Timeout 1 Check @proc.
Timeout 1 Check @AProc.
Timeout 1 Check @AProc.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @AProc.
Timeout 1 Check @AProc.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @AProc.
Timeout 1 Check @AProc.
Timeout 1 Check @AProc.
Set Printing Width 78.
Definition change_marker {T} (p : proc T) (m : ProcMarker p) 
  T' (p' : proc T') : ProcMarker p' := AProc p'.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQ44Ckq"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqJfOnWD"
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
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(match goal with
 | |- proc_spec _ ?p _ _ => pose proof (AProc p) as Hbefore
 end).
(unfold swapXY).
monad_simpl.
Timeout 1 Check @app.
Timeout 1 Check @incl_appl.
Timeout 1 Check @change_marker.
Timeout 1 Check @change_marker.
Timeout 1 Check @change_marker.
Timeout 1 Check @change_marker.
(match goal with
 | |- proc_spec _ ?p _ _ => apply (change_marker p) in Hbefore
 end).
