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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Definition change_marker {T'} (p' : proc T') `(@ProcMarker T p) :
  ProcMarker p' := AProc p'.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqFdVrYR"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtKERBA"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @NotConstant.
Timeout 1 Check @AProc.
Timeout 1 Check @AProc.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @ProcMarker.
Timeout 1 Check @Znumtheory.prime.
Timeout 1 Check @spec_abstraction_compose.
Set Printing Width 78.
Notation "'proc:' p" := (ProcMarker p) (only printing).
