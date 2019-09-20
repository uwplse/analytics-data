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
Theorem swapXY_ok :
  proc_spec
    (fun (_ : unit) state =>
     {|
     pre := True;
     post := fun r state' =>
             state' = mkState (StateY state) (StateX state) (StateZ state);
     recovered := fun _ state' => True |}) swapXY vars.recover vars.abstr.
Proof.
(unfold swapXY).
Timeout 1 Check @Nat.mod_1_r.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
monad_simpl.
Timeout 1 Check @repeat_length.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @missing.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @proc.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec.
Timeout 1 Check @proc_spec_rx.
Timeout 1 Check @proc_spec_rx.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(eapply proc_spec_rx; [ solve [ eauto ] |  ]).
Check proc_spec_rx.
Timeout 1 Check @spec_abstraction_compose.
Timeout 1 Check @repeat_length.
Timeout 1 Check @eq_rec.
Timeout 1 Check @recovered.
Timeout 1 Check @recovered.
(cbn[pre post recovered]).
Timeout 1 Check @Ascii.nat_ascii_embedding.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @repeat_length.
Timeout 1 Check @NotConstant.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Set Printing Width 78.
Show.
(let state := fresh "state" in
 intros ? state Hpre).
