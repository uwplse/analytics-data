Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVOSw5L"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
Require Import Helpers.Helpers.
Require Import Proc.
Require Import ProcTheorems.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ret.
