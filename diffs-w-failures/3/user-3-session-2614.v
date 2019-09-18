Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTHDFnk"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
From Coq Require Import FunInd Recdef.
From Coq Require Import PeanoNat.
From Coq Require Import Arith.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @SReqe_Reqe.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @MRet.
