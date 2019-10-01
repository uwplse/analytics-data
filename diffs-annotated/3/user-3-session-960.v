Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWfrXOb"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ProofIrrelevance.
From Coq Require Export String.
Print sig.
Fixpoint le_to_nat base (digits : list {x : nat | x < S (S base)}) : nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit * base + le_to_nat base digits'
  end.
(* Failed. *)
