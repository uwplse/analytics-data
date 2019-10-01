Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWfrXOb"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ProofIrrelevance.
From Coq Require Export String.
#[program]
Fixpoint nat_to_le base (x : nat) {measure x : list {x : nat | x < S base} :=
  match x with
  | 0 => nil
  | _ => exist _ (x mod S base) _ :: nat_to_le (x / S base)
  end.
(* Failed. *)
