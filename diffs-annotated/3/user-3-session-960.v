Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWfrXOb"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ProofIrrelevance.
From Coq Require Export String.
Check mod_S_lt.
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  match Byte.of_nat (proj1_sig x) with
  | Some b => Ascii.ascii_of_byte b
  | None => ascii0
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhtsIcj"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTyMpHa"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Check Ascii.byte_of_ascii.
Check Ascii.nat_of_ascii.
Definition ascii_to_bounded (a : Ascii.ascii) : {x | x < 256} :=
  Instance aModel : GoModel.
(* Failed. *)
