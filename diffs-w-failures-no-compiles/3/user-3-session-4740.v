Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqUJOOPh"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq98GU8h"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8DKAxw"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 69.
Timeout 1 Check @le.
Timeout 1 Check @Byte.x30.
Unset Silent.
Set Diffs "off".
Set Printing Width 69.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Byte.x50.
Timeout 1 Check @Byte.x10.
Set Printing Width 69.
Unset Silent.
Set Diffs "off".
Set Printing Width 69.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Byte.x10.
Set Printing Width 69.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @forall_exists_coincide_unique_domain.
Set Printing Width 69.
Unset Silent.
Set Diffs "off".
Set Printing Width 69.
Notation "a === b" := (a = b) (at level 100, format "a '/' ===  b").
Definition aReallyBigIdentifier := 3.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqLIXWpS"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrNt0PZ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition anotherLongName := 10.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIn9zkk"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqFdQVWS"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Check 1 + 2 + aReallyBigIdentifier + 4 + anotherLongName
  === 6 + anotherLongName + 8 + 9.
