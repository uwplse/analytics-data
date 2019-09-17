Redirect "/tmp/coq16819zKy" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Redirect "/tmp/coq16819Ldx" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 115.
Set Silent.
From Coq Require Import NArith.
Definition secret_key := N.
Definition public_key := N.
Definition shared_key := N.
Definition base := 5.
Definition prime := 23.
Unset Silent.
