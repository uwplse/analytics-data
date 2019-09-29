Redirect "/tmp/coq16819zKy" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Redirect "/tmp/coq16819Ldx" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import NArith.
Redirect "/tmp/coq168199mA" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Open Scope N_scope.
Definition secret_key := N.
Definition public_key := N.
Definition shared_key := N.
Definition base := 5.
Definition prime := 23.
Definition derive_public (k : secret_key) : public_key := base ^ k mod prime.
Definition calculate_shared (s : secret_key) (p : public_key) : shared_key := p ^ s mod prime.
Definition cipher_text := prod shared_key.
Definition cipher {plain_text} : shared_key -> plain_text -> cipher_text plain_text := pair.
Definition decipher {plain_text} (s : shared_key) (c : cipher_text plain_text) : option plain_text :=
  let (k, t) := c in if s =? k then Some t else None.
Definition random := N.
Redirect "/tmp/coq16819KxG" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
