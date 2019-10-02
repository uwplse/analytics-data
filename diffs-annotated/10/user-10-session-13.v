Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqBYq1cI"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Timeout 1 Print LoadPath.
From Coq Require Import NArith Streams.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqznWAeW" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
CoFixpoint fib (x y : N) : Stream N := Cons y (fib y (x + y)).
Eval compute in Str_nth 10 (map print_id (fib 0 1)).
