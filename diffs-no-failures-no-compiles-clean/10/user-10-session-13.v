Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqBYq1cI"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Timeout 1 Print LoadPath.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coq5lrxpQ" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
From Coq Require Import NArith Streams.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqznWAeW" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
From ReductionEffect Require Import PrintingEffect.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqTlmINW" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Check map.
CoFixpoint fib (x y : N) : Stream N := Cons y (fib y (x + y)).
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqbF6gTS" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Eval compute in Str_nth 10 (map print_id (fib 0 1)).
