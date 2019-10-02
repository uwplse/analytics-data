Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqME2CHi"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From ExtLib Require Import Functor Monad.
From SimpleIO Require Import IO_Random.
From DeepWeb Require Import Crypto4 IO_Test.
Definition run_tester : io_unit :=
  IO.unsafe_run
    (ORandom.self_init tt;; run_test (multi_test (exec_test test_crypto))).
Separate Extraction run_tester.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqQJpnIk"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
