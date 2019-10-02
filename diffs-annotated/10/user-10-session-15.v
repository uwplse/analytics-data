Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqVccw9q"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From ReductionEffect Require Import PrintingEffect.
Eval compute in (fun f x => f (f (f x))) (fun x => S (print_id x)) 0.
Eval cbn in (fun f x => f (f (f x))) print_id 0.
Eval hnf in (fun f x => f (f (f x))) print_id 0.
Eval simpl in (fun f x => f (f (f x))) (fun x => print_id (1 + x) + 1) 0.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqcuNkuE" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Timeout 1 Print LoadPath.
Timeout 1 Print Grammar tactic.
From Coq Require Import List NArith Streams.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqsaA1a1" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Import ListNotations.
Fixpoint fib (fuel : nat) (a b : N) : list N := match fuel with
                                                | O => []
                                                | S fuel => a :: fib fuel b (a + b)
                                                end.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqKkOyz5" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Eval compute in fib 10 0 1.
