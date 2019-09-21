Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqVccw9q"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 114.
Set Silent.
From ReductionEffect Require Import PrintingEffect.
Eval compute in (fun f x => f (f (f x))) (fun x => S (print_id x)) 0.
Eval cbn in (fun f x => f (f (f x))) print_id 0.
Eval hnf in (fun f x => f (f (f x))) print_id 0.
Eval simpl in (fun f x => f (f (f x))) (fun x => print_id (1 + x) + 1) 0.
Unset Silent.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqcuNkuE" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Timeout 1 Print LoadPath.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqzKzL6J" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 114.
Set Silent.
From Coq Require Import NArith Streams.
Unset Silent.
Set Printing Width 114.
Open Scope N_scope.
CoFixpoint fib (a b : N) : Stream N := Cons a (print_id (fib b (a + b))).
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqxfDJ5c" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Eval compute in Str_nth 10 (fib 0 1).
