Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqK4fPkT"
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
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
From Coq Require Import NArith Streams.
Open Scope N_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Unset Silent.
Eval compute in Str_nth 10 (fib1 0 1).
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqAWfqgM" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Timeout 1 Check @fib1.
Timeout 1 Check @fib1.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqkErrKN" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Eval compute in hd (fib2 0 1).
Backtrack 26 0 0.
Unset Silent.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqTOxbsM" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Eval compute in hd (fib2 0 1).
Backtrack 35 0 0.
Unset Silent.
Eval compute in Str_nth 10 (fib2 0 1).
Backtrack 38 0 0.
Unset Silent.
Backtrack 32 0 0.
Unset Silent.
Print hd.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqKJ6qsn" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Fail Timeout 1 Eval compute in hd (fib2 0 1).
Unset Silent.
Backtrack 47 0 0.
