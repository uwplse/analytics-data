Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqBYq1cI"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Timeout 1 Print LoadPath.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coq5lrxpQ" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Unset Silent.
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Set Silent.
From Coq Require Import NArith List Streams.
From ReductionEffect Require Import PrintingEffect.
CoFixpoint fib (x y : N) : Stream N := Cons y (fib y (x + y)).
Unset Silent.
Eval compute in Str_nth 10 (map print_id (fib 0 1)).
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqcRXKe3" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Timeout 1 Check @fib.
Import ListNotations.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqinpWed" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Timeout 1 Check @fib.
Unset Silent.
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqk3FY68" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Eval compute in List.map print_id (fib' 10 0 1).
Eval compute in (fun f x => f (f (f x))) (fun x => S (print_id x)) 0.
Eval cbn in (fun f x => f (f (f x))) print_id 0.
Eval hnf in (fun f x => f (f (f x))) print_id 0.
Eval simpl in (fun f x => f (f (f x))) (fun x => print_id (1 + x) + 1) 0.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
