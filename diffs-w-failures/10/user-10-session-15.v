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
Unset Silent.
Set Printing Width 114.
From Coq Require Import List NArith Streams.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coq23gu0W" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Unset Silent.
Set Printing Width 114.
Import ListNotations.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqOesgEy" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Silent.
Open Scope N_scope.
Unset Silent.
Fixpoint fib (fuel : nat) (a b : N) : list N :=
  match fuel with
  | O => []
  | S fuel => a :: print_id (fib fuel b (a + b))
  end.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqUPskrz" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
CoFixpoint Fib (a b : N) : Stream N := Cons a (print_id (Fib b (a + b))).
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqRuTBbi" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Check @fib.
Check nth.
Print nth.
Timeout 1 Check @fib.
Unset Silent.
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Eval compute in nth 5 (fib 10 0 1) 4.
Eval compute in Str_nth 5 (Fib 0 1).
