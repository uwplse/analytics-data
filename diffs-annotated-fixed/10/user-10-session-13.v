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
From Coq Require Import NArith List Streams.
From ReductionEffect Require Import PrintingEffect.
CoFixpoint fib (x y : N) : Stream N := Cons y (fib y (x + y)).
Eval compute in Str_nth 10 (map print_id (fib 0 1)).
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqcRXKe3" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Import ListNotations.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqinpWed" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Fixpoint fib' (fuel : nat) (x y : N) : list N :=
  match fuel with
  | O => []
  | S fuel => y :: fib' fuel (print_id y) (x + y)
  end.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coq9VBKIy" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Eval compute in List.map print_id (fib' 10 0 1).
(* Auto-generated comment: Succeeded. *)

