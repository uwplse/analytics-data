Redirect "/tmp/coqIwNt4T" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Redirect "/tmp/coq8QvH6N" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 98.
Test Debug Analytics.
Require Import Coq.Strings.String.
Redirect "/tmp/coqsRY5JP" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Unset Silent.
Set Printing Width 98.
Unset Silent.
Set Printing Width 98.
Inductive term :=
  | Nil : term
  | Ident : string -> term
  | Cons : term -> term -> term
  | App : term -> term -> term.
Redirect "/tmp/coqn5gNxo" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
