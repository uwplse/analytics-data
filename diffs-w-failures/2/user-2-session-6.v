Redirect "/tmp/coq5MWvur" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Redirect "/tmp/coqan5ySU" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 98.
Test Debug Analytics.
Require Import Coq.Strings.String.
Redirect "/tmp/coqnSrykz" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Open Scope string_scope.
Inductive term :=
  | Nil : term
  | Ident : string -> term
  | Symb : string -> term
  | Cons : term -> term -> term
  | App : term -> term -> term.
Redirect "/tmp/coqafXLuq" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
