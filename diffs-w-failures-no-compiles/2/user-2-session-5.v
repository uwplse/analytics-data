Redirect "/tmp/coqaLDgJ2" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Redirect "/tmp/coqC69LM6" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 98.
Test Debug Analytics.
Require Import Coq.Strings.String.
Redirect "/tmp/coq4iI7Dj" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Inductive term :=
  | Nil : term
  | Ident : string -> term
  | Cons : term -> term -> term
  | App : term -> term -> term.
Redirect "/tmp/coqmW6Ht8" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Check @term.
Timeout 1 Check @term.
Timeout 1 Check @value.
Timeout 1 Check @value.
Timeout 1 Check @value.
Timeout 1 Check @value.
Unset Silent.
Set Printing Width 98.
Unset Silent.
Set Printing Width 98.
Unset Silent.
Timeout 1 Check @value.
Timeout 1 Check @value.
Timeout 1 Check @value.
Timeout 1 Check @value.
Print List.find.
Print List.find.
Set Printing Width 98.
Definition primitive (name : string) : bool :=
  List.find (String.eq name)
    ("if" :: "fst" :: "snd" :: "fun" :: "arg" :: "nil?" :: "app?" :: "cons?" :: nil).
