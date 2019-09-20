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
Unset Silent.
Set Printing Width 98.
Set Silent.
Open Scope string_scope.
Unset Silent.
Set Printing Width 98.
Inductive term :=
  | Nil : term
  | Ident : string -> term
  | Symb : string -> term
  | Cons : term -> term -> term
  | App : term -> term -> term.
Redirect "/tmp/coq84xhGL" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition oneArgCbvPrimitive (name : string) : bool :=
  if
   List.find (String.eqb name)
     ("fst" :: "snd" :: "fun" :: "arg" :: "nil?" :: "app?" :: "cons?" :: nil)
  then true
  else false.
Redirect "/tmp/coqi2dfar" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
