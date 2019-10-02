Redirect "/tmp/coqaLDgJ2" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Redirect "/tmp/coqC69LM6" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
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
Fixpoint value (t : term) : bool :=
  match t with
  | Nil => true
  | Ident _ => true
  | Cons a b => value a && value b
  | App f a => false
  end.
Redirect "/tmp/coqhYSoRC" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Module TermNotations.
Declare Scope coucou_scope.
Notation "{ f a }" := (App f a) (f  at level 0, a  at level 0) : coucou_scope.
Notation "[ ]" := Nil (format "[ ]") : coucou_scope.
Notation "[ x ]" := (Cons x Nil) : coucou_scope.
Notation "[ x y .. z ]" := (Cons x (Cons y .. (Cons z Nil) ..))
  (x  at level 0, y  at level 0, z  at level 0) : coucou_scope.
End TermNotations.
Import TermNotations.
Open Scope coucou_scope.
Check [Nil (Ident "a") {(Ident "myfun") (Ident "somArg")}].
(* Auto-generated comment: Succeeded. *)

