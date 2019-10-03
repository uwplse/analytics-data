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
Open Scope string_scope.
Inductive term :=
  | Nil : term
  | Ident : string -> term
  | Cons : term -> term -> term
  | App : term -> term -> term.
Definition primitive (name : string) : bool :=
  if
   List.find (String.eqb name)
     ("if" :: "fst" :: "snd" :: "fun" :: "arg" :: "nil?" :: "app?" :: "cons?" :: nil)
  then true
  else false.
Redirect "/tmp/coqgkuM3j" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint value (t : term) : bool :=
  match t with
  | Nil => true
  | Ident name => primitive name
  | Cons a b => value a && value b
  | App f a => false
  end.
Redirect "/tmp/coqACDvw1" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Module TermNotations.
Declare Scope coucou_scope.
Notation "{ f a }" := (App f a) (f  at level 0, a  at level 0) : coucou_scope.
Notation "< a b >" := (Cons a b) (format "< a  b >", a  at level 0, b  at level 0) : coucou_scope.
Notation "[ ]" := Nil (format "[ ]") : coucou_scope.
Notation "[ x ]" := (Cons x Nil) : coucou_scope.
Notation "[ x y .. z ]" := (Cons x (Cons y .. (Cons z Nil) ..))
  (x  at level 0, y  at level 0, z  at level 0) : coucou_scope.
Coercion Ident : string >-> term.
End TermNotations.
Import TermNotations.
Open Scope coucou_scope.
Check
  [<Nil <Nil "hi">> (Cons (Ident "1") (Ident "2")) (Ident "a")
  {(Ident "myfun") (Ident "somArg")}].
Redirect "/tmp/coqLRo0nb" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Fixpoint subst (x : string) (u : term) (t : term) : term := t.
Redirect "/tmp/coqVl2ZnQ" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
(* Auto-generated comment: Succeeded. *)

