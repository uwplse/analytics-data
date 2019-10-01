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
Definition primitive (name : string) : bool :=
  if
   List.find (String.eqb name)
     ("if" :: "fst" :: "snd" :: "fun" :: "arg" :: "nil?" :: "app?" :: "cons?" :: nil)
  then true
  else false.
Fixpoint step (t : term) : term :=
  match t with
  | Nil => Nil
  | Ident _ => Nil
  | <a b> => if value a then <a (step b)> else <(step a) b>
  | {f a} =>
      if value f
      then match f with
           | [(Ident lam) (Ident arg) body] => body
           | Ident prim => t
           | _ => Nil
           end
      else {(step f) a}
  end.
Redirect "/tmp/coqYXWD7k" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Print step.
