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
Inductive term :=
  | Nil : term
  | Ident : string -> term
  | Cons : term -> term -> term
  | App : term -> term -> term.
Unset Silent.
Unset Silent.
Set Printing Width 98.
Definition oneArgCbvPrimitive (name : string) : bool :=
  if
   List.find (String.eqb name)
     ("fst" :: "snd" :: "fun" :: "arg" :: "nil?" :: "app?" :: "cons?" :: nil)
  then true
  else false.
Redirect "/tmp/coqnPJ1L1" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Check @oneArgCbvPrimitive.
Definition primitive (name : string) : bool := String.eqb name "if" || oneArgCbvPrimitive name.
Redirect "/tmp/coqNtQ3Ng" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint value (t : term) : bool :=
  match t with
  | Nil => true
  | Ident name => primitive name
  | Cons a b => value a && value b
  | App f a => false
  end.
Redirect "/tmp/coq5lRvou" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Module TermNotations.
Declare Scope coucou_scope.
Set Silent.
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
Fixpoint subst (x : string) (u : term) (t : term) : term := t.
Unset Silent.
Redirect "/tmp/coqAO7f1D" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Check @oneArgCbvPrimitive.
Timeout 1 Check @oneArgCbvPrimitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @value.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Timeout 1 Check @primitive.
Fixpoint step (t : term) : term :=
  match t with
  | Nil => Nil
  | Ident _ => Nil
  | <a b> => if value a then <a (step b)> else <(step a) b>
  | {f a} =>
      if value f
      then
       match f with
       | [(Ident lam) (Ident x) body] => if value a then subst x a body else {f (step a)}
       | Ident prim =>
           if String.eqb prim "if"
           then
            match a with
            | [cond bThen bElse] =>
                if value cond
                then match cond with
                     | Nil => bElse
                     | _ => bThen
                     end
                else {"if" [(step cond) bThen bElse]}
            | _ => Nil
            end
           else
            if oneArgCbvPrimitive prim
            then
             if value a
             then
              if String.eqb prim "fst"
              then match a with
                   | <x y> => x
                   | _ => Nil
                   end
              else
               if String.eqb prim "snd"
               then match a with
                    | <x y> => y
                    | _ => Nil
                    end
               else
                if String.eqb prim "fun"
                then match a with
                     | {f a} => f
                     | _ => Nil
                     end
                else
                 if String.eqb prim "arg"
                 then match a with
                      | {f a} => a
                      | _ => Nil
                      end
                 else
                  if String.eqb prim "nil?"
                  then match a with
                       | Nil => "t"
                       | _ => Nil
                       end
                  else
                   if String.eqb prim "cons?"
                   then match a with
                        | <_ _> => "t"
                        | _ => Nil
                        end
                   else
                    if String.eqb prim "app?"
                    then match a with
                         | {_ _} => "t"
                         | _ => Nil
                         end
                    else Nil
             else {f (step a)}
            else Nil
       | _ => Nil
       end
      else {(step f) a}
  end.
Redirect "/tmp/coqfAE0Rj" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Unset Silent.
Timeout 1 Check @term.
Timeout 1 Check @term.
Timeout 1 Check @step.
Set Printing Width 98.
Fixpoint multistep (n : nat) : term -> term :=
  match n with
  | O => id
  | S m => fun t => multistep m (step t)
  end.
Redirect "/tmp/coq1McSmJ" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Check @term.
Unset Silent.
Timeout 1 Check @term.
Timeout 1 Check @term.
Timeout 1 Check @step.
Set Printing Width 98.
Fixpoint trace (n : nat) : term -> list term :=
  match n with
  | O => nil
  | S m => fun t => cons t (trace m (step t))
  end.
