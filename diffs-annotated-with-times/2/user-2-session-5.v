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
  | Symb : string -> term
  | Cons : term -> term -> term
  | App : term -> term -> term.
Redirect "/tmp/coqfgPYy0" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition oneArgCbvPrimitive (name : string) : bool :=
  if
   List.find (String.eqb name)
     ("fst" :: "snd" :: "fun" :: "arg" :: "nil?" :: "app?" :: "cons?" :: nil)
  then true
  else false.
Redirect "/tmp/coqdPkGO7" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition primitive (name : string) : bool := String.eqb name "if" || oneArgCbvPrimitive name.
Redirect "/tmp/coq948p4z" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint value (t : term) : bool :=
  match t with
  | Nil => true
  | Ident name => primitive name
  | Symb _ => true
  | Cons a b => value a && value b
  | App f a => false
  end.
Redirect "/tmp/coqxazZMH" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Module TermNotations.
Declare Scope coucou_scope.
Notation "{ f a }" := (App f a) (f  at level 0, a  at level 0) : coucou_scope.
Notation "< a b >" := (Cons a b) (format "< a  b >", a  at level 0, b  at level 0) : coucou_scope.
Notation "[ ]" := Nil (format "[ ]") : coucou_scope.
Notation "[ x ]" := (Cons x Nil) : coucou_scope.
Notation "[ x y .. z ]" := (Cons x (Cons y .. (Cons z Nil) ..))
  (x  at level 0, y  at level 0, z  at level 0) : coucou_scope.
Notation "# s" := (Symb s) (format "# s", at level 0, s  at level 0) : coucou_scope.
Coercion Ident : string >-> term.
End TermNotations.
Import TermNotations.
Open Scope coucou_scope.
Check
  [<#"hello" <Nil #"hi">> (Cons (Ident "1") (Ident "2")) (Ident "a")
  {(Ident "myfun") (Ident "somArg")}].
Redirect "/tmp/coqJVP0xh" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Fixpoint subst (x : string) (u : term) (t : term) : term := t.
Redirect "/tmp/coqiXoFBS" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint step (t : term) : term :=
  match t with
  | Nil => Nil
  | Ident _ => Nil
  | Symb _ => t
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
                       | Nil => #"t"
                       | _ => Nil
                       end
                  else
                   if String.eqb prim "cons?"
                   then match a with
                        | <_ _> => #"t"
                        | _ => Nil
                        end
                   else
                    if String.eqb prim "app?"
                    then match a with
                         | {_ _} => #"t"
                         | _ => Nil
                         end
                    else Nil
             else {f (step a)}
            else Nil
       | _ => Nil
       end
      else {(step f) a}
  end.
Redirect "/tmp/coqsKmbBv" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint multistep (n : nat) : term -> term :=
  match n with
  | O => id
  | S m => fun t => multistep m (step t)
  end.
Redirect "/tmp/coqZBHmvA" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint trace (n : nat) : term -> list term :=
  match n with
  | O => fun _ => nil
  | S m => fun t => cons t (trace m (step t))
  end.
Redirect "/tmp/coqMDtlae" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-17 16:10:41.400000.*)

