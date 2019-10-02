Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.
Definition Identifier := string.
Fixpoint identity (t : Term) : Term :=
  match t with
  | Var x => Var x
  | Bool b => Bool b
  | Bools => Bools
  | Ints => Ints
  | In a b => In (identity a) (identity b)
  | Eq a b => Eq (identity a) (identity b)
  | And a b => And (identity a) (identity b)
  | Or a b => Or (identity a) (identity b)
  | Not a => Not (identity a)
  | If a b c => If (identity a) (identity b) (identity c)
  | Int i => Int i
  | Plus a b => Plus (identity a) (identity b)
  | Times a b => Times (identity a) (identity b)
  | Minus a b => Minus (identity a) (identity b)
  | Choose x P => Choose x (identity P)
  end.
Theorem eval_eq_true_or_false :
  forall (L : EpsilonLogic) env (t1 t2 : Term),
  L.(eval) env (Eq t1 t2) = L.(eval) env (Bool true) \/
  L.(eval) env (Eq t1 t2) = L.(eval) env (Bool false).
Proof.
