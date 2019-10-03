Require Import String.
Require Import ZArith.
Definition Identifier := string.
Definition id_eq_dec := string_dec.
Inductive Term : Set :=
  | Var : Identifier -> Term
  | Int : Z -> Term
  | Eq : Term -> Term -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.
Definition extendEnv {Value} (env : Identifier -> Value) 
  (var : Identifier) (newValue : Value) : Identifier -> Value :=
  fun id => if id_eq_dec id var then newValue else env id.
(* Auto-generated comment: Succeeded. *)

