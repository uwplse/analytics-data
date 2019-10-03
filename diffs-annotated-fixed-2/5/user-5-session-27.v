Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.
Definition Identifier := string.
Definition id_eq_dec := string_dec.
Inductive Term : Set :=
  | Var : Identifier -> Term
  | Bool : bool -> Term
  | Eq : Term -> Term -> Term
  | And : Term -> Term -> Term
  | Or : Term -> Term -> Term
  | Not : Term -> Term
  | If : Term -> Term -> Term -> Term
  | Int : Z -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Bools : Term
  | Ints : Term
  | In : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.
Definition extendEnv {Value} (env : Identifier -> Value) 
  (var : Identifier) (newValue : Value) : Identifier -> Value :=
  fun id => if id_eq_dec id var then newValue else env id.
(* Auto-generated comment: Succeeded. *)

