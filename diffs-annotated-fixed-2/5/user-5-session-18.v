Require Import String.
Definition Identifier := string.
Definition id_eq_dec := string_dec.
Inductive Term : Set :=
  | Var : Identifier -> Term
  | Eq : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.
Module Type EpsilonLogic.
Parameter (Value : Type).
Parameter (vTrue : Value).
Parameter (vFalse : Value).
Axiom (trueAndFalseDistinct : vTrue <> vFalse).
Definition Environment := Identifier -> Value.
Parameter (eval : Environment -> Term -> Value).
Axiom (evalEqTrue : forall env term, eval env (Eq term term) = vTrue).
Axiom
  (evalEqFalse : forall env t1 t2, t1 <> t2 -> eval env (Eq t1 t2) = vFalse).
Axiom (evalVar : forall env id, eval env (Var id) = env id).
(* Auto-generated comment: Succeeded. *)

