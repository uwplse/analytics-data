Require Import String.
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
Definition isTheorem (t : Term) := forall env, eval env t = vTrue.
